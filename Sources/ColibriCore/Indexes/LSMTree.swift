//
//  LSMTree.swift
//  ColibrìDB LSM-Tree Index Implementation
//
//  Based on: spec/LSMTree.tla
//  Implements: Log-Structured Merge Tree (write-optimized)
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//
//  Based on: "The Log-Structured Merge-Tree" (O'Neil et al., 1996)
//

import Foundation

// Use the Value type from Core/Types.swift
typealias Value = ColibriCore.Value

/// LSM-Tree Level
private class LSMLevel {
    var sstables: [SSTable] = []
    let level: Int
    let maxSize: Int
    
    init(level: Int, maxSize: Int) {
        self.level = level
        self.maxSize = maxSize
    }
    
    var size: Int {
        return sstables.reduce(0) { $0 + $1.size }
    }
    
    var needsCompaction: Bool {
        return size > maxSize
    }
}

/// Sorted String Table (SSTable)
private struct SSTable {
    let id: UUID
    let data: [(Value, [RID])]
    let minKey: Value
    let maxKey: Value
    
    var size: Int {
        return data.count
    }
    
    func search(key: Value) -> [RID]? {
        // Binary search in sorted data
        var low = 0
        var high = data.count - 1
        
        while low <= high {
            let mid = (low + high) / 2
            let (midKey, rids) = data[mid]
            
            if midKey == key {
                return rids
            } else if midKey < key {
                low = mid + 1
            } else {
                high = mid - 1
            }
        }
        
        return nil
    }
}

/// LSM-Tree Index (write-optimized)
/// Corresponds to TLA+ module: LSMTree.tla
public actor LSMTree {
    // MARK: - Configuration
    
    /// MemTable size threshold (bytes)
    private static let memTableThreshold = 1024 * 1024  // 1MB
    
    /// Base level size
    private static let baseLevelSize = 10 * 1024 * 1024  // 10MB
    
    /// Level size multiplier
    private static let levelSizeMultiplier = 10
    
    // MARK: - State Variables
    
    /// Active memtable (in-memory sorted tree)
    private var memTable: [(Value, [RID])] = []
    
    /// Immutable memtable (being flushed)
    private var immutableMemTable: [(Value, [RID])]?
    
    /// LSM levels (L0, L1, L2, ...)
    private var levels: [LSMLevel] = []
    
    /// MemTable size (bytes)
    private var memTableSize: Int = 0
    
    // MARK: - Initialization
    
    public init() {
        // Initialize levels
        for level in 0..<7 {  // 7 levels typical
            let maxSize = Self.baseLevelSize * Int(pow(Double(Self.levelSizeMultiplier), Double(level)))
            levels.append(LSMLevel(level: level, maxSize: maxSize))
        }
    }
    
    // MARK: - Core Operations
    
    /// Insert key-RID pair
    /// TLA+ Action: Insert(key, rid)
    public func insert(key: Value, rid: RID) async throws {
        // Insert into memtable
        if let index = memTable.firstIndex(where: { $0.0 == key }) {
            // Key exists, append RID
            memTable[index].1.append(rid)
        } else {
            // New key, insert in sorted order
            memTable.append((key, [rid]))
            memTable.sort { $0.0 < $1.0 }
        }
        
        memTableSize += MemoryLayout<Value>.size + MemoryLayout<RID>.size
        
        // Check if memtable needs flush
        if memTableSize > Self.memTableThreshold {
            try await flushMemTable()
        }
    }
    
    /// Search for key
    /// TLA+ Action: Search(key)
    public func search(key: Value) async -> [RID]? {
        // Search in memtable first
        if let index = memTable.firstIndex(where: { $0.0 == key }) {
            return memTable[index].1
        }
        
        // Search in immutable memtable
        if let immutable = immutableMemTable,
           let index = immutable.firstIndex(where: { $0.0 == key }) {
            return immutable[index].1
        }
        
        // Search in levels (newest to oldest)
        for level in levels {
            for sstable in level.sstables.reversed() {
                // Check if key is in range
                if key >= sstable.minKey && key <= sstable.maxKey {
                    if let rids = sstable.search(key: key) {
                        return rids
                    }
                }
            }
        }
        
        return nil
    }
    
    /// Range scan
    public func rangeScan(minKey: Value, maxKey: Value) async -> [(Value, [RID])] {
        var results: [(Value, [RID])] = []
        
        // Collect from memtable
        for (key, rids) in memTable {
            if key >= minKey && key <= maxKey {
                results.append((key, rids))
            }
        }
        
        // Collect from levels and merge
        for level in levels {
            for sstable in level.sstables {
                if sstable.maxKey >= minKey && sstable.minKey <= maxKey {
                    for (key, rids) in sstable.data {
                        if key >= minKey && key <= maxKey {
                            results.append((key, rids))
                        }
                    }
                }
            }
        }
        
        // Merge and deduplicate
        var merged: [Value: [RID]] = [:]
        for (key, rids) in results {
            merged[key, default: []].append(contentsOf: rids)
        }
        
        return merged.sorted { $0.key < $1.key }.map { ($0.key, $0.value) }
    }
    
    // MARK: - Background Operations
    
    /// Flush memtable to L0
    /// TLA+ Action: FlushMemTable
    private func flushMemTable() async throws {
        guard !memTable.isEmpty else { return }
        
        // Move memtable to immutable
        immutableMemTable = memTable
        memTable = []
        memTableSize = 0
        
        // Create SSTable from immutable memtable
        guard let data = immutableMemTable else { return }
        
        let sstable = SSTable(
            id: UUID(),
            data: data,
            minKey: data.first!.0,
            maxKey: data.last!.0
        )
        
        // Add to L0
        levels[0].sstables.append(sstable)
        
        // Clear immutable memtable
        immutableMemTable = nil
        
        // Check if compaction needed
        await compactIfNeeded()
    }
    
    /// Compact levels if needed
    /// TLA+ Action: Compact
    private func compactIfNeeded() async {
        for i in 0..<(levels.count - 1) {
            let currentLevel = levels[i]
            
            if currentLevel.needsCompaction {
                await compact(fromLevel: i, toLevel: i + 1)
            }
        }
    }
    
    /// Compact from one level to next
    private func compact(fromLevel: Int, toLevel: Int) async {
        let sourceLevel = levels[fromLevel]
        let targetLevel = levels[toLevel]
        
        // Select SSTables to compact (simplified: all SSTables)
        let sourceTables = sourceLevel.sstables
        
        guard !sourceTables.isEmpty else { return }
        
        // Merge all data
        var allData: [Value: [RID]] = [:]
        
        for sstable in sourceTables {
            for (key, rids) in sstable.data {
                allData[key, default: []].append(contentsOf: rids)
            }
        }
        
        // Add target level data
        for sstable in targetLevel.sstables {
            for (key, rids) in sstable.data {
                allData[key, default: []].append(contentsOf: rids)
            }
        }
        
        // Sort and create new SSTable
        let sortedData = allData.sorted { $0.key < $1.key }.map { ($0.key, $0.value) }
        
        guard !sortedData.isEmpty else { return }
        
        let compactedTable = SSTable(
            id: UUID(),
            data: sortedData,
            minKey: sortedData.first!.0,
            maxKey: sortedData.last!.0
        )
        
        // Replace target level
        targetLevel.sstables = [compactedTable]
        
        // Clear source level
        sourceLevel.sstables.removeAll()
    }
    
    // MARK: - Query Operations
    
    /// Get LSM-Tree statistics
    public func getStatistics() -> LSMTreeStatistics {
        return LSMTreeStatistics(
            memTableSize: memTableSize,
            memTableEntries: memTable.count,
            immutableMemTableSize: immutableMemTable?.count ?? 0,
            levels: levels.map { level in
                LevelStatistics(
                    level: level.level,
                    sstableCount: level.sstables.count,
                    totalSize: level.size,
                    maxSize: level.maxSize
                )
            }
        )
    }
    
    /// Force flush memtable
    public func flush() async throws {
        try await flushMemTable()
    }
    
    /// Force compaction
    public func compact() async {
        await compactIfNeeded()
    }
}

// MARK: - Supporting Types

/// LSM-Tree statistics
public struct LSMTreeStatistics: Sendable {
    public let memTableSize: Int
    public let memTableEntries: Int
    public let immutableMemTableSize: Int
    public let levels: [LevelStatistics]
}

/// Level statistics
public struct LevelStatistics: Sendable {
    public let level: Int
    public let sstableCount: Int
    public let totalSize: Int
    public let maxSize: Int
    
    public var loadFactor: Double {
        return maxSize > 0 ? Double(totalSize) / Double(maxSize) : 0.0
    }
}

