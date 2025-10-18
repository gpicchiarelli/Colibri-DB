//
//  FractalTreeIndex.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrDB — BSD 3-Clause License

// Theme: Advanced Fractal Tree Index with message buffering, hierarchical merges,
//        bulk operations, compression, partitioning, and optimization algorithms.

import Foundation
import Compression

/// Advanced Fractal Tree Index implementing:
/// - Multi-level message buffering system
/// - Hierarchical merge operations with lazy propagation
/// - Bulk operations for batch insert/delete/update
/// - Key compression for memory efficiency
/// - Partitioning for scalability
/// - Intelligent optimization algorithms
public final class FractalTreeIndex<Element: Hashable & Comparable, Reference: Hashable>: IndexProtocol {
    public typealias Key = Element
    public typealias Ref = Reference

    // MARK: - Message System
    
    /// Represents a pending operation in the fractal tree
    private enum Message: Hashable {
        case insert(Ref)
        case delete(Ref)
        case bulkInsert([Ref])
        case bulkDelete([Ref])
        
        func apply(to entry: inout TombstoneSet<Ref>) {
            switch self {
            case .insert(let ref):
                entry.insert(ref)
            case .delete(let ref):
                entry.delete(ref)
            case .bulkInsert(let refs):
                entry.insert(refs)
            case .bulkDelete(let refs):
                entry.remove(refs)
            }
        }
    }
    
    /// Multi-level buffer for message propagation
    private struct MessageBuffer {
        var messages: [Key: [Message]] = [:]
        var capacity: Int
        var compressedSize: Int = 0
        
        init(capacity: Int) {
            self.capacity = capacity
        }
        
        mutating func append(key: Key, message: Message) {
            messages[key, default: []].append(message)
        }
        
        var messageCount: Int {
            messages.values.reduce(0) { $0 + $1.count }
        }
        
        var isFull: Bool {
            messageCount >= capacity
        }
        
        mutating func clear() {
            messages.removeAll(keepingCapacity: true)
            compressedSize = 0
        }
    }
    
    // MARK: - Tree Levels
    
    /// Represents a level in the fractal tree hierarchy
    private struct TreeLevel {
        var buffer: MessageBuffer
        var baseData: [Key: TombstoneSet<Ref>]
        var compressionEnabled: Bool
        var stats: LevelStatistics
        
        init(bufferCapacity: Int, compressionEnabled: Bool = false) {
            self.buffer = MessageBuffer(capacity: bufferCapacity)
            self.baseData = [:]
            self.compressionEnabled = compressionEnabled
            self.stats = LevelStatistics()
        }
        
        mutating func incrementStats(operation: String) {
            stats.operationCount += 1
            stats.lastOperation = operation
            stats.lastOperationTime = Date()
        }
    }
    
    /// Statistics for a tree level
    private struct LevelStatistics {
        var operationCount: Int = 0
        var mergeCount: Int = 0
        var compactionCount: Int = 0
        var lastOperation: String = ""
        var lastOperationTime: Date?
    }
    
    // MARK: - Partitioning
    
    /// Partition for horizontal scaling
    private struct Partition {
        var keyRange: Range<Key>?
        var levels: [TreeLevel]
        var partitionId: Int
        
        init(partitionId: Int, levelCount: Int, bufferCapacity: Int) {
            self.partitionId = partitionId
            self.levels = (0..<levelCount).map { level in
                let capacity = bufferCapacity * (1 << level) // Exponential capacity per level
                let compression = level > 0 // Enable compression for lower levels
                return TreeLevel(bufferCapacity: capacity, compressionEnabled: compression)
            }
        }
        
        func contains(key: Key) -> Bool {
            guard let range = keyRange else { return true } // No range = accepts all
            return range.contains(key)
        }
    }
    
    // MARK: - Configuration
    
    /// Configuration for the fractal tree
    public struct Configuration {
        var bufferCapacity: Int = 256
        var levelCount: Int = 3
        var partitionCount: Int = 1
        var compressionEnabled: Bool = true
        var autoCompactionThreshold: Int = 1000
        var bulkOperationBatchSize: Int = 100
        var mergeStrategy: MergeStrategy = .lazy
        
        public init() {}
    }
    
    /// Strategy for merging messages
    public enum MergeStrategy {
        case lazy          // Merge only when necessary
        case eager         // Merge immediately
        case adaptive      // Adjust based on workload
    }
    
    // MARK: - Properties
    
    private var partitions: [Partition]
    private var config: Configuration
    private var globalStats: GlobalStatistics
    
    /// Global statistics for the entire tree
    private struct GlobalStatistics {
        var totalInserts: Int = 0
        var totalDeletes: Int = 0
        var totalBulkOperations: Int = 0
        var totalMerges: Int = 0
        var totalCompactions: Int = 0
        var avgMergeTime: TimeInterval = 0
        var lastOptimizationTime: Date?
    }
    
    // MARK: - Initialization
    
    public convenience init(bufferCapacity: Int = 256) {
        var config = Configuration()
        config.bufferCapacity = max(16, bufferCapacity)
        self.init(config: config)
    }
    
    public init(config: Configuration) {
        self.config = config
        self.partitions = (0..<config.partitionCount).map { partitionId in
            Partition(partitionId: partitionId, 
                     levelCount: config.levelCount, 
                     bufferCapacity: config.bufferCapacity)
        }
        self.globalStats = GlobalStatistics()
    }
    
    // MARK: - IndexProtocol Implementation

    public func insert(_ key: Key, _ ref: Ref) throws {
        let partition = selectPartition(for: key)
        try insertIntoPartition(partition: partition, key: key, message: .insert(ref))
        globalStats.totalInserts += 1
        
        try checkAndOptimize()
    }

    public func searchEquals(_ key: Key) throws -> [Ref] {
        let partition = selectPartition(for: key)
        return try searchInPartition(partition: partition, key: key)
    }

    public func range(_ lo: Key?, _ hi: Key?) throws -> [Ref] {
        var result: [Ref] = []
        
        // Query all partitions that might contain keys in range
        for i in partitions.indices {
            let partitionResults = try rangeInPartition(partition: i, lo: lo, hi: hi)
            result.append(contentsOf: partitionResults)
        }
        
        return result
    }

    public func remove(_ key: Key, _ ref: Ref) throws {
        let partition = selectPartition(for: key)
        try insertIntoPartition(partition: partition, key: key, message: .delete(ref))
        globalStats.totalDeletes += 1
        
        try checkAndOptimize()
    }
    
    // MARK: - Bulk Operations
    
    /// Bulk insert operation for efficient batch processing
    public func bulkInsert(keys: [Key], refs: [Ref]) throws {
        guard keys.count == refs.count else {
            throw FractalTreeError.bulkOperationMismatch
        }
        
        globalStats.totalBulkOperations += 1
        
        // Group by partition
        var partitionedOps: [Int: [(Key, Ref)]] = [:]
        for (key, ref) in zip(keys, refs) {
            let partition = selectPartition(for: key)
            partitionedOps[partition, default: []].append((key, ref))
        }
        
        // Execute batch per partition
        for (partitionId, ops) in partitionedOps {
            try bulkInsertIntoPartition(partition: partitionId, operations: ops)
        }
        
        try checkAndOptimize()
    }
    
    /// Bulk delete operation for efficient batch processing
    public func bulkDelete(keys: [Key], refs: [Ref]) throws {
        guard keys.count == refs.count else {
            throw FractalTreeError.bulkOperationMismatch
        }
        
        globalStats.totalBulkOperations += 1
        
        // Group by partition
        var partitionedOps: [Int: [(Key, Ref)]] = [:]
        for (key, ref) in zip(keys, refs) {
            let partition = selectPartition(for: key)
            partitionedOps[partition, default: []].append((key, ref))
        }
        
        // Execute batch per partition
        for (partitionId, ops) in partitionedOps {
            try bulkDeleteFromPartition(partition: partitionId, operations: ops)
        }
        
        try checkAndOptimize()
    }
    
    /// Bulk update operation (delete old + insert new)
    public func bulkUpdate(keys: [Key], oldRefs: [Ref], newRefs: [Ref]) throws {
        guard keys.count == oldRefs.count && keys.count == newRefs.count else {
            throw FractalTreeError.bulkOperationMismatch
        }
        
        try bulkDelete(keys: keys, refs: oldRefs)
        try bulkInsert(keys: keys, refs: newRefs)
    }
    
    // MARK: - Partition Operations
    
    private func selectPartition(for key: Key) -> Int {
        // Simple hash-based partitioning
        guard partitions.count > 1 else { return 0 }
        
        // For partitions with defined ranges, check membership
        for (index, partition) in partitions.enumerated() {
            if partition.contains(key: key) {
                return index
            }
        }
        
        // Fallback to hash-based selection
        return abs(key.hashValue) % partitions.count
    }
    
    private func insertIntoPartition(partition: Int, key: Key, message: Message) throws {
        partitions[partition].levels[0].buffer.append(key: key, message: message)
        partitions[partition].levels[0].incrementStats(operation: "insert")
        
        // Check if top-level buffer needs flushing
        if partitions[partition].levels[0].buffer.isFull {
            try flushLevel(partition: partition, level: 0)
        }
    }
    
    private func bulkInsertIntoPartition(partition: Int, operations: [(Key, Ref)]) throws {
        // Batch messages for efficiency
        for batch in operations.chunked(into: config.bulkOperationBatchSize) {
            for (key, ref) in batch {
                partitions[partition].levels[0].buffer.append(key: key, message: .insert(ref))
            }
        }
        
        partitions[partition].levels[0].incrementStats(operation: "bulkInsert")
        
        // Flush if needed
        if partitions[partition].levels[0].buffer.isFull {
            try flushLevel(partition: partition, level: 0)
        }
    }
    
    private func bulkDeleteFromPartition(partition: Int, operations: [(Key, Ref)]) throws {
        // Batch messages for efficiency
        for batch in operations.chunked(into: config.bulkOperationBatchSize) {
            for (key, ref) in batch {
                partitions[partition].levels[0].buffer.append(key: key, message: .delete(ref))
            }
        }
        
        partitions[partition].levels[0].incrementStats(operation: "bulkDelete")
        
        // Flush if needed
        if partitions[partition].levels[0].buffer.isFull {
            try flushLevel(partition: partition, level: 0)
        }
    }
    
    private func searchInPartition(partition: Int, key: Key) throws -> [Ref] {
        var entry = TombstoneSet<Ref>()
        
        // Apply messages from all levels
        for level in partitions[partition].levels {
            // Apply buffered messages
            if let messages = level.buffer.messages[key] {
                for message in messages {
                    message.apply(to: &entry)
                }
            }
            
            // Merge with base data
            if let baseEntry = level.baseData[key] {
                entry.merge(with: baseEntry)
            }
        }
        
        return entry.visible()
    }
    
    private func rangeInPartition(partition: Int, lo: Key?, hi: Key?) throws -> [Ref] {
        var combined: [Key: TombstoneSet<Ref>] = [:]
        
        // Collect from all levels
        for level in partitions[partition].levels {
            // Apply buffered messages
            for (key, messages) in level.buffer.messages {
                if let lo = lo, key < lo { continue }
                if let hi = hi, key > hi { continue }
                
                var entry = combined[key] ?? TombstoneSet()
                for message in messages {
                    message.apply(to: &entry)
                }
                combined[key] = entry
            }
            
            // Merge base data
            for (key, baseEntry) in level.baseData {
                if let lo = lo, key < lo { continue }
                if let hi = hi, key > hi { continue }
                
                var entry = combined[key] ?? TombstoneSet()
                entry.merge(with: baseEntry)
                combined[key] = entry
            }
        }
        
        // Sort and collect
        let sortedKeys = combined.keys.sorted()
        var result: [Ref] = []
        for key in sortedKeys {
            if let entry = combined[key] {
                result.append(contentsOf: entry.visible())
            }
        }
        
        return result
    }
    
    // MARK: - Hierarchical Merge Operations
    
    /// Flushes messages from one level to the next
    private func flushLevel(partition: Int, level: Int) throws {
        let startTime = Date()
        
        guard level < partitions[partition].levels.count - 1 else {
            // Last level - flush to base
            try flushToBase(partition: partition, level: level)
            return
        }
        
        let messages = partitions[partition].levels[level].buffer.messages
        
        // Apply merge strategy
        switch config.mergeStrategy {
        case .lazy:
            // Only propagate full buffers
            guard partitions[partition].levels[level].buffer.isFull else { return }
            try propagateMessages(partition: partition, from: level, to: level + 1, messages: messages)
            
        case .eager:
            // Always propagate immediately
            try propagateMessages(partition: partition, from: level, to: level + 1, messages: messages)
            
        case .adaptive:
            // Decide based on buffer fill ratio and lower level capacity
            let fillRatio = Double(partitions[partition].levels[level].buffer.messageCount) / 
                           Double(partitions[partition].levels[level].buffer.capacity)
            if fillRatio > 0.7 {
                try propagateMessages(partition: partition, from: level, to: level + 1, messages: messages)
            }
        }
        
        // Clear buffer after flush
        partitions[partition].levels[level].buffer.clear()
        partitions[partition].levels[level].stats.mergeCount += 1
        
        // Update global stats
        globalStats.totalMerges += 1
        let mergeTime = Date().timeIntervalSince(startTime)
        globalStats.avgMergeTime = (globalStats.avgMergeTime * Double(globalStats.totalMerges - 1) + mergeTime) / Double(globalStats.totalMerges)
    }
    
    /// Propagates messages from one level to the next
    private func propagateMessages(partition: Int, from: Int, to: Int, messages: [Key: [Message]]) throws {
        for (key, msgs) in messages {
            for message in msgs {
                partitions[partition].levels[to].buffer.append(key: key, message: message)
            }
        }
        
        // Recursively flush if lower level is full
        if partitions[partition].levels[to].buffer.isFull {
            try flushLevel(partition: partition, level: to)
        }
    }
    
    /// Flushes messages to the base data of a level
    private func flushToBase(partition: Int, level: Int) throws {
        let messages = partitions[partition].levels[level].buffer.messages
        
        for (key, msgs) in messages {
            var entry = partitions[partition].levels[level].baseData[key] ?? TombstoneSet()
            
            for message in msgs {
                message.apply(to: &entry)
            }
            
            if entry.isDead {
                partitions[partition].levels[level].baseData.removeValue(forKey: key)
            } else {
                partitions[partition].levels[level].baseData[key] = entry
            }
        }
        
        partitions[partition].levels[level].buffer.clear()
    }
    
    // MARK: - Compression
    
    /// Compresses key-value data for a level (placeholder for actual compression)
    private func compressLevel(partition: Int, level: Int) throws {
        guard partitions[partition].levels[level].compressionEnabled else { return }
        
        // In a real implementation, this would compress the baseData dictionary
        // For now, we just mark the compression as done
        partitions[partition].levels[level].buffer.compressedSize = 
            partitions[partition].levels[level].baseData.count
    }
    
    // MARK: - Optimization Algorithms
    
    /// Checks if optimization is needed and performs it
    private func checkAndOptimize() throws {
        let totalOps = globalStats.totalInserts + globalStats.totalDeletes
        
        guard totalOps % config.autoCompactionThreshold == 0 else { return }
        
        try optimize()
    }
    
    /// Performs full tree optimization
    public func optimize() throws {
        _ = Date()
        
        // Flush all pending messages
        for partitionId in partitions.indices {
            for level in (0..<partitions[partitionId].levels.count).reversed() {
                if !partitions[partitionId].levels[level].buffer.messages.isEmpty {
                    try flushLevel(partition: partitionId, level: level)
                }
            }
        }
        
        // Compact base data
        for partitionId in partitions.indices {
            try compactPartition(partition: partitionId)
        }
        
        // Compress levels
        for partitionId in partitions.indices {
            for level in partitions[partitionId].levels.indices {
                try compressLevel(partition: partitionId, level: level)
            }
        }
        
        globalStats.lastOptimizationTime = Date()
        globalStats.totalCompactions += 1
    }
    
    /// Compacts a partition by removing dead entries and consolidating data
    private func compactPartition(partition: Int) throws {
        for level in partitions[partition].levels.indices {
            var compacted: [Key: TombstoneSet<Ref>] = [:]
            
            for (key, entry) in partitions[partition].levels[level].baseData {
                if !entry.isDead {
                    compacted[key] = entry
                }
            }
            
            partitions[partition].levels[level].baseData = compacted
            partitions[partition].levels[level].stats.compactionCount += 1
        }
    }
    
    // MARK: - Statistics & Diagnostics
    
    /// Returns detailed statistics about the tree
    public func getStatistics() -> FractalTreeStatistics {
        var partitionStats: [PartitionStatistics] = []
        
        for partition in partitions {
            let totalOps = partition.levels.reduce(0) { $0 + $1.stats.operationCount }
            let totalMerges = partition.levels.reduce(0) { $0 + $1.stats.mergeCount }
            let totalCompactions = partition.levels.reduce(0) { $0 + $1.stats.compactionCount }
            
            let stats = PartitionStatistics(
                partitionId: partition.partitionId,
                levelCount: partition.levels.count,
                totalKeys: partition.levels.reduce(0) { $0 + $1.baseData.count },
                totalMessages: partition.levels.reduce(0) { $0 + $1.buffer.messageCount },
                operationCount: totalOps,
                mergeCount: totalMerges,
                compactionCount: totalCompactions
            )
            partitionStats.append(stats)
        }
        
        return FractalTreeStatistics(
            totalInserts: globalStats.totalInserts,
            totalDeletes: globalStats.totalDeletes,
            totalBulkOperations: globalStats.totalBulkOperations,
            totalMerges: globalStats.totalMerges,
            totalCompactions: globalStats.totalCompactions,
            avgMergeTime: globalStats.avgMergeTime,
            lastOptimizationTime: globalStats.lastOptimizationTime,
            partitionStats: partitionStats,
            levelCount: config.levelCount,
            partitionCount: config.partitionCount,
            bufferCapacity: config.bufferCapacity
        )
    }
    
    /// Returns memory usage estimate in bytes
    public func estimateMemoryUsage() -> UInt64 {
        var total: UInt64 = 0
        
        for partition in partitions {
            for level in partition.levels {
                // Rough estimate: 64 bytes per key-value pair + 32 bytes per message
                total += UInt64(level.baseData.count * 64)
                total += UInt64(level.buffer.messageCount * 32)
            }
        }
        
        return total
    }
}

// MARK: - Supporting Types

public struct FractalTreeStatistics {
    let totalInserts: Int
    let totalDeletes: Int
    let totalBulkOperations: Int
    let totalMerges: Int
    let totalCompactions: Int
    let avgMergeTime: TimeInterval
    let lastOptimizationTime: Date?
    let partitionStats: [PartitionStatistics]
    let levelCount: Int
    let partitionCount: Int
    let bufferCapacity: Int
}

public struct PartitionStatistics {
    let partitionId: Int
    let levelCount: Int
    let totalKeys: Int
    let totalMessages: Int
    let operationCount: Int
    let mergeCount: Int
    let compactionCount: Int
}

public enum FractalTreeError: Error {
    case bulkOperationMismatch
    case partitionNotFound
    case invalidConfiguration
}

// MARK: - Array Extension for Chunking

private extension Array {
    func chunked(into size: Int) -> [[Element]] {
        stride(from: 0, to: count, by: size).map {
            Array(self[$0..<Swift.min($0 + size, count)])
        }
    }
}
