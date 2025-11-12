//
//  IndexWrappers.swift
//  ColibrìDB Index Protocol Wrappers
//
//  TDD Macro-task A: GREEN phase
//  Author: ColibrìDB TDD Chief Engineer
//  Date: 2025-01-XX
//
//  Wrappers to adapt existing index implementations to unified Index protocol.
//  Minimal changes to existing code - wrappers provide protocol conformance.
//

import Foundation

// MARK: - BTreeIndex Wrapper

/// Wrapper to make BTreeIndex conform to Index protocol
public struct BTreeIndexWrapper: Index {
    private let btree: BTreeIndex
    private let lock = NSLock()
    
    public var supportsOrderedScans: Bool {
        return true  // B+Tree supports ordered scans
    }
    
    public init(_ btree: BTreeIndex) {
        self.btree = btree
    }
    
    public func insert(key: Value, rid: RID) async throws {
        lock.lock()
        defer { lock.unlock() }
        try btree.insert(key: key, rid: rid)
    }
    
    public func seek(key: Value) async throws -> [RID]? {
        lock.lock()
        defer { lock.unlock() }
        return btree.search(key: key)
    }
    
    public func scan(minKey: Value, maxKey: Value) async throws -> [(Value, [RID])] {
        lock.lock()
        defer { lock.unlock() }
        return btree.rangeScan(minKey: minKey, maxKey: maxKey)
    }
    
    public func delete(key: Value) async throws {
        lock.lock()
        defer { lock.unlock() }
        try btree.delete(key: key)
    }
    
    public func rebuild() async throws {
        // BTreeIndex doesn't have explicit rebuild, but we can verify invariants
        lock.lock()
        defer { lock.unlock() }
        // Verify invariants are maintained
        assert(btree.checkKeyOrderInvariant(), "BTree key order invariant violated")
        assert(btree.checkBalancedHeightInvariant(), "BTree balanced height invariant violated")
    }
    
    public func getCardinality() async throws -> Int {
        lock.lock()
        defer { lock.unlock() }
        return btree.getKeyCount()
    }
}

// MARK: - ARTIndex Wrapper

/// Wrapper to make ARTIndex conform to Index protocol
public struct ARTIndexWrapper: Index {
    private let art: ARTIndex
    
    public var supportsOrderedScans: Bool {
        return true  // ART supports prefix scans (ordered)
    }
    
    public init(_ art: ARTIndex) {
        self.art = art
    }
    
    public func insert(key: Value, rid: RID) async throws {
        // Convert Value to Data for ART
        let keyData = try valueToData(key)
        await art.insert(key: keyData, rid: rid)
    }
    
    public func seek(key: Value) async throws -> [RID]? {
        let keyData = try valueToData(key)
        return await art.search(key: keyData)
    }
    
    public func scan(minKey: Value, maxKey: Value) async throws -> [(Value, [RID])] {
        // ART supports prefix scans, but not arbitrary range scans
        // For now, we'll use prefix scan with minKey as prefix
        // Note: This is a limitation - ART doesn't support arbitrary range scans efficiently
        let prefixData = try valueToData(minKey)
        let results = await art.prefixScan(prefix: prefixData)
        
        // Convert back to Value and filter by range
        var filtered: [(Value, [RID])] = []
        for (data, rids) in results {
            if let value = try? dataToValue(data), value >= minKey && value <= maxKey {
                filtered.append((value, rids))
            }
        }
        return filtered
    }
    
    public func delete(key: Value) async throws {
        // ART doesn't have explicit delete in current implementation
        // For now, we'll mark this as not supported
        throw IndexError.operationNotSupported("ARTIndex delete not yet implemented")
    }
    
    public func getCardinality() async throws -> Int {
        return await art.getTotalKeys()
    }
    
    // MARK: - Helper Methods
    
    private func valueToData(_ value: Value) throws -> Data {
        let encoder = JSONEncoder()
        return try encoder.encode(value)
    }
    
    private func dataToValue(_ data: Data) throws -> Value {
        let decoder = JSONDecoder()
        return try decoder.decode(Value.self, from: data)
    }
}

// MARK: - HashIndex Wrapper

/// Wrapper to make HashIndex conform to Index protocol
public struct HashIndexWrapper: Index {
    private let hashIndex: HashIndex
    
    public var supportsOrderedScans: Bool {
        return false  // Hash indexes don't support ordered scans
    }
    
    public init(_ hashIndex: HashIndex) {
        self.hashIndex = hashIndex
    }
    
    public func insert(key: Value, rid: RID) async throws {
        try await hashIndex.insert(key: key, rid: rid)
    }
    
    public func seek(key: Value) async throws -> [RID]? {
        if let rid = try await hashIndex.search(key: key) {
            return [rid]
        }
        return nil
    }
    
    public func scan(minKey: Value, maxKey: Value) async throws -> [(Value, [RID])] {
        // Hash indexes don't support ordered range scans efficiently
        // Return all entries matching range (inefficient, but conforms to protocol)
        // Note: Results may not be sorted
        let entries = await hashIndex.getAllEntries()
        return entries.filter { entry in
            !entry.deleted && entry.key >= minKey && entry.key <= maxKey
        }.map { ($0.key, [$0.rid]) }
    }
    
    public func delete(key: Value) async throws {
        try await hashIndex.delete(key: key)
    }
    
    public func getCardinality() async throws -> Int {
        let stats = await hashIndex.getStatistics()
        return stats.numEntries
    }
}

// MARK: - LSMTree Wrapper

/// Wrapper to make LSMTree conform to Index protocol
public struct LSMTreeWrapper: Index {
    private let lsm: LSMTree
    
    public var supportsOrderedScans: Bool {
        return true  // LSM-Tree supports ordered scans
    }
    
    public init(_ lsm: LSMTree) {
        self.lsm = lsm
    }
    
    public func insert(key: Value, rid: RID) async throws {
        await lsm.insert(key: key, rid: rid)
    }
    
    public func seek(key: Value) async throws -> [RID]? {
        return await lsm.search(key: key)
    }
    
    public func scan(minKey: Value, maxKey: Value) async throws -> [(Value, [RID])] {
        return await lsm.rangeScan(minKey: minKey, maxKey: maxKey)
    }
    
    public func delete(key: Value) async throws {
        // LSM-Tree delete is typically a tombstone insert
        // Note: This is a limitation - proper LSM delete requires tombstone handling
        // For now, we'll insert a tombstone marker
        // In production, this should be handled by the LSM-Tree implementation
        let tombstoneRID = RID(pageID: UInt64.max, slotID: UInt32.max)  // Special marker
        try await lsm.insert(key: key, rid: tombstoneRID)
    }
    
    public func getCardinality() async throws -> Int {
        // LSM-Tree doesn't expose cardinality directly
        // We'll estimate from scan
        let allResults = await lsm.rangeScan(minKey: .int(Int64.min), maxKey: .int(Int64.max))
        return Set(allResults.map { $0.0 }).count
    }
}

// MARK: - SkipList Wrapper

/// Wrapper to make SkipList conform to Index protocol
public struct SkipListWrapper: Index {
    private let skipList: SkipList
    
    public var supportsOrderedScans: Bool {
        return true  // SkipList supports ordered scans
    }
    
    public init(_ skipList: SkipList) {
        self.skipList = skipList
    }
    
    public func insert(key: Value, rid: RID) async throws {
        await skipList.insert(key: key, rid: rid)
    }
    
    public func seek(key: Value) async throws -> [RID]? {
        return await skipList.search(key: key)
    }
    
    public func scan(minKey: Value, maxKey: Value) async throws -> [(Value, [RID])] {
        return await skipList.rangeScan(minKey: minKey, maxKey: maxKey)
    }
    
    public func delete(key: Value) async throws {
        await skipList.delete(key: key)
    }
    
    public func getCardinality() async throws -> Int {
        // SkipList doesn't expose cardinality directly
        // We'll estimate from scan
        let allResults = await skipList.rangeScan(minKey: .int(Int64.min), maxKey: .int(Int64.max))
        return Set(allResults.map { $0.0 }).count
    }
}

// MARK: - Supporting Types

extension IndexError {
    static func operationNotSupported(_ message: String) -> IndexError {
        // Use a generic error for now
        return .lookupFailed
    }
}

// MARK: - Value Comparison Helper
// Note: Value.Comparable conformance is already defined in Utilities/Extensions.swift
// This file relies on that extension for range scans
