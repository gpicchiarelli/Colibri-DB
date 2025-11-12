//
//  IndexProtocol.swift
//  ColibrìDB - Unified Index Protocol
//
//  TDD: RED Phase - Defines contract for all index implementations
//  Based on: spec/IndexSubsystem.tla
//  Author: TDD Chief Engineer
//  Date: 2025-01-27
//
//  Contract Properties:
//  - insert(key, rid) → seek(key) returns rid
//  - scan(range) returns ordered results
//  - delete(key) reduces cardinality
//  - No phantom keys (insert → seek → delete → seek returns nil)
//

import Foundation

// MARK: - Index Protocol

/// Unified protocol for all index implementations
/// All indices (BTree, ART, Hash, LSM, SkipList) must conform to this contract
public protocol Index: Sendable {
    /// Insert a key-RID pair into the index
    /// Postcondition: After insert(k, r), seek(k) returns r
    func insert(key: Value, rid: RID) async throws
    
    /// Seek for a key in the index
    /// Returns: RIDs associated with the key, or nil if not found
    /// Postcondition: Returns last inserted value for key
    func seek(key: Value) async throws -> [RID]?
    
    /// Scan a range of keys [minKey, maxKey] (inclusive)
    /// Returns: Array of (key, RIDs) tuples in sorted order
    /// Postcondition: Results are sorted by key, all keys in [minKey, maxKey]
    func scan(minKey: Value, maxKey: Value) async throws -> [(Value, [RID])]
    
    /// Delete a key from the index
    /// Postcondition: After delete(k), seek(k) returns nil
    func delete(key: Value) async throws
    
    /// Rebuild the index (for maintenance/compaction)
    /// Postcondition: Index structure optimized, all entries preserved
    func rebuild() async throws
    
    /// Get cardinality (number of entries)
    /// Postcondition: Returns count of non-deleted entries
    func cardinality() async throws -> Int
}

// MARK: - Index Conformance Helpers

/// Helper to make synchronous indices async-compatible
public struct AsyncIndexWrapper<I: Index>: Index {
    private let index: I
    
    public init(_ index: I) {
        self.index = index
    }
    
    public func insert(key: Value, rid: RID) async throws {
        try await index.insert(key: key, rid: rid)
    }
    
    public func seek(key: Value) async throws -> [RID]? {
        try await index.seek(key: key)
    }
    
    public func scan(minKey: Value, maxKey: Value) async throws -> [(Value, [RID])] {
        try await index.scan(minKey: minKey, maxKey: maxKey)
    }
    
    public func delete(key: Value) async throws {
        try await index.delete(key: key)
    }
    
    public func rebuild() async throws {
        try await index.rebuild()
    }
    
    public func cardinality() async throws -> Int {
        try await index.cardinality()
    }
}
