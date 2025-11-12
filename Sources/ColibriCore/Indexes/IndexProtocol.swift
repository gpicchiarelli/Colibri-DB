//
//  IndexProtocol.swift
//  ColibrìDB Unified Index Protocol
//
//  TDD Macro-task A: Contratto Index unificato
//  Author: ColibrìDB TDD Chief Engineer
//  Date: 2025-01-XX
//
//  Defines unified contract for all index implementations:
//  - BTreeIndex, ARTIndex, HashIndex, LSMTree, SkipList
//
//  Key Properties (verified by IndexContractTests):
//  - Insert → Seek: insert(key, rid) → seek(key) returns last value
//  - Scan Order: scan(range) returns sorted results for ordered indexes
//  - Delete Reduces Cardinality: delete(key) reduces entry count
//  - No Phantom Keys: deleted keys don't appear in scans
//

import Foundation

// MARK: - Index Protocol

/// Unified protocol for all index implementations
/// TLA+ Contract: IndexContract
public protocol Index: Sendable {
    /// Insert a key-RID pair into the index
    /// TLA+ Action: Insert(key, rid)
    /// Precondition: key and rid are valid
    /// Postcondition: key inserted, index remains consistent
    func insert(key: Value, rid: RID) async throws
    
    /// Seek for a key in the index
    /// TLA+ Action: Seek(key)
    /// Precondition: key is valid
    /// Postcondition: returns RIDs if found, nil otherwise
    func seek(key: Value) async throws -> [RID]?
    
    /// Range scan: find all keys in range [minKey, maxKey]
    /// TLA+ Action: Scan(minKey, maxKey)
    /// Precondition: minKey <= maxKey (for ordered indexes)
    /// Postcondition: returns all (key, RIDs) pairs in range
    func scan(minKey: Value, maxKey: Value) async throws -> [(Value, [RID])]
    
    /// Delete a key from the index
    /// TLA+ Action: Delete(key)
    /// Precondition: key exists in index (optional, some indexes allow delete of non-existent keys)
    /// Postcondition: key deleted, index remains consistent
    func delete(key: Value) async throws
    
    /// Rebuild the index (optional, for maintenance)
    /// TLA+ Action: Rebuild()
    /// Postcondition: index rebuilt, all entries preserved
    func rebuild() async throws
    
    /// Get cardinality (number of distinct keys)
    /// TLA+ Query: Cardinality()
    func getCardinality() async throws -> Int
    
    /// Check if index supports ordered scans
    /// Some indexes (e.g., HashIndex) may not support ordered range scans
    var supportsOrderedScans: Bool { get }
}

// MARK: - Index Contract Extensions

extension Index {
    /// Default implementation: rebuild does nothing
    public func rebuild() async throws {
        // Default: no-op
    }
    
    /// Default: assume ordered scans are supported
    public var supportsOrderedScans: Bool {
        return true
    }
}
