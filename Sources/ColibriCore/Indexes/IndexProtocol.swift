//
//  IndexProtocol.swift
//  ColibrìDB Index Protocol
//
//  Based on: spec/Index.tla
//  Implements: Unified interface for all index types
//  Author: ColibrìDB Team
//  Date: 2025-11-12
//
//  Key Properties:
//  - Insert → Seek Consistency: After insert(key, rid), seek(key) returns rid
//  - Scan Order: For ordered indexes, scan returns sorted results
//  - Delete Reduces Cardinality: delete(key) reduces entry count
//  - No Phantom Keys: Deleted keys don't appear in scans
//  - Idempotent Operations: Multiple inserts/deletes behave correctly
//

import Foundation

// MARK: - Index Protocol

/// Unified protocol for all index implementations
/// All index types (BTree, ART, Hash, LSM, SkipList, etc.) must conform to this protocol
/// to ensure consistent behavior and enable property-based testing.
public protocol IndexProtocol: Sendable {
    
    // MARK: - Core Operations
    
    /// Insert a key-value pair into the index
    /// - Parameters:
    ///   - key: The key to insert
    ///   - rid: The record identifier (page ID + slot ID)
    /// - Throws: IndexError if the operation fails
    /// - Invariant: After insert(k, r), seek(k) must return r (or contain r for multi-value indexes)
    func insert(key: Value, rid: RID) async throws
    
    /// Search for a key in the index
    /// - Parameter key: The key to search for
    /// - Returns: Array of RIDs associated with the key, or nil if not found
    /// - Note: For unique indexes, the array contains at most one RID
    ///         For non-unique indexes, the array may contain multiple RIDs
    func seek(key: Value) async throws -> [RID]?
    
    /// Scan a range of keys
    /// - Parameters:
    ///   - minKey: The minimum key (inclusive)
    ///   - maxKey: The maximum key (inclusive)
    /// - Returns: Array of (key, [RID]) pairs in the range
    /// - Invariant: For ordered indexes, results must be sorted by key
    /// - Note: Hash indexes may not support ordered scans
    func scan(minKey: Value, maxKey: Value) async throws -> [(Value, [RID])]
    
    /// Delete a key from the index
    /// - Parameter key: The key to delete
    /// - Throws: IndexError if the operation fails
    /// - Invariant: After delete(k), seek(k) must return nil
    /// - Invariant: Cardinality must decrease (unless key didn't exist)
    func delete(key: Value) async throws
    
    /// Rebuild the index from scratch
    /// - Throws: IndexError if the operation fails
    /// - Note: Used for index maintenance and optimization
    func rebuild() async throws
    
    // MARK: - Metadata Operations
    
    /// Get the number of distinct keys in the index
    /// - Returns: The cardinality (number of distinct keys)
    func getCardinality() async throws -> Int
    
    /// Whether this index supports ordered scans
    /// - Returns: true if scan() returns results in sorted order, false otherwise
    /// - Note: BTree, ART, LSM, SkipList return true; Hash returns false
    var supportsOrderedScans: Bool { get }
    
    // MARK: - Optional Operations (with default implementations)
    
    /// Get statistics about the index
    /// - Returns: Dictionary of statistics (size, height, etc.)
    func getStatistics() async throws -> [String: Any]
    
    /// Clear all entries from the index
    /// - Throws: IndexError if the operation fails
    func clear() async throws
    
    /// Check if the index contains a key
    /// - Parameter key: The key to check
    /// - Returns: true if the key exists, false otherwise
    func contains(key: Value) async throws -> Bool
}

// MARK: - Default Implementations

extension IndexProtocol {
    
    /// Default implementation of getStatistics
    public func getStatistics() async throws -> [String: Any] {
        return [
            "cardinality": try await getCardinality(),
            "supportsOrderedScans": supportsOrderedScans
        ]
    }
    
    /// Default implementation of clear (rebuild with no data)
    public func clear() async throws {
        try await rebuild()
    }
    
    /// Default implementation of contains (uses seek)
    public func contains(key: Value) async throws -> Bool {
        let result = try await seek(key: key)
        return result != nil && !result!.isEmpty
    }
}

// MARK: - Index Protocol Errors

/// Errors that can occur during index protocol operations
public enum IndexProtocolError: Error, LocalizedError {
    case keyNotFound(String)
    case duplicateKey(String)
    case invalidKey(String)
    case invalidRID(String)
    case indexFull(String)
    case corruptedIndex(String)
    case unsupportedOperation(String)
    case internalError(String)
    
    public var errorDescription: String? {
        switch self {
        case .keyNotFound(let msg):
            return "Key not found: \(msg)"
        case .duplicateKey(let msg):
            return "Duplicate key: \(msg)"
        case .invalidKey(let msg):
            return "Invalid key: \(msg)"
        case .invalidRID(let msg):
            return "Invalid RID: \(msg)"
        case .indexFull(let msg):
            return "Index full: \(msg)"
        case .corruptedIndex(let msg):
            return "Corrupted index: \(msg)"
        case .unsupportedOperation(let msg):
            return "Unsupported operation: \(msg)"
        case .internalError(let msg):
            return "Internal error: \(msg)"
        }
    }
}

// MARK: - Index Implementation Types

/// Enumeration of supported index implementation types
public enum IndexImplementationType: String, Codable, Sendable {
    case btree = "BTree"
    case art = "ART"
    case hash = "Hash"
    case lsm = "LSM"
    case skiplist = "SkipList"
    case fractal = "Fractal"
    case ttree = "TTree"
    case radix = "Radix"
    case bloom = "Bloom"
}

// MARK: - Index Configuration

/// Configuration options for index creation
public struct IndexProtocolConfiguration: Codable, Sendable {
    public let type: IndexImplementationType
    public let isUnique: Bool
    public let allowNulls: Bool
    public let pageSize: Int
    public let cacheSize: Int
    
    public init(
        type: IndexImplementationType,
        isUnique: Bool = false,
        allowNulls: Bool = true,
        pageSize: Int = 4096,
        cacheSize: Int = 100
    ) {
        self.type = type
        self.isUnique = isUnique
        self.allowNulls = allowNulls
        self.pageSize = pageSize
        self.cacheSize = cacheSize
    }
}

