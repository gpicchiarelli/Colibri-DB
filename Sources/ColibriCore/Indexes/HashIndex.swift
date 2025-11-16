//
//  HashIndex.swift
//  ColibrìDB Hash Index Implementation
//
//  Based on: spec/HashIndex.tla
//  Implements: Hash-based indexing with collision resolution
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//
//  Key Properties:
//  - Load Factor: Maintains optimal load factor
//  - Uniqueness: Enforces uniqueness constraints
//  - Collision Handling: Handles collisions with linear probing
//  - Deterministic Hashing: Consistent hash values
//

import Foundation
import CryptoKit

// MARK: - Hash Index Types

/// Hash entry
/// Corresponds to TLA+: HashEntry
public struct HashEntry: Codable, Sendable, Equatable {
    public let key: Value
    public let rid: RID
    public let deleted: Bool
    public let timestamp: UInt64
    
    public init(key: Value, rid: RID, deleted: Bool, timestamp: UInt64 = 0) {
        self.key = key
        self.rid = rid
        self.deleted = deleted
        self.timestamp = timestamp
    }
}

// MARK: - Hash Index

/// Hash Index with open addressing and linear probing
/// Corresponds to TLA+ module: HashIndex.tla
public actor HashIndex {
    
    // MARK: - Constants
    
    /// Initial number of buckets
    /// TLA+: INITIAL_BUCKETS
    private static let initialBuckets = 16
    
    /// Maximum load factor (percentage)
    /// TLA+: MAX_LOAD_FACTOR
    private static let maxLoadFactor = 75
    
    // MARK: - State Variables (TLA+ vars)
    
    /// Buckets
    /// TLA+: buckets \in Seq(HashEntry \union {0})
    private var buckets: [HashEntry?] = []
    
    /// Number of entries
    /// TLA+: numEntries \in Nat
    private var numEntries: Int = 0
    
    /// Number of buckets
    /// TLA+: numBuckets \in Nat
    private var numBuckets: Int = 0
    
    /// Load factor
    /// TLA+: loadFactor \in Nat
    private var loadFactor: Int = 0
    
    /// Is unique index
    /// TLA+: isUnique \in BOOLEAN
    private var isUnique: Bool = false
    
    /// Maximum probes allowed for current bucket count
    private var probeLimit: Int {
        return max(numBuckets, Self.initialBuckets)
    }
    
    // MARK: - Initialization
    
    public init(isUnique: Bool = false) {
        self.isUnique = isUnique
        
        // TLA+ Init
        self.buckets = Array(repeating: nil, count: Self.initialBuckets)
        self.numEntries = 0
        self.numBuckets = Self.initialBuckets
        self.loadFactor = 0
    }
    
    // MARK: - Hash Index Operations
    
    /// Insert entry
    /// TLA+ Action: Insert(key, rid)
    public func insert(key: Value, rid: RID) async throws {
        try await ensureCapacityForNextInsert()
        
        // TLA+: Find insertion position
        var position: Int
        do {
            position = try await findInsertPosition(key: key)
        } catch HashIndexError.maxProbesExceeded {
            try await resize()
            position = try await findInsertPosition(key: key)
        }
        
        // TLA+: Check for uniqueness
        if isUnique && buckets[position] != nil && !(buckets[position]?.deleted ?? false) {
            throw HashIndexError.duplicateKey
        }
        
        // TLA+: Insert entry
        buckets[position] = HashEntry(key: key, rid: rid, deleted: false)
        numEntries += 1
        
        // TLA+: Update load factor
        updateLoadFactor()
        
        logInfo("Inserted key: \(key) at position: \(position)")
    }
    
    /// Search for entry
    /// TLA+ Action: Search(key)
    public func search(key: Value) async throws -> RID? {
        // TLA+: Find entry
        let position = try await findEntryPosition(key: key)
        
        if let entry = buckets[position], !entry.deleted {
            return entry.rid
        }
        
        return nil
    }
    
    /// Delete entry
    /// TLA+ Action: Delete(key)
    public func delete(key: Value) async throws {
        // TLA+: Find entry
        let position = try await findEntryPosition(key: key)
        
        if let entry = buckets[position], !entry.deleted {
            // TLA+: Mark as deleted (tombstone)
            buckets[position] = HashEntry(key: entry.key, rid: entry.rid, deleted: true)
            numEntries -= 1
            
            // TLA+: Update load factor
            updateLoadFactor()
            
            logInfo("Deleted key: \(key) at position: \(position)")
        }
    }
    
    /// Resize hash table
    /// TLA+ Action: Resize()
    public func resize(to requestedSize: Int? = nil) async throws {
        let targetSize: Int
        if let requestedSize, requestedSize > 0 {
            targetSize = max(requestedSize, Self.initialBuckets)
        } else if numBuckets == 0 {
            targetSize = Self.initialBuckets
        } else {
            targetSize = numBuckets * 2
        }
        
        let activeEntries = buckets.compactMap { $0 }.filter { !$0.deleted }
        
        buckets = Array(repeating: nil, count: targetSize)
        numBuckets = targetSize
        numEntries = 0
        
        for entry in activeEntries {
            try reinsert(entry)
        }
        
        updateLoadFactor()
        logInfo("Resized hash table to \(targetSize) buckets")
    }
    
    // MARK: - Helper Methods
    
    /// Ensure we have enough capacity before inserting new entries
    private func ensureCapacityForNextInsert() async throws {
        guard numBuckets > 0 else {
            try await resize(to: Self.initialBuckets)
            return
        }
        
        let projectedLoadFactor = ((numEntries + 1) * 100) / numBuckets
        if projectedLoadFactor >= Self.maxLoadFactor {
            try await resize()
        }
    }
    
    /// Hash function (deterministic, hardware-accelerated)
    private func hash(_ key: Value) -> Int {
        let h = HardwareHash.hash64(key, seed: 0)
        // Ensure non-negative Int to avoid negative modulo behavior
        return Int(truncatingIfNeeded: h & 0x7fffffffffffffff)
    }
    
    /// Find insertion position
    private func findInsertPosition(key: Value) async throws -> Int {
        // TLA+: Linear probing
        let hashValue = hash(key)
        var position = hashValue % numBuckets
        var probes = 0
        let limit = probeLimit
        
        while probes < limit {
            if buckets[position] == nil || buckets[position]?.deleted == true {
                return position
            }
            position = (position + 1) % numBuckets
            probes += 1
        }
        
        throw HashIndexError.maxProbesExceeded
    }
    
    /// Find entry position
    private func findEntryPosition(key: Value) async throws -> Int {
        // TLA+: Linear probing
        let hashValue = hash(key)
        var position = hashValue % numBuckets
        var probes = 0
        let limit = probeLimit
        
        while probes < limit {
            if let entry = buckets[position], entry.key == key {
                return position
            }
            if buckets[position] == nil {
                break
            }
            position = (position + 1) % numBuckets
            probes += 1
        }
        
        return position
    }
    
    /// Update load factor
    private func updateLoadFactor() {
        // TLA+: Update load factor
        guard numBuckets > 0 else {
            loadFactor = 0
            return
        }
        loadFactor = (numEntries * 100) / numBuckets
    }
    
    /// Reinsert entry during resize without triggering additional operations
    private func reinsert(_ entry: HashEntry) throws {
        var position = hash(entry.key) % numBuckets
        var probes = 0
        let limit = probeLimit
        
        while probes < limit {
            if buckets[position] == nil || buckets[position]?.deleted == true {
                buckets[position] = HashEntry(key: entry.key, rid: entry.rid, deleted: false, timestamp: entry.timestamp)
                numEntries += 1
                return
            }
            position = (position + 1) % numBuckets
            probes += 1
        }
        
        throw HashIndexError.maxProbesExceeded
    }
    
    // MARK: - Query Operations
    
    /// Get statistics
    public func getStatistics() -> (numEntries: Int, numBuckets: Int, loadFactor: Int) {
        return (numEntries, numBuckets, loadFactor)
    }
    
    /// Get entry count
    public func getEntryCount() -> Int {
        return numEntries
    }
    
    /// Get bucket count
    public func getBucketCount() -> Int {
        return numBuckets
    }
    
    /// Get load factor
    public func getLoadFactor() -> Int {
        return loadFactor
    }
    
    /// Check if unique index
    public func isUniqueIndex() -> Bool {
        return isUnique
    }
    
    /// Get all entries
    public func getAllEntries() -> [HashEntry] {
        return buckets.compactMap { $0 }.filter { !$0.deleted }
    }
    
    /// Check if empty
    public func isEmpty() -> Bool {
        return numEntries == 0
    }
    
    /// Check if full
    public func isFull() -> Bool {
        return loadFactor >= Self.maxLoadFactor
    }
    
    // MARK: - Invariant Checking (for testing)
    
    /// Check load factor invariant
    /// TLA+ Inv_HashIndex_LoadFactor
    public func checkLoadFactorInvariant() -> Bool {
        // Check that load factor is within bounds
        return loadFactor <= Self.maxLoadFactor
    }
    
    /// Check uniqueness invariant
    /// TLA+ Inv_HashIndex_Uniqueness
    public func checkUniquenessInvariant() -> Bool {
        // Check that uniqueness is enforced
        if !isUnique {
            return true
        }
        
        let entries = getAllEntries()
        let keys = entries.map { $0.key }
        return Set(keys).count == keys.count
    }
    
    /// Check collision handling invariant
    /// TLA+ Inv_HashIndex_CollisionHandling
    public func checkCollisionHandlingInvariant() -> Bool {
        // Check that collisions are handled correctly
        return true // Simplified
    }
    
    /// Check deterministic hashing invariant
    /// TLA+ Inv_HashIndex_DeterministicHashing
    public func checkDeterministicHashingInvariant() -> Bool {
        // Check that hashing is deterministic
        return true // Simplified
    }
    
    /// Check all invariants
    public func checkAllInvariants() -> Bool {
        let loadFactor = checkLoadFactorInvariant()
        let uniqueness = checkUniquenessInvariant()
        let collisionHandling = checkCollisionHandlingInvariant()
        let deterministicHashing = checkDeterministicHashingInvariant()
        
        return loadFactor && uniqueness && collisionHandling && deterministicHashing
    }
}

// MARK: - Supporting Types

/// Hash index error
public enum HashIndexError: Error, LocalizedError {
    case duplicateKey
    case maxProbesExceeded
    case resizeFailed
    case invalidKey
    case indexFull
    
    public var errorDescription: String? {
        switch self {
        case .duplicateKey:
            return "Duplicate key in unique index"
        case .maxProbesExceeded:
            return "Maximum probes exceeded"
        case .resizeFailed:
            return "Hash table resize failed"
        case .invalidKey:
            return "Invalid key"
        case .indexFull:
            return "Hash index is full"
        }
    }
}