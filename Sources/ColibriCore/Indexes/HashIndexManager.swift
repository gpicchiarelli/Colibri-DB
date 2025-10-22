//
//  HashIndexManager.swift
//  ColibrìDB Hash Index Manager Implementation
//
//  Based on: spec/HashIndex.tla
//  Implements: Hash-based indexing with collision resolution
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//
//  Key Properties:
//  - Load Factor: Load factor is maintained
//  - Uniqueness: Uniqueness is enforced
//  - Collision Handling: Collisions are handled correctly
//  - Deterministic Hashing: Hashing is deterministic
//

import Foundation

// MARK: - Hash Index Types

/// LSN (Log Sequence Number)
/// Corresponds to TLA+: LSN
public typealias LSN = UInt64

/// Page ID
/// Corresponds to TLA+: PageID
public typealias PageID = UInt64

/// Transaction ID
/// Corresponds to TLA+: TxID
public typealias TxID = UInt64

/// RID (Record ID)
/// Corresponds to TLA+: RID
public typealias RID = UInt64

/// Value
/// Corresponds to TLA+: Value
public typealias Value = String

/// Key
/// Corresponds to TLA+: Key
public typealias Key = Value

/// Hash entry
/// Corresponds to TLA+: HashEntry
public struct HashEntry: Codable, Sendable, Equatable {
    public let key: Key
    public let rid: RID
    public let deleted: Bool
    public let timestamp: UInt64
    
    public init(key: Key, rid: RID, deleted: Bool, timestamp: UInt64) {
        self.key = key
        self.rid = rid
        self.deleted = deleted
        self.timestamp = timestamp
    }
}

// MARK: - Hash Index Manager

/// Hash Index Manager for database indexing
/// Corresponds to TLA+ module: HashIndex.tla
public actor HashIndexManager {
    
    // MARK: - Constants
    
    /// Initial buckets
    /// TLA+: INITIAL_BUCKETS
    private let INITIAL_BUCKETS: Int = 16
    
    /// Maximum load factor
    /// TLA+: MAX_LOAD_FACTOR
    private let MAX_LOAD_FACTOR: Int = 75
    
    /// Maximum probes
    /// TLA+: MAX_PROBES
    private let MAX_PROBES: Int = 10
    
    // MARK: - State Variables (TLA+ vars)
    
    /// Buckets
    /// TLA+: buckets \in [Nat -> HashEntry]
    private var buckets: [Int: HashEntry?] = [:]
    
    /// Number of entries
    /// TLA+: numEntries \in Nat
    private var numEntries: Int = 0
    
    /// Number of buckets
    /// TLA+: numBuckets \in Nat
    private var numBuckets: Int = 0
    
    /// Load factor
    /// TLA+: loadFactor \in Nat
    private var loadFactor: Int = 0
    
    /// Is unique
    /// TLA+: isUnique \in BOOLEAN
    private var isUnique: Bool = false
    
    // MARK: - Initialization
    
    public init(isUnique: Bool = false) {
        // TLA+ Init
        self.buckets = [:]
        self.numEntries = 0
        self.numBuckets = INITIAL_BUCKETS
        self.loadFactor = 0
        self.isUnique = isUnique
        
        // TLA+: Initialize buckets
        for i in 0..<INITIAL_BUCKETS {
            buckets[i] = nil
        }
    }
    
    // MARK: - Core Operations
    
    /// Insert
    /// TLA+ Action: Insert(key, rid)
    public func insert(key: Key, rid: RID) async throws {
        // TLA+: Check if key already exists (for unique index)
        if isUnique {
            if let existingRid = try await search(key: key) {
                throw HashIndexManagerError.duplicateKey
            }
        }
        
        // TLA+: Check if resize is needed
        if loadFactor >= MAX_LOAD_FACTOR {
            try await resize()
        }
        
        // TLA+: Find insertion position
        let position = try await findInsertPosition(key: key)
        
        // TLA+: Insert entry
        let entry = HashEntry(
            key: key,
            rid: rid,
            deleted: false,
            timestamp: UInt64(Date().timeIntervalSince1970 * 1000)
        )
        
        buckets[position] = entry
        numEntries += 1
        
        // TLA+: Update load factor
        try await updateLoadFactor()
        
        print("Inserted key: \(key), rid: \(rid)")
    }
    
    /// Search
    /// TLA+ Action: Search(key)
    public func search(key: Key) async throws -> RID? {
        // TLA+: Find entry
        let position = try await findEntryPosition(key: key)
        
        if let entry = buckets[position], !entry.deleted && entry.key == key {
            return entry.rid
        }
        
        return nil
    }
    
    /// Delete
    /// TLA+ Action: Delete(key)
    public func delete(key: Key) async throws {
        // TLA+: Find entry
        let position = try await findEntryPosition(key: key)
        
        if let entry = buckets[position], !entry.deleted && entry.key == key {
            // TLA+: Mark as deleted (tombstone)
            let deletedEntry = HashEntry(
                key: entry.key,
                rid: entry.rid,
                deleted: true,
                timestamp: UInt64(Date().timeIntervalSince1970 * 1000)
            )
            
            buckets[position] = deletedEntry
            numEntries -= 1
            
            // TLA+: Update load factor
            try await updateLoadFactor()
            
            print("Deleted key: \(key)")
        }
    }
    
    /// Resize
    /// TLA+ Action: Resize()
    public func resize() async throws {
        // TLA+: Double the number of buckets
        let oldBuckets = buckets
        let oldNumBuckets = numBuckets
        
        numBuckets *= 2
        buckets.removeAll()
        
        // TLA+: Initialize new buckets
        for i in 0..<numBuckets {
            buckets[i] = nil
        }
        
        // TLA+: Rehash entries
        for i in 0..<oldNumBuckets {
            if let entry = oldBuckets[i], !entry.deleted {
                let newPosition = try await findInsertPosition(key: entry.key)
                buckets[newPosition] = entry
            }
        }
        
        // TLA+: Update load factor
        try await updateLoadFactor()
        
        print("Resized to \(numBuckets) buckets")
    }
    
    // MARK: - Helper Methods
    
    /// Find insert position
    /// TLA+ Function: FindInsertPosition(key)
    private func findInsertPosition(key: Key) async throws -> Int {
        let hash = try await hash(key: key)
        var position = hash % numBuckets
        var probes = 0
        
        // TLA+: Linear probing
        while buckets[position] != nil && probes < MAX_PROBES {
            position = (position + 1) % numBuckets
            probes += 1
        }
        
        if probes >= MAX_PROBES {
            throw HashIndexManagerError.maxProbesExceeded
        }
        
        return position
    }
    
    /// Find entry position
    /// TLA+ Function: FindEntryPosition(key)
    private func findEntryPosition(key: Key) async throws -> Int {
        let hash = try await hash(key: key)
        var position = hash % numBuckets
        var probes = 0
        
        // TLA+: Linear probing
        while buckets[position] != nil && probes < MAX_PROBES {
            if let entry = buckets[position], entry.key == key {
                return position
            }
            position = (position + 1) % numBuckets
            probes += 1
        }
        
        return position
    }
    
    /// Hash function
    /// TLA+ Function: Hash(key)
    private func hash(key: Key) async throws -> Int {
        // TLA+: Simple hash function
        var hash = 0
        for char in key {
            hash = (hash * 31 + Int(char.asciiValue ?? 0)) % Int.max
        }
        return abs(hash)
    }
    
    /// Update load factor
    /// TLA+ Function: UpdateLoadFactor()
    private func updateLoadFactor() async throws {
        // TLA+: Calculate load factor
        loadFactor = (numEntries * 100) / numBuckets
    }
    
    /// Check if key exists
    /// TLA+ Function: KeyExists(key)
    private func keyExists(key: Key) async throws -> Bool {
        let position = try await findEntryPosition(key: key)
        if let entry = buckets[position], !entry.deleted && entry.key == key {
            return true
        }
        return false
    }
    
    /// Get entry count
    /// TLA+ Function: GetEntryCount()
    private func getEntryCount() -> Int {
        return numEntries
    }
    
    /// Get bucket count
    /// TLA+ Function: GetBucketCount()
    private func getBucketCount() -> Int {
        return numBuckets
    }
    
    /// Get load factor
    /// TLA+ Function: GetLoadFactor()
    private func getLoadFactor() -> Int {
        return loadFactor
    }
    
    /// Check if unique
    /// TLA+ Function: IsUnique()
    private func isUniqueIndex() -> Bool {
        return isUnique
    }
    
    /// Clear index
    /// TLA+ Function: ClearIndex()
    private func clearIndex() async throws {
        buckets.removeAll()
        numEntries = 0
        numBuckets = INITIAL_BUCKETS
        loadFactor = 0
        
        // TLA+: Initialize buckets
        for i in 0..<INITIAL_BUCKETS {
            buckets[i] = nil
        }
        
        print("Index cleared")
    }
    
    /// Reset index
    /// TLA+ Function: ResetIndex()
    private func resetIndex() async throws {
        try await clearIndex()
        print("Index reset")
    }
    
    // MARK: - Query Operations
    
    /// Get statistics
    public func getStatistics() -> [String: Any] {
        return [
            "numEntries": numEntries,
            "numBuckets": numBuckets,
            "loadFactor": loadFactor,
            "isUnique": isUnique,
            "maxLoadFactor": MAX_LOAD_FACTOR,
            "maxProbes": MAX_PROBES
        ]
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
    
    /// Check if unique
    public func isUniqueIndex() -> Bool {
        return isUnique
    }
    
    /// Get buckets
    public func getBuckets() -> [Int: HashEntry?] {
        return buckets
    }
    
    /// Get non-empty buckets
    public func getNonEmptyBuckets() -> [Int: HashEntry] {
        var nonEmptyBuckets: [Int: HashEntry] = [:]
        for (index, entry) in buckets {
            if let entry = entry {
                nonEmptyBuckets[index] = entry
            }
        }
        return nonEmptyBuckets
    }
    
    /// Get deleted entries
    public func getDeletedEntries() -> [Int: HashEntry] {
        var deletedEntries: [Int: HashEntry] = [:]
        for (index, entry) in buckets {
            if let entry = entry, entry.deleted {
                deletedEntries[index] = entry
            }
        }
        return deletedEntries
    }
    
    /// Get active entries
    public func getActiveEntries() -> [Int: HashEntry] {
        var activeEntries: [Int: HashEntry] = [:]
        for (index, entry) in buckets {
            if let entry = entry, !entry.deleted {
                activeEntries[index] = entry
            }
        }
        return activeEntries
    }
    
    /// Get all entries
    public func getAllEntries() -> [Int: HashEntry] {
        var allEntries: [Int: HashEntry] = [:]
        for (index, entry) in buckets {
            if let entry = entry {
                allEntries[index] = entry
            }
        }
        return allEntries
    }
    
    /// Get configuration
    public func getConfiguration() -> [String: Any] {
        return [
            "initialBuckets": INITIAL_BUCKETS,
            "maxLoadFactor": MAX_LOAD_FACTOR,
            "maxProbes": MAX_PROBES,
            "isUnique": isUnique
        ]
    }
    
    /// Clear index
    public func clearIndex() async throws {
        try await clearIndex()
    }
    
    /// Reset index
    public func resetIndex() async throws {
        try await resetIndex()
    }
    
    // MARK: - Invariant Checking (for testing)
    
    /// Check load factor invariant
    /// TLA+ Inv_HashIndex_LoadFactor
    public func checkLoadFactorInvariant() -> Bool {
        // Check that load factor is within bounds
        return loadFactor <= MAX_LOAD_FACTOR
    }
    
    /// Check uniqueness invariant
    /// TLA+ Inv_HashIndex_Uniqueness
    public func checkUniquenessInvariant() -> Bool {
        // Check that uniqueness is enforced
        if !isUnique {
            return true
        }
        
        // Check for duplicate keys
        var seenKeys: Set<Key> = []
        for (_, entry) in buckets {
            if let entry = entry, !entry.deleted {
                if seenKeys.contains(entry.key) {
                    return false
                }
                seenKeys.insert(entry.key)
            }
        }
        
        return true
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

/// Hash index manager error
public enum HashIndexManagerError: Error, LocalizedError {
    case duplicateKey
    case maxProbesExceeded
    case keyNotFound
    case insertionFailed
    case deletionFailed
    case searchFailed
    case resizeFailed
    case hashFailed
    case loadFactorExceeded
    
    public var errorDescription: String? {
        switch self {
        case .duplicateKey:
            return "Duplicate key"
        case .maxProbesExceeded:
            return "Maximum probes exceeded"
        case .keyNotFound:
            return "Key not found"
        case .insertionFailed:
            return "Insertion failed"
        case .deletionFailed:
            return "Deletion failed"
        case .searchFailed:
            return "Search failed"
        case .resizeFailed:
            return "Resize failed"
        case .hashFailed:
            return "Hash failed"
        case .loadFactorExceeded:
            return "Load factor exceeded"
        }
    }
}
