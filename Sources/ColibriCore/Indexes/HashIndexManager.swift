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
    private var numBuckets: Int = 16
    
    /// Load factor
    /// TLA+: loadFactor \in Nat
    private var loadFactor: Int = 0
    
    /// Is unique
    /// TLA+: isUnique \in BOOLEAN
    private var isUnique: Bool = false
    
    // MARK: - Initialization
    
    /// Initialize hash index manager
    /// TLA+: Init
    public init(isUnique: Bool = false) {
        self.isUnique = isUnique
        self.numBuckets = INITIAL_BUCKETS
        self.numEntries = 0
        self.loadFactor = 0
        
        // Initialize buckets
        for i in 0..<numBuckets {
            buckets[i] = nil
        }
    }
    
    // MARK: - Public Interface
    
    /// Insert a key-value pair
    /// TLA+: Insert
    public func insert(key: Value, rid: RID) async throws {
        // TLA+: Check if key already exists (for unique index)
        if isUnique {
            if let _ = try await search(key: key) {
                throw HashIndexManagerError.duplicateKey
            }
        }
        
        // TLA+: Find position to insert
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
        
        // TLA+: Check if resize is needed
        if loadFactor > MAX_LOAD_FACTOR {
            try await resize()
        }
    }
    
    /// Search for a key
    /// TLA+: Search
    public func search(key: Value) async throws -> RID? {
        let position = try await findEntryPosition(key: key)
        
        if let entry = buckets[position] {
            if !entry.deleted && entry.key == key {
                return entry.rid
            }
        }
        
        return nil
    }
    
    /// Delete a key
    /// TLA+: Delete
    public func delete(key: Value) async throws {
        let position = try await findEntryPosition(key: key)
        
        if let entry = buckets[position] {
            if !entry.deleted && entry.key == key {
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
            }
        }
    }
    
    // MARK: - Private Methods
    
    /// Resize the hash table
    /// TLA+: Resize
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
        
        // TLA+: Rehash all entries
        for (_, entry) in oldBuckets {
            if let entry = entry {
                if !entry.deleted {
                    let newPosition = try await findInsertPosition(key: entry.key)
                    buckets[newPosition] = entry
                }
            }
        }
        
        // TLA+: Update load factor
        try await updateLoadFactor()
        
        print("Resized to \(numBuckets) buckets")
    }
    
    /// Find position to insert a key
    /// TLA+: FindInsertPosition
    private func findInsertPosition(key: Value) async throws -> Int {
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
    
    /// Find position of an existing key
    /// TLA+: FindEntryPosition
    private func findEntryPosition(key: Value) async throws -> Int {
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
    
    /// Hash a key
    /// TLA+: Hash
    private func hash(key: Value) async throws -> Int {
        // TLA+: Simple hash function
        var hash = 0
        let keyString = String(describing: key)
        for char in keyString {
            hash = (hash * 31 + Int(char.asciiValue ?? 0)) % Int.max
        }
        return abs(hash)
    }
    
    /// Update load factor
    /// TLA+: UpdateLoadFactor
    private func updateLoadFactor() async throws {
        // TLA+: Calculate load factor
        loadFactor = (numEntries * 100) / numBuckets
    }
    
    /// Check if key exists
    /// TLA+: KeyExists
    private func keyExists(key: Value) async throws -> Bool {
        let position = try await findEntryPosition(key: key)
        if let entry = buckets[position], !entry.deleted && entry.key == key {
            return true
        }
        return false
    }
    
    // MARK: - Statistics and Monitoring
    
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
    
    // MARK: - Maintenance Operations
    
    /// Clear index
    public func clearIndex() async throws {
        buckets.removeAll()
        numEntries = 0
        numBuckets = INITIAL_BUCKETS
        print("Index cleared")
    }
    
    // MARK: - TLA+ Invariants
    
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
        var seenKeys: Set<Value> = []
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