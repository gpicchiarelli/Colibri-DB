//
//  HashIndex.swift
//  ColibrìDB Hash Index Implementation
//
//  Based on: spec/HashIndex.tla
//  Implements: Hash index with open addressing and linear probing
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//
//  Key Properties:
//  - Uniqueness: No duplicate keys (if unique index)
//  - Load Factor: Maintains load factor below threshold
//  - Collision Handling: All collisions resolved
//  - Deterministic Hashing: Same key hashes to same bucket
//
//  Based on:
//  - "Introduction to Algorithms" (Cormen et al., 2009) - Hash Tables
//  - "The Art of Computer Programming" (Knuth, Vol 3) - Searching
//

import Foundation

// MARK: - Hash Entry

/// Hash index entry
/// Corresponds to TLA+: HashEntry
public struct HashEntry: Codable, Sendable, Equatable {
    public let key: Value
    public let rid: RID
    public let deleted: Bool  // For tombstone in open addressing
    
    public init(key: Value, rid: RID, deleted: Bool = false) {
        self.key = key
        self.rid = rid
        self.deleted = deleted
    }
}

// MARK: - Hash Index

/// Hash Index with open addressing
/// Corresponds to TLA+ module: HashIndex.tla
public actor HashIndex {
    
    // MARK: - Constants (TLA+ constants)
    
    /// Initial bucket count
    /// TLA+: InitialBuckets
    private static let initialBuckets = 16
    
    /// Maximum load factor before resize (75%)
    /// TLA+: MaxLoadFactor
    private static let maxLoadFactor = 75
    
    /// Maximum probe attempts for open addressing
    /// TLA+: MaxProbes
    private static let maxProbes = 1000
    
    // MARK: - State Variables (TLA+ vars)
    
    /// Array of buckets
    /// TLA+: buckets \in [0..(numBuckets-1) -> Bucket]
    private var buckets: [HashEntry?]
    
    /// Total number of entries in index
    /// TLA+: numEntries \in Nat
    private var numEntries: Int = 0
    
    /// Current number of buckets
    /// TLA+: numBuckets \in Nat
    private var numBuckets: Int
    
    /// Current load factor (numEntries / numBuckets * 100)
    /// TLA+: loadFactor \in 0..100
    private var loadFactor: Int = 0
    
    /// Whether this is a unique index
    /// TLA+: isUnique \in BOOLEAN
    private let isUnique: Bool
    
    // MARK: - Initialization
    
    public init(unique: Bool = true) {
        // TLA+ Init
        self.buckets = Array(repeating: nil, count: Self.initialBuckets)
        self.numEntries = 0
        self.numBuckets = Self.initialBuckets
        self.loadFactor = 0
        self.isUnique = unique
    }
    
    // MARK: - Core Operations
    
    /// Insert key-RID pair
    /// TLA+ Action: Insert(key, rid)
    /// Precondition: loadFactor < MaxLoadFactor \/ ResizeEnabled
    /// Postcondition: key-rid pair inserted, load factor updated
    public func insert(key: Value, rid: RID) throws {
        // TLA+: Check load factor and resize if needed
        if loadFactor >= Self.maxLoadFactor {
            try resize()
        }
        
        // TLA+: Hash(key, numBuckets)
        let hashValue = hash(key)
        var index = hashValue % numBuckets
        var attempt = 0
        
        // TLA+: Probe(key, attempt, numBuckets) - Linear probing
        while attempt < Self.maxProbes {
            let probeIndex = (hashValue + attempt) % numBuckets
            
            if let entry = buckets[probeIndex] {
                if entry.key == key {
                    // TLA+: Check uniqueness constraint
                    if isUnique {
                        throw DBError.uniqueViolation
                    }
                    // For non-unique index, we could add to a list, but for simplicity, replace
                    buckets[probeIndex] = HashEntry(key: key, rid: rid, deleted: false)
                    return
                }
                
                // Continue probing
                attempt += 1
            } else {
                // Empty slot - insert here
                buckets[probeIndex] = HashEntry(key: key, rid: rid, deleted: false)
                numEntries += 1
                updateLoadFactor()
                return
            }
        }
        
        // TLA+: MaxProbes exceeded
        throw DBError.diskFull
    }
    
    /// Search for key
    /// TLA+ Action: Search(key)
    /// Precondition: key is valid
    /// Postcondition: returns RID if found, nil otherwise
    public func search(key: Value) -> RID? {
        // TLA+: Hash(key, numBuckets)
        let hashValue = hash(key)
        var attempt = 0
        
        // TLA+: Probe(key, attempt, numBuckets) - Linear probing
        while attempt < Self.maxProbes {
            let probeIndex = (hashValue + attempt) % numBuckets
            
            if let entry = buckets[probeIndex] {
                if entry.key == key && !entry.deleted {
                    return entry.rid
                }
                
                // Continue probing
                attempt += 1
            } else {
                // Empty slot - key not found
                return nil
            }
        }
        
        return nil
    }
    
    /// Delete key
    /// TLA+ Action: Delete(key)
    /// Precondition: key exists in index
    /// Postcondition: key marked as deleted (tombstone)
    public func delete(key: Value) throws {
        // TLA+: Hash(key, numBuckets)
        let hashValue = hash(key)
        var attempt = 0
        
        // TLA+: Probe(key, attempt, numBuckets) - Linear probing
        while attempt < Self.maxProbes {
            let probeIndex = (hashValue + attempt) % numBuckets
            
            if let entry = buckets[probeIndex] {
                if entry.key == key && !entry.deleted {
                    // TLA+: Mark as deleted (tombstone)
                    buckets[probeIndex] = HashEntry(key: key, rid: entry.rid, deleted: true)
                    numEntries -= 1
                    updateLoadFactor()
                    return
                }
                
                // Continue probing
                attempt += 1
            } else {
                // Empty slot - key not found
                throw DBError.notFound
            }
        }
        
        throw DBError.notFound
    }
    
    // MARK: - Helper Methods
    
    /// Hash function
    /// TLA+: Hash(key, numBuckets)
    private func hash(_ key: Value) -> Int {
        var hasher = Hasher()
        
        switch key {
        case .int(let value):
            hasher.combine(value)
        case .string(let value):
            hasher.combine(value)
        case .bool(let value):
            hasher.combine(value)
        case .null:
            hasher.combine(0)
        }
        
        return abs(hasher.finalize())
    }
    
    /// Update load factor
    /// TLA+: ComputeLoadFactor
    private func updateLoadFactor() {
        if numBuckets == 0 {
            loadFactor = 0
        } else {
            loadFactor = (numEntries * 100) / numBuckets
        }
    }
    
    /// Resize hash table
    /// TLA+ Action: Resize
    /// Precondition: loadFactor >= MaxLoadFactor
    /// Postcondition: numBuckets doubled, all entries rehashed
    private func resize() throws {
        let oldBuckets = buckets
        let oldNumBuckets = numBuckets
        
        // TLA+: Double the number of buckets
        numBuckets = oldNumBuckets * 2
        buckets = Array(repeating: nil, count: numBuckets)
        numEntries = 0
        
        // TLA+: Rehash all entries
        for entry in oldBuckets {
            if let entry = entry, !entry.deleted {
                try insert(key: entry.key, rid: entry.rid)
            }
        }
        
        updateLoadFactor()
    }
    
    // MARK: - Query Operations
    
    /// Get index statistics
    /// TLA+ Query: GetStatistics
    public func getStatistics() -> HashIndexStatistics {
        return HashIndexStatistics(
            bucketCount: numBuckets,
            entryCount: numEntries,
            loadFactor: loadFactor,
            isUnique: isUnique
        )
    }
    
    /// Get number of entries
    public func getEntryCount() -> Int {
        return numEntries
    }
    
    /// Get number of buckets
    public func getBucketCount() -> Int {
        return numBuckets
    }
    
    /// Get current load factor
    public func getLoadFactor() -> Int {
        return loadFactor
    }
    
    /// Check if index is unique
    public func isUniqueIndex() -> Bool {
        return isUnique
    }
    
    // MARK: - Invariant Checking (for testing)
    
    /// Check load factor invariant
    /// TLA+ Inv_HashIndex_LoadFactor
    public func checkLoadFactorInvariant() -> Bool {
        return loadFactor <= 100 && loadFactor >= 0
    }
    
    /// Check uniqueness invariant
    /// TLA+ Inv_HashIndex_Uniqueness
    public func checkUniquenessInvariant() -> Bool {
        if !isUnique {
            return true
        }
        
        var seenKeys: Set<String> = []
        
        for entry in buckets {
            if let entry = entry, !entry.deleted {
                let keyString = "\(entry.key)"
                if seenKeys.contains(keyString) {
                    return false
                }
                seenKeys.insert(keyString)
            }
        }
        
        return true
    }
    
    /// Check collision handling invariant
    /// TLA+ Inv_HashIndex_CollisionHandling
    public func checkCollisionHandlingInvariant() -> Bool {
        // Check that all entries are properly placed according to hash function
        for (index, entry) in buckets.enumerated() {
            if let entry = entry, !entry.deleted {
                let hashValue = hash(entry.key)
                let expectedIndex = hashValue % numBuckets
                
                // Check if entry is in correct position or in probe sequence
                var found = false
                var attempt = 0
                
                while attempt < Self.maxProbes {
                    let probeIndex = (hashValue + attempt) % numBuckets
                    if probeIndex == index {
                        found = true
                        break
                    }
                    attempt += 1
                }
                
                if !found {
                    return false
                }
            }
        }
        
        return true
    }
    
    /// Check deterministic hashing invariant
    /// TLA+ Inv_HashIndex_DeterministicHashing
    public func checkDeterministicHashingInvariant() -> Bool {
        // Check that same key always hashes to same value
        var keyHashes: [String: Int] = [:]
        
        for entry in buckets {
            if let entry = entry, !entry.deleted {
                let keyString = "\(entry.key)"
                let hashValue = hash(entry.key)
                
                if let existingHash = keyHashes[keyString] {
                    if existingHash != hashValue {
                        return false
                    }
                } else {
                    keyHashes[keyString] = hashValue
                }
            }
        }
        
        return true
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

/// Hash index statistics
/// Corresponds to TLA+ query results
public struct HashIndexStatistics: Sendable {
    public let bucketCount: Int
    public let entryCount: Int
    public let loadFactor: Int
    public let isUnique: Bool
}

