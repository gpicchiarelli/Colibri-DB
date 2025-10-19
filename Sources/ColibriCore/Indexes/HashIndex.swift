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
//  - O(1) average case lookup
//  - Open addressing with linear probing
//  - Dynamic resizing when load factor exceeds threshold
//  - Uniqueness enforcement
//

import Foundation

/// Hash Index with open addressing
/// Corresponds to TLA+ module: HashIndex.tla
public actor HashIndex {
    // MARK: - Configuration
    
    /// Initial bucket count
    private static let initialBuckets = 16
    
    /// Load factor threshold for resizing (75%)
    private static let loadFactorThreshold = 0.75
    
    // MARK: - State Variables
    
    /// Hash table buckets
    private var buckets: [HashBucket?]
    
    /// Number of entries
    private var count: Int = 0
    
    /// Unique index flag
    private let unique: Bool
    
    // MARK: - Initialization
    
    public init(unique: Bool = false) {
        self.buckets = Array(repeating: nil, count: Self.initialBuckets)
        self.unique = unique
    }
    
    // MARK: - Core Operations
    
    /// Insert key-RID pair
    /// TLA+ Action: Insert(key, rid)
    public func insert(key: Value, rid: RID) throws {
        // Check load factor and resize if needed
        if shouldResize() {
            try resize()
        }
        
        let hashValue = hash(key)
        var index = hashValue % buckets.count
        var probeCount = 0
        
        // Linear probing
        while probeCount < buckets.count {
            if let bucket = buckets[index] {
                // Bucket occupied
                if bucket.key == key {
                    if unique {
                        throw DBError.uniqueViolation
                    }
                    // Add to existing bucket
                    var updatedBucket = bucket
                    updatedBucket.rids.append(rid)
                    buckets[index] = updatedBucket
                    return
                }
                
                // Continue probing
                index = (index + 1) % buckets.count
                probeCount += 1
            } else {
                // Empty bucket - insert here
                buckets[index] = HashBucket(key: key, rids: [rid])
                count += 1
                return
            }
        }
        
        // Table full (should not happen with proper resizing)
        throw DBError.diskFull
    }
    
    /// Search for key
    /// TLA+ Action: Search(key)
    public func search(key: Value) -> [RID]? {
        let hashValue = hash(key)
        var index = hashValue % buckets.count
        var probeCount = 0
        
        // Linear probing
        while probeCount < buckets.count {
            if let bucket = buckets[index] {
                if bucket.key == key {
                    return bucket.rids
                }
                
                // Continue probing
                index = (index + 1) % buckets.count
                probeCount += 1
            } else {
                // Empty bucket - key not found
                return nil
            }
        }
        
        return nil
    }
    
    /// Delete key
    /// TLA+ Action: Delete(key)
    public func delete(key: Value) throws {
        let hashValue = hash(key)
        var index = hashValue % buckets.count
        var probeCount = 0
        
        // Linear probing
        while probeCount < buckets.count {
            if let bucket = buckets[index] {
                if bucket.key == key {
                    // Mark as deleted (tombstone)
                    buckets[index] = nil
                    count -= 1
                    
                    // Rehash subsequent entries to fix probe chains
                    try rehashFrom(index: (index + 1) % buckets.count)
                    return
                }
                
                // Continue probing
                index = (index + 1) % buckets.count
                probeCount += 1
            } else {
                // Empty bucket - key not found
                throw DBError.notFound
            }
        }
        
        throw DBError.notFound
    }
    
    // MARK: - Private Helpers
    
    /// Hash function
    private func hash(_ key: Value) -> Int {
        var hasher = Hasher()
        
        switch key {
        case .int(let value):
            hasher.combine(value)
        case .double(let value):
            hasher.combine(value)
        case .string(let value):
            hasher.combine(value)
        case .bool(let value):
            hasher.combine(value)
        case .date(let value):
            hasher.combine(value)
        case .null:
            hasher.combine(0)
        case .decimal(let value):
            hasher.combine(value)
        case .bytes(let value):
            hasher.combine(value)
        }
        
        return abs(hasher.finalize())
    }
    
    /// Check if resize is needed
    private func shouldResize() -> Bool {
        let loadFactor = Double(count) / Double(buckets.count)
        return loadFactor >= Self.loadFactorThreshold
    }
    
    /// Resize hash table
    /// TLA+ Action: Resize
    private func resize() throws {
        let oldBuckets = buckets
        let newSize = buckets.count * 2
        
        // Create new bucket array
        buckets = Array(repeating: nil, count: newSize)
        count = 0
        
        // Rehash all entries
        for bucket in oldBuckets {
            if let bucket = bucket {
                for rid in bucket.rids {
                    try insert(key: bucket.key, rid: rid)
                }
            }
        }
    }
    
    /// Rehash entries after deletion to fix probe chains
    private func rehashFrom(index: Int) throws {
        var currentIndex = index
        var probeCount = 0
        
        while probeCount < buckets.count {
            guard let bucket = buckets[currentIndex] else {
                // Empty slot - done rehashing
                return
            }
            
            // Remove and reinsert
            buckets[currentIndex] = nil
            count -= 1
            
            for rid in bucket.rids {
                try insert(key: bucket.key, rid: rid)
            }
            
            currentIndex = (currentIndex + 1) % buckets.count
            probeCount += 1
        }
    }
    
    // MARK: - Query Operations
    
    /// Get index statistics
    public func getStatistics() -> HashIndexStatistics {
        let loadFactor = Double(count) / Double(buckets.count)
        return HashIndexStatistics(
            bucketCount: buckets.count,
            entryCount: count,
            loadFactor: loadFactor,
            isUnique: unique
        )
    }
    
    // MARK: - Invariant Checking
    
    /// Check load factor invariant
    public func checkLoadFactorInvariant() -> Bool {
        let loadFactor = Double(count) / Double(buckets.count)
        return loadFactor <= 1.0  // Should never exceed 100%
    }
    
    /// Check uniqueness invariant
    public func checkUniquenessInvariant() -> Bool {
        if !unique {
            return true
        }
        
        var seenKeys: Set<String> = []
        
        for bucket in buckets {
            if let bucket = bucket {
                let keyString = "\(bucket.key)"
                if seenKeys.contains(keyString) {
                    return false
                }
                seenKeys.insert(keyString)
            }
        }
        
        return true
    }
}

// MARK: - Supporting Types

/// Hash bucket
private struct HashBucket {
    let key: Value
    var rids: [RID]
}

/// Hash index statistics
public struct HashIndexStatistics: Sendable {
    public let bucketCount: Int
    public let entryCount: Int
    public let loadFactor: Double
    public let isUnique: Bool
}

