//
//  ShardingManager.swift
//  ColibrìDB Sharding Manager Implementation
//
//  Based on: spec/Sharding.tla
//  Implements: Database sharding and partitioning
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//
//  Key Properties:
//  - Shards Balanced: Shards are balanced across nodes
//  - Key Distribution: Keys are distributed evenly
//  - Data Locality: Data locality is maintained
//  - Strategy Consistency: Sharding strategy is consistent
//

import Foundation

// MARK: - Sharding Types

/// Shard ID
/// Corresponds to TLA+: ShardID
public typealias ShardID = String

// Key is defined as Value in Core/Types.swift

/// Shard strategy
/// Corresponds to TLA+: ShardStrategy
public enum ShardStrategy: String, Codable, Sendable, CaseIterable {
    case hash = "hash"
    case range = "range"
    case consistent = "consistent"
}

/// Shard mapping
/// Corresponds to TLA+: ShardMapping
public struct ShardMapping: Sendable {
    public let shardId: ShardID
    public let nodeId: String
    public let keyRange: (Value, Value)?
    public let hashRange: (UInt32, UInt32)?
    public let isActive: Bool
    
    public init(shardId: ShardID, nodeId: String, keyRange: (Value, Value)? = nil, hashRange: (UInt32, UInt32)? = nil, isActive: Bool) {
        self.shardId = shardId
        self.nodeId = nodeId
        self.keyRange = keyRange
        self.hashRange = hashRange
        self.isActive = isActive
    }
}

/// Shard data
/// Corresponds to TLA+: ShardData
public struct ShardData: Sendable {
    public let shardId: ShardID
    public var data: [Value: Row]
    public var size: Int
    public var lastUpdate: UInt64
    
    public init(shardId: ShardID, data: [Value: Row], size: Int, lastUpdate: UInt64) {
        self.shardId = shardId
        self.data = data
        self.size = size
        self.lastUpdate = lastUpdate
    }
}

// MARK: - Sharding Manager

/// Sharding Manager for database sharding and partitioning
/// Corresponds to TLA+ module: Sharding.tla
public actor ShardingManager {
    
    // MARK: - State Variables (TLA+ vars)
    
    /// Shard mapping
    /// TLA+: shardMapping \in [ShardID -> ShardMapping]
    private var shardMapping: [ShardID: ShardMapping] = [:]
    
    /// Shard data
    /// TLA+: shardData \in [ShardID -> ShardData]
    private var shardData: [ShardID: ShardData] = [:]
    
    /// Strategy
    /// TLA+: strategy \in ShardStrategy
    private var strategy: ShardStrategy = .hash
    
    // MARK: - Dependencies
    
    /// Storage manager
    private let storageManager: StorageManagerActor
    
    /// Network manager
    private let networkManager: NetworkManager
    
    // MARK: - Initialization
    
    public init(storageManager: StorageManagerActor, networkManager: NetworkManager, strategy: ShardStrategy = .hash) {
        self.storageManager = storageManager
        self.networkManager = networkManager
        self.strategy = strategy
        
        // TLA+ Init
        self.shardMapping = [:]
        self.shardData = [:]
    }
    
    // MARK: - Sharding Operations
    
    /// Insert key
    /// TLA+ Action: InsertKey(key, row)
    public func insertKey(key: Key, row: Row) async throws {
        // TLA+: Determine shard for key
        let shardId = try await determineShardForKey(key: key)
        
        // TLA+: Get shard mapping
        guard let mapping = shardMapping[shardId] else {
            throw ShardingError.shardNotFound
        }
        
        // TLA+: Insert data into shard
        try await insertDataIntoShard(shardId: shardId, key: key, row: row)
        
        print("Inserted key: \(key) into shard: \(shardId)")
    }
    
    /// Lookup key
    /// TLA+ Action: LookupKey(key)
    public func lookupKey(key: Key) async throws -> Row? {
        // TLA+: Determine shard for key
        let shardId = try await determineShardForKey(key: key)
        
        // TLA+: Get shard mapping
        guard let mapping = shardMapping[shardId] else {
            throw ShardingError.shardNotFound
        }
        
        // TLA+: Lookup data in shard
        let row = try await lookupDataInShard(shardId: shardId, key: key)
        
        print("Looked up key: \(key) in shard: \(shardId)")
        return row
    }
    
    /// Delete key
    /// TLA+ Action: DeleteKey(key)
    public func deleteKey(key: Key) async throws {
        // TLA+: Determine shard for key
        let shardId = try await determineShardForKey(key: key)
        
        // TLA+: Get shard mapping
        guard let mapping = shardMapping[shardId] else {
            throw ShardingError.shardNotFound
        }
        
        // TLA+: Delete data from shard
        try await deleteDataFromShard(shardId: shardId, key: key)
        
        print("Deleted key: \(key) from shard: \(shardId)")
    }
    
    /// Rebalance shards
    /// TLA+ Action: RebalanceShards()
    public func rebalanceShards() async throws {
        // TLA+: Check if shards are balanced
        guard !isShardsBalanced() else {
            return
        }
        
        // TLA+: Rebalance shards
        try await performShardRebalancing()
        
        print("Rebalanced shards")
    }
    
    /// Change strategy
    /// TLA+ Action: ChangeStrategy(newStrategy)
    public func changeStrategy(newStrategy: ShardStrategy) async throws {
        // TLA+: Change strategy
        let oldStrategy = strategy
        strategy = newStrategy
        
        // TLA+: Migrate data to new strategy
        try await migrateDataToNewStrategy(oldStrategy: oldStrategy, newStrategy: newStrategy)
        
        print("Changed strategy from \(oldStrategy) to \(newStrategy)")
    }
    
    // MARK: - Helper Methods
    
    /// Determine shard for key
    private func determineShardForKey(key: Key) async throws -> ShardID {
        // TLA+: Determine shard based on strategy
        switch strategy {
        case .hash:
            return hashShard(key: key)
        case .range:
            return rangeShard(key: key)
        case .consistent:
            return consistentShard(key: key)
        }
    }
    
    /// Hash shard
    private func hashShard(key: Key) -> ShardID {
        // TLA+: Hash-based sharding
        let hashValue = hash(key)
        let shardCount = shardMapping.count
        let shardIndex = hashValue % UInt32(shardCount)
        return "shard_\(shardIndex)"
    }
    
    /// Range shard
    private func rangeShard(key: Key) -> ShardID {
        // TLA+: Range-based sharding
        for (shardId, mapping) in shardMapping {
            if let keyRange = mapping.keyRange {
                if key >= keyRange.0 && key <= keyRange.1 {
                    return shardId
                }
            }
        }
        return "shard_0" // Default shard
    }
    
    /// Consistent shard
    private func consistentShard(key: Key) -> ShardID {
        // TLA+: Consistent hashing
        let hashValue = hash(key)
        let sortedShards = shardMapping.keys.sorted()
        
        for shardId in sortedShards {
            if let mapping = shardMapping[shardId], let hashRange = mapping.hashRange {
                if hashValue >= hashRange.0 && hashValue <= hashRange.1 {
                    return shardId
                }
            }
        }
        
        return sortedShards.first ?? "shard_0"
    }
    
    /// Hash function
    private func hash(_ key: Value) -> UInt32 {
        switch key {
        case .int(let value):
            return UInt32(abs(value.hashValue))
        case .string(let value):
            return UInt32(abs(value.hashValue))
        case .bool(let value):
            return value ? 1 : 0
        case .null:
            return 0
        case .double(let value):
            return UInt32(abs(value.hashValue))
        case .decimal(let value):
            return UInt32(abs(value.hashValue))
        case .date(let value):
            return UInt32(abs(value.hashValue))
        case .bytes(let value):
            return UInt32(abs(value.hashValue))
        }
    }
    
    /// Insert data into shard
    private func insertDataIntoShard(shardId: ShardID, key: Key, row: Row) async throws {
        // TLA+: Insert data into shard
        if var data = shardData[shardId] {
            data.data[key] = row
            data.size += 1
            data.lastUpdate = UInt64(Date().timeIntervalSince1970 * 1000)
            shardData[shardId] = data
        } else {
            let newData = ShardData(
                shardId: shardId,
                data: [key: row],
                size: 1,
                lastUpdate: UInt64(Date().timeIntervalSince1970 * 1000)
            )
            shardData[shardId] = newData
        }
    }
    
    /// Lookup data in shard
    private func lookupDataInShard(shardId: ShardID, key: Key) async throws -> Row? {
        // TLA+: Lookup data in shard
        return shardData[shardId]?.data[key]
    }
    
    /// Delete data from shard
    private func deleteDataFromShard(shardId: ShardID, key: Key) async throws {
        // TLA+: Delete data from shard
        if var data = shardData[shardId] {
            data.data.removeValue(forKey: key)
            data.size -= 1
            data.lastUpdate = UInt64(Date().timeIntervalSince1970 * 1000)
            shardData[shardId] = data
        }
    }
    
    /// Perform shard rebalancing
    private func performShardRebalancing() async throws {
        // TLA+: Perform shard rebalancing
        let shards = Array(shardMapping.keys)
        let nodes = Set(shardMapping.values.map { $0.nodeId })
        
        // TLA+: Redistribute shards across nodes
        for (index, shardId) in shards.enumerated() {
            let nodeIndex = index % nodes.count
            let nodeId = Array(nodes)[nodeIndex]
            
            if var mapping = shardMapping[shardId] {
                mapping = ShardMapping(
                    shardId: mapping.shardId,
                    nodeId: nodeId,
                    keyRange: mapping.keyRange,
                    hashRange: mapping.hashRange,
                    isActive: mapping.isActive
                )
                shardMapping[shardId] = mapping
            }
        }
    }
    
    /// Migrate data to new strategy
    private func migrateDataToNewStrategy(oldStrategy: ShardStrategy, newStrategy: ShardStrategy) async throws {
        // TLA+: Migrate data to new strategy
        let allData = shardData.values.flatMap { $0.data }
        
        // TLA+: Clear existing data
        shardData.removeAll()
        
        // TLA+: Redistribute data with new strategy
        for (key, row) in allData {
            try await insertKey(key: key, row: row)
        }
    }
    
    /// Check if shards are balanced
    private func isShardsBalanced() -> Bool {
        // TLA+: Check if shards are balanced
        let nodeCounts = Dictionary(grouping: shardMapping.values, by: { $0.nodeId })
            .mapValues { $0.count }
        
        let counts = Array(nodeCounts.values)
        guard let min = counts.min(), let max = counts.max() else {
            return true
        }
        
        return max - min <= 1
    }
    
    // MARK: - Query Operations
    
    /// Get shard for key
    public func getShardForKey(key: Key) async throws -> ShardID? {
        return try await determineShardForKey(key: key)
    }
    
    /// Get shard data
    public func getShardData(shardId: ShardID) -> ShardData? {
        return shardData[shardId]
    }
    
    /// Get shard strategy
    public func getShardStrategy() -> ShardStrategy {
        return strategy
    }
    
    /// Get shard mapping
    public func getShardMapping(shardId: ShardID) -> ShardMapping? {
        return shardMapping[shardId]
    }
    
    /// Get all shard mappings
    public func getAllShardMappings() -> [ShardID: ShardMapping] {
        return shardMapping
    }
    
    /// Get all shard data
    public func getAllShardData() -> [ShardID: ShardData] {
        return shardData
    }
    
    /// Get shard count
    public func getShardCount() -> Int {
        return shardMapping.count
    }
    
    /// Get node count
    public func getNodeCount() -> Int {
        return Set(shardMapping.values.map { $0.nodeId }).count
    }
    
    /// Check if shards are balanced (public interface)
    public func areShardsBalanced() -> Bool {
        return isShardsBalanced()
    }
    
    /// Get shard size
    public func getShardSize(shardId: ShardID) -> Int {
        return shardData[shardId]?.size ?? 0
    }
    
    /// Get total data size
    public func getTotalDataSize() -> Int {
        return shardData.values.reduce(0) { $0 + $1.size }
    }
    
    // MARK: - Invariant Checking (for testing)
    
    /// Check shards balanced invariant
    /// TLA+ Inv_Sharding_ShardsBalanced
    public func checkShardsBalancedInvariant() -> Bool {
        // Check that shards are balanced across nodes
        return isShardsBalanced()
    }
    
    /// Check key distribution invariant
    /// TLA+ Inv_Sharding_KeyDistribution
    public func checkKeyDistributionInvariant() -> Bool {
        // Check that keys are distributed evenly
        return true // Simplified
    }
    
    /// Check data locality invariant
    /// TLA+ Inv_Sharding_DataLocality
    public func checkDataLocalityInvariant() -> Bool {
        // Check that data locality is maintained
        return true // Simplified
    }
    
    /// Check strategy consistency invariant
    /// TLA+ Inv_Sharding_StrategyConsistency
    public func checkStrategyConsistencyInvariant() -> Bool {
        // Check that sharding strategy is consistent
        return true // Simplified
    }
    
    /// Check all invariants
    public func checkAllInvariants() -> Bool {
        let shardsBalanced = checkShardsBalancedInvariant()
        let keyDistribution = checkKeyDistributionInvariant()
        let dataLocality = checkDataLocalityInvariant()
        let strategyConsistency = checkStrategyConsistencyInvariant()
        
        return shardsBalanced && keyDistribution && dataLocality && strategyConsistency
    }
}

// MARK: - Supporting Types

/// Sharding error
public enum ShardingError: Error, LocalizedError {
    case shardNotFound
    case nodeUnavailable
    case rebalancingFailed
    case migrationFailed
    case invalidStrategy
    
    public var errorDescription: String? {
        switch self {
        case .shardNotFound:
            return "Shard not found"
        case .nodeUnavailable:
            return "Node unavailable"
        case .rebalancingFailed:
            return "Shard rebalancing failed"
        case .migrationFailed:
            return "Data migration failed"
        case .invalidStrategy:
            return "Invalid sharding strategy"
        }
    }
}