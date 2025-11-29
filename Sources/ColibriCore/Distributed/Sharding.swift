//
//  Sharding.swift
//  Based on: spec/Sharding.tla
//

import Foundation

// MARK: - Types

/// Sharding strategy
public enum ShardingStrategy {
    case hash
    case range
    case consistent
}

public struct Shard {
    public let id: Int
    public let nodeID: String
    public let rangeStart: Value?
    public let rangeEnd: Value?
    
    public init(id: Int, nodeID: String, rangeStart: Value? = nil, rangeEnd: Value? = nil) {
        self.id = id
        self.nodeID = nodeID
        self.rangeStart = rangeStart
        self.rangeEnd = rangeEnd
    }
}

// MARK: - Shard Manager

/// Manager for database sharding
public actor ShardManager {
    // MARK: - Properties
    
    private let strategy: ShardingStrategy
    private var shards: [Shard] = []
    private let shardCount: Int
    
    // MARK: - Initialization
    
    /// Initialize shard manager
    /// - Parameters:
    ///   - strategy: Sharding strategy to use
    ///   - shardCount: Number of shards
    public init(strategy: ShardingStrategy, shardCount: Int) {
        self.strategy = strategy
        self.shardCount = shardCount
    }
    
    // MARK: - Public Methods
    
    /// Register a shard
    /// - Parameter shard: Shard to register
    public func registerShard(_ shard: Shard) {
        shards.append(shard)
    }
    
    /// Get shard for a given key
    /// - Parameter key: Key to find shard for
    /// - Returns: Shard that should handle this key, or nil if not found
    public func getShardForKey(_ key: Value) -> Shard? {
        switch strategy {
        case .hash:
            let hash = hashValue(key)
            let shardId = hash % shardCount
            return shards.first { $0.id == shardId }
            
        case .range:
            for shard in shards {
                if let start = shard.rangeStart, let end = shard.rangeEnd {
                    if key >= start && key < end {
                        return shard
                    }
                }
            }
            return shards.first
            
        case .consistent:
            return shards.first
        }
    }
    
    /// Rebalance shards across nodes
    public func rebalance() async {
        logInfo("Rebalancing shards...")
    }
    
    // MARK: - Private Methods
    
    /// Hash a value for shard distribution
    /// - Parameter value: Value to hash
    /// - Returns: Hash value
    private func hashValue(_ value: Value) -> Int {
        var hasher = Hasher()
        switch value {
        case .int(let v): hasher.combine(v)
        case .double(let v): hasher.combine(v)
        case .string(let v): hasher.combine(v)
        case .bool(let v): hasher.combine(v)
        case .date(let v): hasher.combine(v)
        case .null: hasher.combine(0)
        case .decimal(let v): hasher.combine(v)
        case .bytes(let v): hasher.combine(v)
        }
        return abs(hasher.finalize())
    }
}

