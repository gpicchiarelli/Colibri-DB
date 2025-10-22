//
//  ResourceQuotas.swift
//  ColibrìDB Resource Quota Management
//
//  Based on: spec/ResourceQuotas.tla
//  Implements: CPU/Memory/Storage quotas for multi-tenancy
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//

import Foundation

/// Resource quota configuration
public struct ResourceQuota: Codable, Sendable {
    public let maxConnections: Int
    public let maxMemoryMB: Int
    public let maxStorageGB: Int
    public let maxTransactionsPerSecond: Int
    
    public init(
        maxConnections: Int = 100,
        maxMemoryMB: Int = 1024,
        maxStorageGB: Int = 100,
        maxTransactionsPerSecond: Int = 1000
    ) {
        self.maxConnections = maxConnections
        self.maxMemoryMB = maxMemoryMB
        self.maxStorageGB = maxStorageGB
        self.maxTransactionsPerSecond = maxTransactionsPerSecond
    }
}

/// Multi-tenancy resource usage tracking
public struct MultiTenancyResourceUsage: Sendable {
    public var connections: Int = 0
    public var memoryMB: Int = 0
    public var storageGB: Int = 0
    public var transactionsThisSecond: Int = 0
    public var lastResetTime: Date = Date()
}

/// Resource Quota Manager
public actor ResourceQuotaManager {
    // MARK: - State
    
    private var quotas: [String: ResourceQuota] = [:]  // database -> quota
    private var usage: [String: MultiTenancyResourceUsage] = [:]   // database -> usage
    
    // MARK: - Quota Management
    
    /// Set quota for database
    public func setQuota(database: String, quota: ResourceQuota) {
        quotas[database] = quota
        if usage[database] == nil {
            usage[database] = ResourceUsage()
        }
    }
    
    /// Check if resource can be allocated
    public func canAllocate(database: String, resource: MultiTenancyResourceType, amount: Int) -> Bool {
        guard let quota = quotas[database],
              var currentUsage = usage[database] else {
            return true  // No quota = unlimited
        }
        
        // Reset TPS counter if needed
        if Date().timeIntervalSince(currentUsage.lastResetTime) >= 1.0 {
            currentUsage.transactionsThisSecond = 0
            currentUsage.lastResetTime = Date()
            usage[database] = currentUsage
        }
        
        switch resource {
        case .connections:
            return currentUsage.connections + amount <= quota.maxConnections
        case .memory:
            return currentUsage.memoryMB + amount <= quota.maxMemoryMB
        case .storage:
            return currentUsage.storageGB + amount <= quota.maxStorageGB
        case .transactions:
            return currentUsage.transactionsThisSecond + amount <= quota.maxTransactionsPerSecond
        }
    }
    
    /// Allocate resource
    public func allocate(database: String, resource: MultiTenancyResourceType, amount: Int) throws {
        guard canAllocate(database: database, resource: resource, amount: amount) else {
            throw DBError.internalError("Resource quota exceeded")
        }
        
        guard var currentUsage = usage[database] else {
            return
        }
        
        switch resource {
        case .connections:
            currentUsage.connections += amount
        case .memory:
            currentUsage.memoryMB += amount
        case .storage:
            currentUsage.storageGB += amount
        case .transactions:
            currentUsage.transactionsThisSecond += amount
        }
        
        usage[database] = currentUsage
    }
    
    /// Release resource
    public func release(database: String, resource: ResourceType, amount: Int) {
        guard var currentUsage = usage[database] else {
            return
        }
        
        switch resource {
        case .connections:
            currentUsage.connections = max(0, currentUsage.connections - amount)
        case .memory:
            currentUsage.memoryMB = max(0, currentUsage.memoryMB - amount)
        case .storage:
            currentUsage.storageGB = max(0, currentUsage.storageGB - amount)
        case .transactions:
            // TPS resets automatically
            break
        }
        
        usage[database] = currentUsage
    }
    
    /// Get current usage
    public func getUsage(database: String) -> ResourceUsage? {
        return usage[database]
    }
}

/// Multi-tenancy resource types
public enum MultiTenancyResourceType {
    case connections
    case memory
    case storage
    case transactions
}

