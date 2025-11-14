//
//  ResourceManager.swift
//  ColibrìDB Resource Manager
//
//  Implements: Resource allocation and management
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//

import Foundation

/// Resource type
public enum ResourceType: String, Codable, Sendable {
    case memory
    case disk
    case cpu
    case network
}

/// Resource allocation
public struct ResourceAllocation: Codable, Sendable {
    public let type: ResourceType
    public let amount: Int64
    public let timestamp: Date
    
    public init(type: ResourceType, amount: Int64, timestamp: Date = Date()) {
        self.type = type
        self.amount = amount
        self.timestamp = timestamp
    }
}

/// Resource manager protocol
public protocol ResourceManager: Sendable {
    func allocate(_ type: ResourceType, amount: Int64) throws
    func deallocate(_ type: ResourceType, amount: Int64)
    func getAvailable(_ type: ResourceType) -> Int64
    func getUsed(_ type: ResourceType) -> Int64
}

/// Default resource manager implementation
public actor DefaultResourceManager: ResourceManager {
    private var allocations: [ResourceType: Int64] = [:]
    private var limits: [ResourceType: Int64] = [:]
    
    public init(limits: [ResourceType: Int64] = [:]) {
        self.limits = limits
        // Initialize with default limits if not provided
        if limits.isEmpty {
            self.limits = [
                .memory: 8 * 1024 * 1024 * 1024, // 8GB
                .disk: 100 * 1024 * 1024 * 1024, // 100GB
                .cpu: 100, // 100%
                .network: 1000 * 1024 * 1024 // 1GB/s
            ]
        }
    }
    
    public func allocate(_ type: ResourceType, amount: Int64) throws {
        let current = allocations[type] ?? 0
        let limit = limits[type] ?? Int64.max
        
        guard current + amount <= limit else {
            throw ResourceError.insufficientResources
        }
        
        allocations[type] = current + amount
    }
    
    public func deallocate(_ type: ResourceType, amount: Int64) {
        let current = allocations[type] ?? 0
        allocations[type] = max(0, current - amount)
    }
    
    public func getAvailable(_ type: ResourceType) -> Int64 {
        let limit = limits[type] ?? Int64.max
        let used = allocations[type] ?? 0
        return max(0, limit - used)
    }
    
    public func getUsed(_ type: ResourceType) -> Int64 {
        return allocations[type] ?? 0
    }
}

public enum ResourceError: Error, LocalizedError {
    case insufficientResources
    
    public var errorDescription: String? {
        switch self {
        case .insufficientResources:
            return "Insufficient resources available"
        }
    }
}

