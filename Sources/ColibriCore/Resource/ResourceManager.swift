//
//  ResourceManager.swift
//  ColibrìDB Resource Manager
//
//  Implements: Resource allocation and management
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//

import Foundation

// MARK: - Types

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

// MARK: - Protocol

/// Resource manager protocol
public protocol ResourceManager: Sendable {
    func allocate(_ type: ResourceType, amount: Int64) async throws
    func deallocate(_ type: ResourceType, amount: Int64) async
    func getAvailable(_ type: ResourceType) async -> Int64
    func getUsed(_ type: ResourceType) async -> Int64
}

// MARK: - Default Implementation

/// Default resource manager implementation
public actor DefaultResourceManager: ResourceManager {
    // MARK: - Properties
    
    private var allocations: [ResourceType: Int64] = [:]
    private var limits: [ResourceType: Int64] = [:]
    
    // MARK: - Initialization
    
    /// Initialize resource manager
    /// - Parameter limits: Resource limits dictionary
    public init(limits: [ResourceType: Int64] = [:]) {
        self.limits = limits
        // Initialize with default limits if not provided
        if limits.isEmpty {
            self.limits = [
                .memory: Int64(8 * 1024 * 1024 * 1024), // 8GB
                .disk: Int64(100 * 1024 * 1024 * 1024), // 100GB
                .cpu: Int64(100),
                .network: Int64(1000 * 1024 * 1024) // 1GB/s
            ]
        }
    }
    
    // MARK: - Protocol Implementation
    
    /// Allocate resources
    /// - Parameters:
    ///   - type: Resource type
    ///   - amount: Amount to allocate
    public func allocate(_ type: ResourceType, amount: Int64) async throws {
        let current = allocations[type] ?? 0
        let limit = limits[type] ?? Int64.max
        
        guard current + amount <= limit else {
            throw ResourceError.insufficientResources
        }
        
        allocations[type] = current + amount
    }
    
    /// Deallocate resources
    /// - Parameters:
    ///   - type: Resource type
    ///   - amount: Amount to deallocate
    public func deallocate(_ type: ResourceType, amount: Int64) async {
        let current = allocations[type] ?? 0
        allocations[type] = max(0, current - amount)
    }
    
    /// Get available resources
    /// - Parameter type: Resource type
    /// - Returns: Available amount
    public func getAvailable(_ type: ResourceType) async -> Int64 {
        let limit = limits[type] ?? Int64.max
        let used = allocations[type] ?? 0
        return max(0, limit - used)
    }
    
    /// Get used resources
    /// - Parameter type: Resource type
    /// - Returns: Used amount
    public func getUsed(_ type: ResourceType) async -> Int64 {
        return allocations[type] ?? 0
    }
}

// MARK: - Error Types

/// Resource-related errors
public enum ResourceError: Error, LocalizedError {
    case insufficientResources
    
    public var errorDescription: String? {
        switch self {
        case .insufficientResources:
            return "Insufficient resources available"
        }
    }
}

