//
//  ResourceManagerImpl.swift
//  ColibrìDB Resource Manager Implementation
//
//  Concrete implementation of ResourceManager protocol
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//

import Foundation

/// Concrete implementation of OptimizationResourceManager protocol
public actor OptimizationResourceManagerImpl: OptimizationResourceManager {
    private var allocations: [String: Double] = [:]
    private var limits: [String: Double] = [:]
    
    public init(limits: [String: Double] = [:]) {
        self.limits = limits
        if limits.isEmpty {
            // Default limits
            self.limits = [
                "memory": 8_000_000_000.0, // 8GB
                "cpu": 100.0, // 100%
                "disk": 100_000_000_000.0, // 100GB
                "network": 1_000_000_000.0 // 1GB/s
            ]
        }
    }
    
    public func allocateResource(resourceType: String, amount: Double) async throws {
        let current = allocations[resourceType] ?? 0.0
        let limit = limits[resourceType] ?? Double.infinity
        
        guard current + amount <= limit else {
            throw OptimizationResourceError.insufficientResources
        }
        
        allocations[resourceType] = current + amount
    }
    
    public func deallocateResource(resourceType: String, amount: Double) async throws {
        let current = allocations[resourceType] ?? 0.0
        allocations[resourceType] = max(0.0, current - amount)
    }
    
    public func getResourceUsage(resourceType: String) async throws -> Double {
        return allocations[resourceType] ?? 0.0
    }
}

public enum OptimizationResourceError: Error, LocalizedError {
    case insufficientResources
    
    public var errorDescription: String? {
        switch self {
        case .insufficientResources:
            return "Insufficient resources available"
        }
    }
}

