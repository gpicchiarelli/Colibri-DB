//
//  LoadBalancer.swift
//  Based on: spec/LoadBalancer.tla
//

import Foundation

// MARK: - Types

/// Load balancing strategy
public enum LoadBalancingStrategy {
    case roundRobin
    case leastConnections
    case random
    case weighted
}

public struct BackendNode {
    public let id: String
    public let host: String
    public let port: Int
    public var weight: Int
    public var activeConnections: Int
    public var isHealthy: Bool
    
    public init(id: String, host: String, port: Int, weight: Int = 1) {
        self.id = id
        self.host = host
        self.port = port
        self.weight = weight
        self.activeConnections = 0
        self.isHealthy = true
    }
}

// MARK: - Load Balancer

/// Load balancer for distributing requests across backend nodes
public actor LoadBalancer {
    // MARK: - Properties
    
    private var nodes: [BackendNode]
    private let strategy: LoadBalancingStrategy
    private var currentIndex: Int = 0
    
    // MARK: - Initialization
    
    /// Initialize load balancer
    /// - Parameters:
    ///   - nodes: List of backend nodes
    ///   - strategy: Load balancing strategy to use
    public init(nodes: [BackendNode], strategy: LoadBalancingStrategy = .roundRobin) {
        self.nodes = nodes
        self.strategy = strategy
    }
    
    // MARK: - Public Methods
    
    /// Select a node based on the configured strategy
    /// - Returns: Selected backend node, or nil if no healthy nodes available
    public func selectNode() -> BackendNode? {
        let healthyNodes = nodes.filter { $0.isHealthy }
        
        guard !healthyNodes.isEmpty else {
            return nil
        }
        
        switch strategy {
        case .roundRobin:
            let node = healthyNodes[currentIndex % healthyNodes.count]
            currentIndex += 1
            return node
            
        case .leastConnections:
            return healthyNodes.min { $0.activeConnections < $1.activeConnections }
            
        case .random:
            return healthyNodes.randomElement()
            
        case .weighted:
            let totalWeight = healthyNodes.reduce(0) { $0 + $1.weight }
            var random = Int.random(in: 0..<totalWeight)
            
            for node in healthyNodes {
                random -= node.weight
                if random < 0 {
                    return node
                }
            }
            
            return healthyNodes.first
        }
    }
    
    /// Increment connection count for a node
    /// - Parameter nodeId: ID of the node
    public func incrementConnections(nodeId: String) {
        if let index = nodes.firstIndex(where: { $0.id == nodeId }) {
            nodes[index].activeConnections += 1
        }
    }
    
    /// Decrement connection count for a node
    /// - Parameter nodeId: ID of the node
    public func decrementConnections(nodeId: String) {
        if let index = nodes.firstIndex(where: { $0.id == nodeId }) {
            nodes[index].activeConnections = max(0, nodes[index].activeConnections - 1)
        }
    }
    
    /// Mark a node as unhealthy
    /// - Parameter nodeId: ID of the node
    public func markUnhealthy(nodeId: String) {
        if let index = nodes.firstIndex(where: { $0.id == nodeId }) {
            nodes[index].isHealthy = false
        }
    }
    
    /// Mark a node as healthy
    /// - Parameter nodeId: ID of the node
    public func markHealthy(nodeId: String) {
        if let index = nodes.firstIndex(where: { $0.id == nodeId }) {
            nodes[index].isHealthy = true
        }
    }
    
    /// Get all backend nodes
    /// - Returns: Array of all backend nodes
    public func getNodes() -> [BackendNode] {
        return nodes
    }
}

