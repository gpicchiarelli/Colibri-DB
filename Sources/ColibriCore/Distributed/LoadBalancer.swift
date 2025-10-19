//
//  LoadBalancer.swift
//  Based on: spec/LoadBalancer.tla
//

import Foundation

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

public actor LoadBalancer {
    private var nodes: [BackendNode]
    private let strategy: LoadBalancingStrategy
    private var currentIndex: Int = 0
    
    public init(nodes: [BackendNode], strategy: LoadBalancingStrategy = .roundRobin) {
        self.nodes = nodes
        self.strategy = strategy
    }
    
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
    
    public func incrementConnections(nodeId: String) {
        if let index = nodes.firstIndex(where: { $0.id == nodeId }) {
            nodes[index].activeConnections += 1
        }
    }
    
    public func decrementConnections(nodeId: String) {
        if let index = nodes.firstIndex(where: { $0.id == nodeId }) {
            nodes[index].activeConnections = max(0, nodes[index].activeConnections - 1)
        }
    }
    
    public func markUnhealthy(nodeId: String) {
        if let index = nodes.firstIndex(where: { $0.id == nodeId }) {
            nodes[index].isHealthy = false
        }
    }
    
    public func markHealthy(nodeId: String) {
        if let index = nodes.firstIndex(where: { $0.id == nodeId }) {
            nodes[index].isHealthy = true
        }
    }
    
    public func getNodes() -> [BackendNode] {
        return nodes
    }
}

