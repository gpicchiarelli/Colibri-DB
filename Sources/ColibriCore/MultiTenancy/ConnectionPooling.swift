//
//  ConnectionPooling.swift
//  Based on: spec/ConnectionPooling.tla
//

import Foundation

public struct PooledConnection: Sendable {
    public let id: UUID
    public let createdAt: Date
    public var lastUsed: Date
    public var inUse: Bool
    
    public init(id: UUID = UUID()) {
        self.id = id
        self.createdAt = Date()
        self.lastUsed = Date()
        self.inUse = false
    }
}

public actor ConnectionPool {
    private let minConnections: Int
    private let maxConnections: Int
    private let idleTimeout: TimeInterval
    
    private var connections: [PooledConnection] = []
    private var waitQueue: [CheckedContinuation<PooledConnection, Error>] = []
    
    public init(minConnections: Int = 5, maxConnections: Int = 100, idleTimeout: TimeInterval = 300) {
        self.minConnections = minConnections
        self.maxConnections = maxConnections
        self.idleTimeout = idleTimeout
    }
    
    public func initialize() async {
        for _ in 0..<minConnections {
            connections.append(PooledConnection())
        }
    }
    
    public func acquire() async throws -> PooledConnection {
        if let index = connections.firstIndex(where: { !$0.inUse }) {
            connections[index].inUse = true
            connections[index].lastUsed = Date()
            return connections[index]
        }
        
        if connections.count < maxConnections {
            var conn = PooledConnection()
            conn.inUse = true
            connections.append(conn)
            return conn
        }
        
        return try await withCheckedThrowingContinuation { continuation in
            waitQueue.append(continuation)
        }
    }
    
    public func release(_ connection: PooledConnection) {
        if let index = connections.firstIndex(where: { $0.id == connection.id }) {
            connections[index].inUse = false
            connections[index].lastUsed = Date()
            
            if !waitQueue.isEmpty {
                let waiter = waitQueue.removeFirst()
                connections[index].inUse = true
                waiter.resume(returning: connections[index])
            }
        }
    }
    
    public func evictIdle() {
        let now = Date()
        
        connections.removeAll { conn in
            !conn.inUse &&
            now.timeIntervalSince(conn.lastUsed) > idleTimeout &&
            connections.count > minConnections
        }
    }
    
    public func getStatistics() -> ConnectionPoolStatistics {
        return ConnectionPoolStatistics(
            totalConnections: connections.count,
            activeConnections: connections.filter { $0.inUse }.count,
            idleConnections: connections.filter { !$0.inUse }.count,
            waitingRequests: waitQueue.count
        )
    }
}

public struct ConnectionPoolStatistics {
    public let totalConnections: Int
    public let activeConnections: Int
    public let idleConnections: Int
    public let waitingRequests: Int
}

