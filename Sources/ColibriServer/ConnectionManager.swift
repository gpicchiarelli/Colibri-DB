//
//  ConnectionManager.swift
//  coldb-server
//
//  Created by Giacomo Picchiarelli on 2025-09-27.
//
// Theme: Connection management and pooling for the database server

import Foundation
import NIO
import ColibriCore

// MARK: - Connection Manager

public final class ConnectionManager: @unchecked Sendable {
    private let maxConnections: Int
    private let connectionTimeout: TimeInterval
    private let queryTimeout: TimeInterval
    private let database: Database
    
    private var activeConnections: Set<ConnectionID> = []
    private var connectionPool: [ConnectionID: DatabaseConnection] = [:]
    private let connectionQueue = DispatchQueue(label: "com.colibridb.connections", attributes: .concurrent)
    
    public init(
        maxConnections: Int = 1000,
        connectionTimeout: TimeInterval = 30.0,
        queryTimeout: TimeInterval = 60.0,
        database: Database
    ) {
        self.maxConnections = maxConnections
        self.connectionTimeout = connectionTimeout
        self.queryTimeout = queryTimeout
        self.database = database
    }
    
    public func createConnection(channel: Channel) -> ConnectionID {
        let connectionID = ConnectionID()
        
        connectionQueue.async(flags: .barrier) {
            guard self.activeConnections.count < self.maxConnections else {
                logWarning("Connection limit reached, rejecting new connection")
                return
            }
            
            let connection = DatabaseConnection(
                id: connectionID,
                channel: channel,
                database: self.database,
                timeout: self.queryTimeout
            )
            
            self.activeConnections.insert(connectionID)
            self.connectionPool[connectionID] = connection
            
            logInfo("New connection created: \(connectionID)")
        }
        
        return connectionID
    }
    
    public func getConnection(id: ConnectionID) -> DatabaseConnection? {
        return connectionQueue.sync {
            return connectionPool[id]
        }
    }
    
    public func closeConnection(id: ConnectionID) {
        connectionQueue.async(flags: .barrier) {
            if let connection = self.connectionPool[id] {
                connection.close()
                self.connectionPool.removeValue(forKey: id)
                self.activeConnections.remove(id)
                logInfo("Connection closed: \(id)")
            }
        }
    }
    
    public func closeAllConnections() {
        connectionQueue.async(flags: .barrier) {
            for connection in self.connectionPool.values {
                connection.close()
            }
            self.connectionPool.removeAll()
            self.activeConnections.removeAll()
            logInfo("All connections closed")
        }
    }
    
    public var connectionCount: Int {
        return connectionQueue.sync {
            return activeConnections.count
        }
    }
    
    public var availableConnections: Int {
        return maxConnections - connectionCount
    }
}

// MARK: - Connection ID

public struct ConnectionID: Hashable, CustomStringConvertible, Sendable {
    private let id: UUID
    
    public init() {
        self.id = UUID()
    }
    
    public var description: String {
        return id.uuidString.prefix(8).description
    }
}

// MARK: - Database Connection

public final class DatabaseConnection: @unchecked Sendable {
    public let id: ConnectionID
    private let channel: Channel
    private let database: Database
    private let queryTimeout: TimeInterval
    private var currentTransaction: UInt64?
    private let connectionQueue: DispatchQueue
    
    public init(id: ConnectionID, channel: Channel, database: Database, timeout: TimeInterval) {
        self.id = id
        self.channel = channel
        self.database = database
        self.queryTimeout = timeout
        self.connectionQueue = DispatchQueue(label: "com.colibridb.connection.\(id)", qos: .userInitiated)
    }
    
    public func executeQuery(_ sql: String) -> EventLoopFuture<SQLQueryResult> {
        let promise = channel.eventLoop.makePromise(of: SQLQueryResult.self)
        
        connectionQueue.async {
            do {
                let interface = SQLQueryInterface(database: self.database)
                let result = try interface.execute(sql)
                promise.succeed(result)
            } catch {
                promise.fail(error)
            }
        }
        
        return promise.futureResult
    }
    
    public func beginTransaction() -> EventLoopFuture<UInt64> {
        let promise = channel.eventLoop.makePromise(of: UInt64.self)
        
        connectionQueue.async {
            do {
                let tid = try self.database.begin(isolation: .readCommitted)
                self.currentTransaction = tid
                promise.succeed(tid)
            } catch {
                promise.fail(error)
            }
        }
        
        return promise.futureResult
    }
    
    public func commitTransaction() -> EventLoopFuture<Void> {
        let promise = channel.eventLoop.makePromise(of: Void.self)
        
        connectionQueue.async {
            do {
                if let tid = self.currentTransaction {
                    try self.database.commit(tid)
                    self.currentTransaction = nil
                }
                promise.succeed(())
            } catch {
                promise.fail(error)
            }
        }
        
        return promise.futureResult
    }
    
    public func rollbackTransaction() -> EventLoopFuture<Void> {
        let promise = channel.eventLoop.makePromise(of: Void.self)
        
        connectionQueue.async {
            do {
                if let tid = self.currentTransaction {
                    try self.database.rollback(toSavepoint: "", tid: tid)
                    self.currentTransaction = nil
                }
                promise.succeed(())
            } catch {
                promise.fail(error)
            }
        }
        
        return promise.futureResult
    }
    
    public func close() {
        connectionQueue.async {
            if let tid = self.currentTransaction {
                try? self.database.rollback(toSavepoint: "", tid: tid)
                self.currentTransaction = nil
            }
        }
    }
    
    public var isActive: Bool {
        return channel.isActive
    }
    
    public var hasActiveTransaction: Bool {
        return currentTransaction != nil
    }
}

// MARK: - Connection Statistics

public struct ConnectionStatistics {
    public let totalConnections: Int
    public let activeConnections: Int
    public let availableConnections: Int
    public let maxConnections: Int
    public let connectionsWithTransactions: Int
    
    public init(
        totalConnections: Int,
        activeConnections: Int,
        availableConnections: Int,
        maxConnections: Int,
        connectionsWithTransactions: Int
    ) {
        self.totalConnections = totalConnections
        self.activeConnections = activeConnections
        self.availableConnections = availableConnections
        self.maxConnections = maxConnections
        self.connectionsWithTransactions = connectionsWithTransactions
    }
}

// MARK: - Connection Manager Extensions

extension ConnectionManager {
    public func getStatistics() -> ConnectionStatistics {
        return connectionQueue.sync {
            let connectionsWithTransactions = connectionPool.values.filter { $0.hasActiveTransaction }.count
            
            return ConnectionStatistics(
                totalConnections: activeConnections.count,
                activeConnections: activeConnections.count,
                availableConnections: maxConnections - activeConnections.count,
                maxConnections: maxConnections,
                connectionsWithTransactions: connectionsWithTransactions
            )
        }
    }
    
    public func cleanupInactiveConnections() {
        connectionQueue.async(flags: .barrier) {
            let inactiveConnections = self.connectionPool.filter { !$0.value.isActive }
            
            for (id, _) in inactiveConnections {
                self.connectionPool.removeValue(forKey: id)
                self.activeConnections.remove(id)
                logInfo("Cleaned up inactive connection: \(id)")
            }
        }
    }
}
