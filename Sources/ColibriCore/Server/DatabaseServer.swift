//
//  DatabaseServer.swift
//  ColibrìDB Database Server
//
//  Based on: spec/Server.tla
//  Implements: Database server with connection management
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//

import Foundation

/// Database configuration
public struct DatabaseConfiguration: Codable, Sendable {
    public let maxConnections: Int
    public let cacheSize: Int64
    public let walBufferSize: Int
    
    public init(maxConnections: Int = 100, cacheSize: Int64 = 1024*1024*1024, walBufferSize: Int = 8192) {
        self.maxConnections = maxConnections
        self.cacheSize = cacheSize
        self.walBufferSize = walBufferSize
    }
}

/// Database Server
/// Corresponds to TLA+ module: Server.tla
public final class DatabaseServer: @unchecked Sendable {
    // MARK: - Configuration
    
    public struct Configuration: Sendable {
        public let host: String
        public let port: Int
        public let maxConnections: Int
        public let databaseConfig: DatabaseConfiguration
        
        public init(
            host: String = "127.0.0.1",
            port: Int = 5432,
            maxConnections: Int = 100,
            databaseConfig: DatabaseConfiguration
        ) {
            self.host = host
            self.port = port
            self.maxConnections = maxConnections
            self.databaseConfig = databaseConfig
        }
    }
    
    // MARK: - State
    
    private let config: Configuration
    private let database: ColibrìDB
    private var connections: [String: ServerConnection] = [:]
    private var isRunning: Bool = false
    private let lock = NSLock()
    
    // MARK: - Initialization
    
    public init(config: Configuration) throws {
        self.config = config
        self.database = try ColibrìDB(config: ColibrìDBConfiguration(
            dataDirectory: URL(fileURLWithPath: "/tmp/colibridb_data")
        ))
    }
    
    // MARK: - Server Lifecycle
    
    /// Start the server
    public func start() throws {
        guard !isRunning else { return }
        
        print("Starting ColibrìDB Server on \(config.host):\(config.port)...")
        
        // Start database
        try database.start()
        
        isRunning = true
        print("ColibrìDB Server started successfully")
    }
    
    /// Stop the server
    public func stop() throws {
        guard isRunning else { return }
        
        print("Stopping ColibrìDB Server...")
        
        // Close all connections
        for (_, connection) in connections {
            connection.close()
        }
        connections.removeAll()
        
        // Shutdown database
        try database.shutdown()
        
        isRunning = false
        print("ColibrìDB Server stopped successfully")
    }
    
    // MARK: - Connection Management
    
    /// Accept a new connection
    public func acceptConnection(clientID: String) throws -> ServerConnection {
        guard isRunning else {
            throw DBError.internalError("Server not running")
        }
        
        guard connections.count < config.maxConnections else {
            throw DBError.internalError("Max connections reached")
        }
        
        let connection = ServerConnection(clientID: clientID, database: database)
        connections[clientID] = connection
        
        print("Client \(clientID) connected")
        return connection
    }
    
    /// Close a connection
    public func closeConnection(clientID: String) {
        if let connection = connections[clientID] {
            connection.close()
            connections[clientID] = nil
            print("Client \(clientID) disconnected")
        }
    }
    
    // MARK: - Statistics
    
    /// Get server statistics
    public func getStatistics() -> ServerStatistics {
        let _ = database.getStatistics()
        
        return ServerStatistics(
            isRunning: isRunning,
            activeConnections: connections.count,
            maxConnections: config.maxConnections,
            databaseStatistics: ["status": "running"]
        )
    }
}

// MARK: - Server Connection

/// Represents a client connection to the server
public final class ServerConnection: @unchecked Sendable {
    public let clientID: String
    private let database: ColibrìDB
    private var sessionToken: String?
    private var currentTxID: TxID?
    private let lock = NSLock()
    
    init(clientID: String, database: ColibrìDB) {
        self.clientID = clientID
        self.database = database
    }
    
    /// Authenticate
    public func authenticate(username: String, password: String) throws {
        lock.lock()
        defer { lock.unlock() }
        
        // Note: Authentication is handled by AuthenticatedServer
        sessionToken = "mock_token_\(username)"
    }
    
    /// Begin transaction
    public func beginTransaction() throws -> TxID {
        lock.lock()
        defer { lock.unlock() }
        
        guard sessionToken != nil else {
            throw DBError.internalError("Not authenticated")
        }
        
        let txID = try database.beginTransaction()
        currentTxID = txID
        return txID
    }
    
    /// Commit transaction
    public func commit() throws {
        lock.lock()
        defer { lock.unlock() }
        
        guard let txID = currentTxID else {
            throw DBError.internalError("No active transaction")
        }
        
        try database.commit(txId: txID)
        currentTxID = nil
    }
    
    /// Rollback transaction
    public func rollback() throws {
        lock.lock()
        defer { lock.unlock() }
        
        guard let txID = currentTxID else {
            throw DBError.internalError("No active transaction")
        }
        
        try database.abort(txId: txID)
        currentTxID = nil
    }
    
    /// Execute query
    public func executeQuery(sql: String) throws -> [Row] {
        lock.lock()
        defer { lock.unlock() }
        
        guard let txID = currentTxID else {
            throw DBError.internalError("No active transaction")
        }
        
        let result = try database.executeQuery(sql, txId: txID)
        return result.rows
    }
    
    /// Close connection
    public func close() {
        lock.lock()
        defer { lock.unlock() }
        
        // Rollback any active transaction
        if currentTxID != nil {
            try? rollback()
        }
    }
}

// MARK: - Supporting Types

/// Server statistics
public struct ServerStatistics: Sendable {
    public let isRunning: Bool
    public let activeConnections: Int
    public let maxConnections: Int
    public let databaseStatistics: [String: String]
}

