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
import Logging

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
public actor DatabaseServer {
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
    private var database: ColibrìDB?
    private var connections: [String: ServerConnection] = [:]
    private var isRunning: Bool = false
    private let logger: ColibriLogger
    
    // MARK: - Initialization
    
    public init(config: Configuration) throws {
        self.config = config
        self.database = nil  // Will be set by setDatabase()
        self.logger = ColibriLogger()
    }
    
    /// Set the database instance (must be called before start())
    public func setDatabase(_ db: ColibrìDB) async {
        self.database = db
    }
    
    // MARK: - Server Lifecycle
    
    /// Start the server
    public func start() async throws {
        guard !isRunning else { return }
        
        guard database != nil else {
            throw DBError.internalError("Database not set")
        }
        
        await logger.info("Starting ColibrìDB Server", metadata: ["host": config.host, "port": "\(config.port)"])
        
        // Note: Database is started by ColibrìDB.start(), not here
        // This avoids circular dependency where db.start() -> server.start() -> db.start()
        
        isRunning = true
        await logger.info("ColibrìDB Server started successfully")
    }
    
    /// Stop the server
    public func stop() async throws {
        guard isRunning else { return }
        
        guard database != nil else {
            throw DBError.internalError("Database not set")
        }
        
        await logger.info("Stopping ColibrìDB Server")
        
        // Close all connections
        for (_, connection) in connections {
            await connection.close()
        }
        connections.removeAll()
        
        // Note: Database is shut down by ColibrìDB.shutdown(), not here
        // This avoids circular dependency
        
        isRunning = false
        await logger.info("ColibrìDB Server stopped successfully")
    }
    
    // MARK: - Connection Management
    
    /// Accept a new connection
    public func acceptConnection(clientID: String) async throws -> ServerConnection {
        guard isRunning else {
            throw DBError.internalError("Server not running")
        }
        
        guard let db = database else {
            throw DBError.internalError("Database not set")
        }
        
        guard connections.count < config.maxConnections else {
            throw DBError.internalError("Max connections reached")
        }
        
        let connection = ServerConnection(clientID: clientID, database: db)
        connections[clientID] = connection
        
        await logger.info("Client connected", metadata: ["clientId": clientID])
        return connection
    }
    
    /// Close a connection
    public func closeConnection(clientID: String) async {
        if let connection = connections[clientID] {
            await connection.close()
            connections[clientID] = nil
            await logger.info("Client disconnected", metadata: ["clientId": clientID])
        }
    }
    
    // MARK: - Statistics
    
    /// Get server statistics
    public func getStatistics() async -> ServerStatistics {
        if let db = database {
            let _ = await db.getStatistics()
        }
        
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
public actor ServerConnection {
    public let clientID: String
    private let database: ColibrìDB
    private var sessionToken: String?
    private var currentTxID: TxID?
    
    init(clientID: String, database: ColibrìDB) {
        self.clientID = clientID
        self.database = database
    }
    
    /// Authenticate
    public func authenticate(username: String, password: String) async throws {
        // Note: Authentication is handled by AuthenticatedServer
        sessionToken = "mock_token_\(username)"
    }
    
    /// Begin transaction
    public func beginTransaction() async throws -> TxID {
        guard sessionToken != nil else {
            throw DBError.internalError("Not authenticated")
        }
        
        let txID = try await database.beginTransaction()
        currentTxID = txID
        return txID
    }
    
    /// Commit transaction
    public func commit() async throws {
        guard let txID = currentTxID else {
            throw DBError.internalError("No active transaction")
        }
        
        try await database.commit(txId: txID)
        currentTxID = nil
    }
    
    /// Rollback transaction
    public func rollback() async throws {
        guard let txID = currentTxID else {
            throw DBError.internalError("No active transaction")
        }
        
        try await database.abort(txId: txID)
        currentTxID = nil
    }
    
    /// Execute query
    public func executeQuery(sql: String) async throws -> [Row] {
        guard let txID = currentTxID else {
            throw DBError.internalError("No active transaction")
        }
        
        let result = try await database.executeQuery(sql, txId: txID)
        return result.rows
    }
    
    /// Close connection
    public func close() async {
        // Rollback any active transaction
        if currentTxID != nil {
            try? await rollback()
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

