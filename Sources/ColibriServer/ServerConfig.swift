//
//  ServerConfig.swift
//  ColibriServer
//
//  Server configuration structure
//
// ColibrDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

import Foundation
import ColibriCore

/// Server configuration
public struct ServerConfig: Codable {
    public var host: String
    public var port: Int
    public var maxConnections: Int
    public var connectionTimeout: TimeInterval
    public var queryTimeout: TimeInterval
    public var database: DatabaseConfig
    
    public init(
        host: String = "0.0.0.0",
        port: Int = 5432,
        maxConnections: Int = 100,
        connectionTimeout: TimeInterval = 30.0,
        queryTimeout: TimeInterval = 60.0,
        database: DatabaseConfig = DatabaseConfig()
    ) {
        self.host = host
        self.port = port
        self.maxConnections = maxConnections
        self.connectionTimeout = connectionTimeout
        self.queryTimeout = queryTimeout
        self.database = database
    }
    
    public func validate() throws {
        guard port > 0 && port < 65536 else {
            throw ServerConfigError.invalidPort(port)
        }
        
        guard maxConnections > 0 else {
            throw ServerConfigError.invalidMaxConnections(maxConnections)
        }
    }
}

/// Database configuration
public struct DatabaseConfig: Codable {
    public var path: String
    public var walEnabled: Bool
    public var checkpointInterval: TimeInterval
    
    public init(
        path: String = "data",
        walEnabled: Bool = true,
        checkpointInterval: TimeInterval = 60.0
    ) {
        self.path = path
        self.walEnabled = walEnabled
        self.checkpointInterval = checkpointInterval
    }
    
    /// Convert to DBConfig for database initialization
    public func toDBConfig() -> DBConfig {
        return DBConfig(
            dataDir: path,
            walEnabled: walEnabled
        )
    }
}

/// Server configuration errors
public enum ServerConfigError: Error {
    case invalidPort(Int)
    case invalidMaxConnections(Int)
}
