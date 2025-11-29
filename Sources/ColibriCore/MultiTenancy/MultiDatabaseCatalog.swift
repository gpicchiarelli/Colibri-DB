//
//  MultiDatabaseCatalog.swift
//  Based on: spec/MultiDatabaseCatalog.tla
//

import Foundation

// MARK: - Types

/// Database metadata
public struct Database: @unchecked Sendable {
    public let name: String
    public let owner: String
    public let createdAt: Date
    public var encoding: String
    public var collation: String
    
    public init(name: String, owner: String, encoding: String = "UTF8", collation: String = "en_US.UTF-8") {
        self.name = name
        self.owner = owner
        self.createdAt = Date()
        self.encoding = encoding
        self.collation = collation
    }
}

// MARK: - Multi Database Catalog

/// Catalog for managing multiple databases
public actor MultiDatabaseCatalog {
    // MARK: - Properties
    
    private var databases: [String: Database] = [:]
    private var currentDatabase: String?
    
    // MARK: - Initialization
    
    /// Initialize multi-database catalog
    public init() {
        databases["system"] = Database(name: "system", owner: "admin")
        currentDatabase = "system"
    }
    
    // MARK: - Public Methods
    
    /// Create a new database
    /// - Parameters:
    ///   - name: Database name
    ///   - owner: Database owner
    public func createDatabase(name: String, owner: String) throws {
        guard databases[name] == nil else {
            throw DBError.duplicate
        }
        
        databases[name] = Database(name: name, owner: owner)
    }
    
    /// Drop a database
    /// - Parameter name: Database name to drop
    public func dropDatabase(name: String) throws {
        guard name != "system" else {
            throw DBError.internalError("Cannot drop system database")
        }
        
        guard databases[name] != nil else {
            throw DBError.notFound
        }
        
        databases[name] = nil
        
        if currentDatabase == name {
            currentDatabase = "system"
        }
    }
    
    /// Switch to a different database
    /// - Parameter name: Database name to switch to
    public func switchDatabase(name: String) throws {
        guard databases[name] != nil else {
            throw DBError.notFound
        }
        
        currentDatabase = name
    }
    
    /// Get current database name
    /// - Returns: Current database name, or nil
    public func getCurrentDatabase() -> String? {
        return currentDatabase
    }
    
    /// List all databases
    /// - Returns: Array of database names
    public func listDatabases() -> [String] {
        return Array(databases.keys)
    }
    
    /// Get database information
    /// - Parameter name: Database name
    /// - Returns: Database metadata, or nil if not found
    public func getDatabaseInfo(name: String) -> Database? {
        return databases[name]
    }
}

