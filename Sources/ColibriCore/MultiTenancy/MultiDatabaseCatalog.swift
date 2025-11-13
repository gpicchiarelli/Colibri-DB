//
//  MultiDatabaseCatalog.swift
//  Based on: spec/MultiDatabaseCatalog.tla
//

import Foundation

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

public actor MultiDatabaseCatalog {
    private var databases: [String: Database] = [:]
    private var currentDatabase: String?
    
    public init() {
        databases["system"] = Database(name: "system", owner: "admin")
        currentDatabase = "system"
    }
    
    public func createDatabase(name: String, owner: String) throws {
        guard databases[name] == nil else {
            throw DBError.duplicate
        }
        
        databases[name] = Database(name: name, owner: owner)
    }
    
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
    
    public func switchDatabase(name: String) throws {
        guard databases[name] != nil else {
            throw DBError.notFound
        }
        
        currentDatabase = name
    }
    
    public func getCurrentDatabase() -> String? {
        return currentDatabase
    }
    
    public func listDatabases() -> [String] {
        return Array(databases.keys)
    }
    
    public func getDatabaseInfo(name: String) -> Database? {
        return databases[name]
    }
}

