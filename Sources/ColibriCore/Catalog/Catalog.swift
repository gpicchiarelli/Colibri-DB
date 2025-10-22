//
//  Catalog.swift
//  ColibrìDB System Catalog
//
//  Based on: spec/Catalog.tla
//  Implements: System metadata management
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//

import Foundation

/// Column definition
public struct ColumnDefinition: Codable, Sendable {
    public let name: String
    public let type: ValueType
    public let nullable: Bool
    public let defaultValue: Value?
    
    public init(name: String, type: ValueType, nullable: Bool = true, defaultValue: Value? = nil) {
        self.name = name
        self.type = type
        self.nullable = nullable
        self.defaultValue = defaultValue
    }
}

/// Catalog index definition
public struct CatalogIndexDefinition: Codable, Sendable {
    public let name: String
    public let columns: [String]
    public let unique: Bool
    public let type: IndexType
    
    public enum IndexType: String, Codable {
        case btree
        case hash
    }
    
    public init(name: String, columns: [String], unique: Bool = false, type: IndexType = .btree) {
        self.name = name
        self.columns = columns
        self.unique = unique
        self.type = type
    }
}

/// Table definition
public struct TableDefinition: Codable, Sendable {
    public let name: String
    public let columns: [ColumnDefinition]
    public let primaryKey: [String]?
    public let indexes: [CatalogIndexDefinition]
    
    public init(name: String, columns: [ColumnDefinition], primaryKey: [String]? = nil, indexes: [CatalogIndexDefinition] = []) {
        self.name = name
        self.columns = columns
        self.primaryKey = primaryKey
        self.indexes = indexes
    }
}


/// System Catalog
/// Corresponds to TLA+ module: Catalog.tla
public actor Catalog {
    // MARK: - State
    
    private var tables: [String: TableDefinition] = [:]
    private var schemaVersion: Int = 1
    
    // MARK: - Initialization
    
    public init() {
        // Initialize with system tables
        initializeSystemTables()
    }
    
    /// Initialize system tables
    private func initializeSystemTables() {
        // System catalog table
        let catalogTable = TableDefinition(
            name: "colibri_tables",
            columns: [
                ColumnDefinition(name: "table_name", type: .string, nullable: false),
                ColumnDefinition(name: "schema_version", type: .int, nullable: false),
                ColumnDefinition(name: "created_at", type: .date, nullable: false)
            ],
            primaryKey: ["table_name"]
        )
        
        tables["colibri_tables"] = catalogTable
    }
    
    // MARK: - DDL Operations
    
    /// Create table
    public func createTable(_ table: TableDefinition) throws {
        guard tables[table.name] == nil else {
            throw DBError.duplicate
        }
        
        tables[table.name] = table
        schemaVersion += 1
    }
    
    /// Drop table
    public func dropTable(_ tableName: String) throws {
        guard tables[tableName] != nil else {
            throw DBError.notFound
        }
        
        tables[tableName] = nil
        schemaVersion += 1
    }
    
    /// Get table definition
    public func getTable(_ tableName: String) -> TableDefinition? {
        return tables[tableName]
    }
    
    /// List all tables
    public func listTables() -> [String] {
        return Array(tables.keys)
    }
    
    /// Add index to table
    public func addIndex(tableName: String, index: CatalogIndexDefinition) throws {
        guard var table = tables[tableName] else {
            throw DBError.notFound
        }
        
        var indexes = table.indexes
        indexes.append(index)
        
        tables[tableName] = TableDefinition(
            name: table.name,
            columns: table.columns,
            primaryKey: table.primaryKey,
            indexes: indexes
        )
        
        schemaVersion += 1
    }
    
    /// Get schema version
    public func getSchemaVersion() -> Int {
        return schemaVersion
    }
}

