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
    
    public enum IndexType: String, Codable, Sendable {
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


/// System Catalog (Compatibility Wrapper)
/// Corresponds to TLA+ module: Catalog.tla
/// 
/// **DEPRECATED**: This is a compatibility wrapper for CatalogManager.
/// New code should use CatalogManager directly.
/// 
/// This wrapper delegates all operations to CatalogManager to maintain
/// backward compatibility with existing code while migrating to CatalogManager.
public actor Catalog {
    // MARK: - Internal Catalog Manager
    
    /// Internal Catalog Manager (the real implementation)
    /// **Catalog-First**: All operations delegate to CatalogManager
    private let catalogManager: CatalogManager
    
    // MARK: - Initialization
    
    /// Initialize Catalog with CatalogManager
    /// 
    /// **Catalog-First**: Catalog is a thin wrapper around CatalogManager.
    /// All metadata comes from CatalogManager.
    public init(storageManager: StorageManager? = nil, walManager: WALManagerProtocol? = nil) {
        // Create CatalogManager (the real implementation)
        self.catalogManager = CatalogManager(
            storageManager: storageManager,
            walManager: walManager
        )
    }
    
    // MARK: - DDL Operations (Delegated to CatalogManager)
    
    /// Create table
    /// **Catalog-First**: Delegates to CatalogManager
    public func createTable(_ table: TableDefinition) async throws {
        // Convert TableDefinition to TableMetadata
        let columns = table.columns.map { col in
            ColumnMetadata(name: col.name, type: col.type, nullable: col.nullable, defaultValue: col.defaultValue)
        }
        let primaryKey = Set(table.primaryKey ?? [])
        let foreignKeys: [ForeignKeyMetadata] = []  // TODO: Add foreign key support
        let constraints: [ConstraintMetadata] = []  // TODO: Add constraint support
        
        // Delegate to CatalogManager
        try await catalogManager.createTable(
            name: table.name,
            columns: columns,
            primaryKey: primaryKey,
            foreignKeys: foreignKeys,
            constraints: constraints
        )
    }
    
    /// Drop table
    /// **Catalog-First**: Delegates to CatalogManager
    public func dropTable(_ tableName: String) async throws {
        // Delegate to CatalogManager
        try await catalogManager.dropTable(name: tableName)
    }
    
    /// Get table definition
    /// **Catalog-First**: Delegates to CatalogManager
    public func getTable(_ tableName: String) async -> TableDefinition? {
        // Get from CatalogManager
        guard let tableMetadata = await catalogManager.getTable(name: tableName) else {
            return nil
        }
        
        // Convert TableMetadata to TableDefinition (for backward compatibility)
        let columns = tableMetadata.columns.map { col in
            ColumnDefinition(name: col.name, type: col.type, nullable: col.nullable, defaultValue: col.defaultValue)
        }
        let primaryKey = Array(tableMetadata.primaryKey)
        let indexes: [CatalogIndexDefinition] = []  // TODO: Get indexes from CatalogManager
        
        return TableDefinition(
            name: tableMetadata.name,
            columns: columns,
            primaryKey: primaryKey.isEmpty ? nil : primaryKey,
            indexes: indexes
        )
    }
    
    /// List all tables
    /// **Catalog-First**: Delegates to CatalogManager
    public func listTables() async -> [String] {
        // Delegate to CatalogManager
        return await catalogManager.getTableNames()
    }
    
    /// Add index to table
    /// **Catalog-First**: Delegates to CatalogManager
    public func addIndex(tableName: String, index: CatalogIndexDefinition) async throws {
        // Delegate to CatalogManager
        try await catalogManager.createIndex(
            name: index.name,
            tableName: tableName,
            columns: index.columns,
            indexType: index.type == .btree ? .btree : .hash,
            unique: index.unique
        )
    }
    
    /// Get schema version
    /// **Catalog-First**: Delegates to CatalogManager
    public func getSchemaVersion() async -> Int {
        // Delegate to CatalogManager
        return await catalogManager.getSchemaVersion()
    }
    
    // MARK: - Direct Access to CatalogManager (for new code)
    
    /// Get the underlying CatalogManager
    /// **Catalog-First**: Use this for direct access to CatalogManager
    public func getCatalogManager() -> CatalogManager {
        return catalogManager
    }
}

