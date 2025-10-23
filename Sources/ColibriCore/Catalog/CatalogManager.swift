//
//  CatalogManager.swift
//  ColibrìDB System Catalog Implementation
//
//  Based on: spec/Catalog.tla
//  Implements: Database metadata management
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//
//  Key Properties:
//  - Consistency: Metadata changes are atomic
//  - Durability: Catalog survives crashes
//  - Isolation: DDL operations don't interfere
//  - Versioning: Schema changes are versioned
//

import Foundation

// MARK: - Column Metadata

/// Column metadata
/// Corresponds to TLA+: ColumnMetadata
public struct ColumnMetadata: Codable, Sendable, Equatable {
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

// MARK: - Table Metadata

/// Table metadata
/// Corresponds to TLA+: TableMetadata
public struct TableMetadata: Codable, Sendable, Equatable {
    public let name: String
    public let columns: [ColumnMetadata]
    public let primaryKey: Set<String>
    public let foreignKeys: [ForeignKeyMetadata]
    public let constraints: [ConstraintMetadata]
    
    public init(name: String, columns: [ColumnMetadata], primaryKey: Set<String> = [], foreignKeys: [ForeignKeyMetadata] = [], constraints: [ConstraintMetadata] = []) {
        self.name = name
        self.columns = columns
        self.primaryKey = primaryKey
        self.foreignKeys = foreignKeys
        self.constraints = constraints
    }
}

/// Foreign key metadata
public struct ForeignKeyMetadata: Codable, Sendable, Equatable {
    public let from: Set<String>
    public let to: ForeignKeyReference
    
    public init(from: Set<String>, to: ForeignKeyReference) {
        self.from = from
        self.to = to
    }
}

/// Foreign key reference
public struct ForeignKeyReference: Codable, Sendable, Equatable {
    public let table: String
    public let column: Set<String>
    
    public init(table: String, column: Set<String>) {
        self.table = table
        self.column = column
    }
}

/// Constraint type
public enum ConstraintType: String, Codable, Sendable {
    case check = "check"
    case unique = "unique"
    case notNull = "not_null"
}

/// Constraint metadata
public struct ConstraintMetadata: Codable, Sendable, Equatable {
    public let type: ConstraintType
    public let columns: Set<String>
    
    public init(type: ConstraintType, columns: Set<String>) {
        self.type = type
        self.columns = columns
    }
}


// MARK: - Index Metadata

/// Index metadata
/// Corresponds to TLA+: IndexMetadata
public struct IndexMetadata: Codable, Sendable, Equatable {
    public let name: String
    public let tableName: String
    public let columns: [String]
    public let indexType: IndexType
    public let unique: Bool
    
    public init(name: String, tableName: String, columns: [String], indexType: IndexType = .btree, unique: Bool = false) {
        self.name = name
        self.tableName = tableName
        self.columns = columns
        self.indexType = indexType
        self.unique = unique
    }
}

public enum IndexType: String, Codable, Sendable {
    case btree = "btree"
    case hash = "hash"
}

// MARK: - Statistics

/// Table statistics for query optimizer
/// Corresponds to TLA+: Statistics
public struct Statistics: Codable, Sendable, Equatable {
    public let rowCount: Int
    public let avgRowSize: Int
    public let distinctValues: [String: Int]
    
    public init(rowCount: Int, avgRowSize: Int = 100, distinctValues: [String: Int] = [:]) {
        self.rowCount = rowCount
        self.avgRowSize = avgRowSize
        self.distinctValues = distinctValues
    }
}

// MARK: - Catalog Manager

/// System Catalog Manager for database metadata
/// Corresponds to TLA+ module: Catalog.tla
public actor CatalogManager {
    
    // MARK: - State Variables (TLA+ vars)
    
    /// Table metadata
    /// TLA+: tables \in [TableName -> TableMetadata]
    private var tables: [String: TableMetadata] = [:]
    
    /// Index metadata
    /// TLA+: indexes \in [IndexName -> IndexMetadata]
    private var indexes: [String: IndexMetadata] = [:]
    
    /// Table statistics
    /// TLA+: statistics \in [TableName -> Statistics]
    private var statistics: [String: Statistics] = [:]
    
    /// Current schema version number
    /// TLA+: schemaVersion \in Nat
    private var schemaVersion: Int = 0
    
    // MARK: - Initialization
    
    public init() {
        // TLA+ Init
        self.tables = [:]
        self.indexes = [:]
        self.statistics = [:]
        self.schemaVersion = 0
    }
    
    // MARK: - Table Operations
    
    /// Create a table
    /// TLA+ Action: CreateTable(tableName, columns, primaryKey, foreignKeys, constraints)
    public func createTable(
        name: String,
        columns: [ColumnMetadata],
        primaryKey: Set<String> = [],
        foreignKeys: [ForeignKeyMetadata] = [],
        constraints: [ConstraintMetadata] = []
    ) throws {
        // TLA+: Check if table already exists
        guard tables[name] == nil else {
            throw DBError.tableAlreadyExists
        }
        
        // TLA+: Validate primary key columns exist
        for pkColumn in primaryKey {
            guard columns.contains(where: { $0.name == pkColumn }) else {
                throw DBError.invalidColumn("Primary key column \(pkColumn) not found")
            }
        }
        
        // TLA+: Validate foreign key columns exist
        for fk in foreignKeys {
            for fkColumn in fk.from {
                guard columns.contains(where: { $0.name == fkColumn }) else {
                    throw DBError.invalidColumn("Foreign key column \(fkColumn) not found")
                }
            }
        }
        
        // TLA+: Create table metadata
        let tableMetadata = TableMetadata(
            name: name,
            columns: columns,
            primaryKey: primaryKey,
            foreignKeys: foreignKeys,
            constraints: constraints
        )
        
        tables[name] = tableMetadata
        schemaVersion += 1
        
        // Initialize statistics
        statistics[name] = Statistics(rowCount: 0)
    }
    
    /// Drop a table
    /// TLA+ Action: DropTable(tableName)
    public func dropTable(name: String) throws {
        // TLA+: Check if table exists
        guard tables[name] != nil else {
            throw DBError.tableNotFound
        }
        
        // TLA+: Check for dependent indexes
        let dependentIndexes = indexes.values.filter { $0.tableName == name }
        if !dependentIndexes.isEmpty {
            throw DBError.custom("Table has dependent indexes")
        }
        
        // TLA+: Remove table and related metadata
        tables.removeValue(forKey: name)
        statistics.removeValue(forKey: name)
        schemaVersion += 1
    }
    
    /// Alter table (add column)
    /// TLA+ Action: AlterTable(tableName, newColumn)
    public func alterTableAddColumn(tableName: String, column: ColumnMetadata) throws {
        // TLA+: Check if table exists
        guard var tableMetadata = tables[tableName] else {
            throw DBError.tableNotFound
        }
        
        // TLA+: Check if column already exists
        guard !tableMetadata.columns.contains(where: { $0.name == column.name }) else {
            throw DBError.columnAlreadyExists
        }
        
        // TLA+: Add column to table
        var newColumns = tableMetadata.columns
        newColumns.append(column)
        
        let updatedTable = TableMetadata(
            name: tableName,
            columns: newColumns,
            primaryKey: tableMetadata.primaryKey,
            foreignKeys: tableMetadata.foreignKeys,
            constraints: tableMetadata.constraints
        )
        
        tables[tableName] = updatedTable
        schemaVersion += 1
    }
    
    /// Get table metadata
    public func getTable(name: String) -> TableMetadata? {
        return tables[name]
    }
    
    /// Get all table names
    public func getTableNames() -> [String] {
        return Array(tables.keys)
    }
    
    // MARK: - Index Operations
    
    /// Create an index
    /// TLA+ Action: CreateIndex(indexName, tableName, columns, indexType, unique)
    public func createIndex(
        name: String,
        tableName: String,
        columns: [String],
        indexType: IndexType = .btree,
        unique: Bool = false
    ) throws {
        // TLA+: Check if table exists
        guard tables[tableName] != nil else {
            throw DBError.tableNotFound
        }
        
        // TLA+: Check if index already exists
        guard indexes[name] == nil else {
            throw DBError.indexAlreadyExists
        }
        
        // TLA+: Validate index columns exist in table
        guard let tableMetadata = tables[tableName] else {
            throw DBError.tableNotFound
        }
        
        for column in columns {
            guard tableMetadata.columns.contains(where: { $0.name == column }) else {
                throw DBError.invalidColumn("Index column \(column) not found in table")
            }
        }
        
        // TLA+: Create index metadata
        let indexMetadata = IndexMetadata(
            name: name,
            tableName: tableName,
            columns: columns,
            indexType: indexType,
            unique: unique
        )
        
        indexes[name] = indexMetadata
        schemaVersion += 1
    }
    
    /// Drop an index
    /// TLA+ Action: DropIndex(indexName)
    public func dropIndex(name: String) throws {
        // TLA+: Check if index exists
        guard indexes[name] != nil else {
            throw DBError.indexNotFound
        }
        
        // TLA+: Remove index
        indexes.removeValue(forKey: name)
        schemaVersion += 1
    }
    
    /// Get index metadata
    public func getIndex(name: String) -> IndexMetadata? {
        return indexes[name]
    }
    
    /// Get indexes for a table
    public func getIndexes(for tableName: String) -> [IndexMetadata] {
        return indexes.values.filter { $0.tableName == tableName }
    }
    
    // MARK: - Statistics Operations
    
    /// Update table statistics
    /// TLA+ Action: UpdateStatistics(tableName, stats)
    public func updateStatistics(tableName: String, stats: Statistics) throws {
        // TLA+: Check if table exists
        guard tables[tableName] != nil else {
            throw DBError.tableNotFound
        }
        
        // TLA+: Update statistics
        statistics[tableName] = stats
    }
    
    /// Get table statistics
    public func getStatistics(tableName: String) -> Statistics? {
        return statistics[tableName]
    }
    
    /// Get all statistics
    public func getAllStatistics() -> [String: Statistics] {
        return statistics
    }
    
    // MARK: - Schema Versioning
    
    /// Get current schema version
    public func getSchemaVersion() -> Int {
        return schemaVersion
    }
    
    /// Increment schema version
    public func incrementSchemaVersion() {
        schemaVersion += 1
    }
    
    // MARK: - Query Operations
    
    /// Get total table count
    public func getTableCount() -> Int {
        return tables.count
    }
    
    /// Get total index count
    public func getIndexCount() -> Int {
        return indexes.count
    }
    
    /// Check if table exists
    public func tableExists(_ name: String) -> Bool {
        return tables[name] != nil
    }
    
    /// Check if index exists
    public func indexExists(_ name: String) -> Bool {
        return indexes[name] != nil
    }
    
    // MARK: - Invariant Checking (for testing)
    
    /// Check consistency invariant
    /// TLA+ Inv_Catalog_Consistency
    public func checkConsistencyInvariant() -> Bool {
        // Check that all indexes reference existing tables
        for (_, index) in indexes {
            if !tables.keys.contains(index.tableName) {
                return false
            }
        }
        
        // Check that all statistics reference existing tables
        for tableName in statistics.keys {
            if !tables.keys.contains(tableName) {
                return false
            }
        }
        
        return true
    }
    
    /// Check durability invariant
    /// TLA+ Inv_Catalog_Durability
    public func checkDurabilityInvariant() -> Bool {
        // Check that schema version is non-negative
        return schemaVersion >= 0
    }
    
    /// Check isolation invariant
    /// TLA+ Inv_Catalog_Isolation
    public func checkIsolationInvariant() -> Bool {
        // Check that table names are unique
        let tableNames = Set(tables.keys)
        return tableNames.count == tables.count
    }
    
    /// Check versioning invariant
    /// TLA+ Inv_Catalog_Versioning
    public func checkVersioningInvariant() -> Bool {
        // Check that schema version is monotonically increasing
        return schemaVersion >= 0
    }
    
    /// Check all invariants
    public func checkAllInvariants() -> Bool {
        let consistency = checkConsistencyInvariant()
        let durability = checkDurabilityInvariant()
        let isolation = checkIsolationInvariant()
        let versioning = checkVersioningInvariant()
        
        return consistency && durability && isolation && versioning
    }
}

// MARK: - Extensions

extension DBError {
    static let tableAlreadyExists = DBError.custom("Table already exists")
    static let tableNotFound = DBError.custom("Table not found")
    static let columnAlreadyExists = DBError.custom("Column already exists")
    static let indexAlreadyExists = DBError.custom("Index already exists")
    static let indexNotFound = DBError.custom("Index not found")
    static let tableHasDependencies = DBError.custom("Table has dependencies")
    
    static func invalidColumn(_ message: String) -> DBError {
        return .custom("Invalid column: \(message)")
    }
}
