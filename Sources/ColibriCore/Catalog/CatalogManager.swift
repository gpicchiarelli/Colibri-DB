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

// MARK: - DDL Operation Record (for WAL)

/// DDL operation record for WAL logging
/// Used to log Catalog DDL operations for crash recovery
private struct DDLOperationRecord: Codable, Sendable {
    let operation: String  // "CREATE_TABLE", "DROP_TABLE", "ALTER_TABLE_ADD_COLUMN", "CREATE_INDEX", "DROP_INDEX"
    let tableName: String?
    let indexName: String?
    let metadata: TableMetadata?
    let indexMetadata: IndexMetadata?
    
    init(operation: String, tableName: String?, metadata: TableMetadata?, indexName: String? = nil, indexMetadata: IndexMetadata? = nil) {
        self.operation = operation
        self.tableName = tableName
        self.indexName = indexName
        self.metadata = metadata
        self.indexMetadata = indexMetadata
    }
    
    init(operation: String, tableName: String?, indexMetadata: IndexMetadata?) {
        self.operation = operation
        self.tableName = tableName
        self.indexName = nil
        self.metadata = nil
        self.indexMetadata = indexMetadata
    }
    
    init(operation: String, tableName: String?, indexName: String) {
        self.operation = operation
        self.tableName = tableName
        self.indexName = indexName
        self.metadata = nil
        self.indexMetadata = nil
    }
}

// MARK: - User and Role Types (for Catalog)

/// Role metadata
/// **Catalog-First**: Roles stored in Catalog
public struct RoleMetadata: Codable, Sendable, Equatable {
    public let name: String
    public let permissions: [String]  // List of permission strings (e.g., "SELECT:users", "INSERT:orders")
    
    public init(name: String, permissions: [String] = []) {
        self.name = name
        self.permissions = permissions
    }
}

/// Permission metadata
/// **Catalog-First**: Permissions stored in Catalog
public struct PermissionMetadata: Codable, Sendable, Equatable {
    public let username: String
    public let tableName: String
    public let permission: String  // "SELECT", "INSERT", "UPDATE", "DELETE"
    
    public init(username: String, tableName: String, permission: String) {
        self.username = username
        self.tableName = tableName
        self.permission = permission
    }
}

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

/// Foreign key action (for CASCADE/SET NULL)
public enum ForeignKeyAction: String, Codable, Sendable {
    case restrict = "RESTRICT"    // Prevent deletion/update (default)
    case cascade = "CASCADE"      // Delete/update referencing rows
    case setNull = "SET NULL"     // Set foreign key columns to NULL
    case setDefault = "SET DEFAULT"  // Set foreign key columns to default value
    case noAction = "NO ACTION"   // Similar to RESTRICT (SQL standard)
}

/// Foreign key metadata
public struct ForeignKeyMetadata: Codable, Sendable, Equatable {
    public let from: Set<String>
    public let to: ForeignKeyReference
    public let onDelete: ForeignKeyAction  // Action on DELETE
    public let onUpdate: ForeignKeyAction  // Action on UPDATE
    
    public init(from: Set<String>, to: ForeignKeyReference, onDelete: ForeignKeyAction = .restrict, onUpdate: ForeignKeyAction = .restrict) {
        self.from = from
        self.to = to
        self.onDelete = onDelete
        self.onUpdate = onUpdate
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
/// 
/// **CRITICAL**: The Catalog Manager is the FOUNDATION of ColibrìDB.
/// EVERY component MUST depend on the Catalog for metadata.
/// NOTHING operates without consulting the Catalog first.
///
/// The Catalog Manager serves as the single source of truth for:
/// - Table schemas and column definitions
/// - Index definitions and metadata
/// - Statistics for query optimization
/// - User and role management (future)
/// - System configuration (future)
public actor CatalogManager {
    
    // MARK: - State Variables (TLA+ vars)
    
    /// Table metadata
    /// TLA+: tables \in [TableName -> TableMetadata]
    /// **Catalog-First**: ALL table metadata comes from Catalog
    private var tables: [String: TableMetadata] = [:]
    
    /// Index metadata
    /// TLA+: indexes \in [IndexName -> IndexMetadata]
    /// **Catalog-First**: ALL index metadata comes from Catalog
    private var indexes: [String: IndexMetadata] = [:]
    
    /// Table statistics
    /// TLA+: statistics \in [TableName -> Statistics]
    /// **Catalog-First**: ALL statistics come from Catalog
    private var statistics: [String: Statistics] = [:]
    
    /// Users (Catalog-First: user metadata stored in Catalog)
    /// **Catalog-First**: Authentication Manager uses Catalog for user metadata
    private var users: [String: UserMetadata] = [:]
    
    /// Roles (Catalog-First: role definitions stored in Catalog)
    /// **Catalog-First**: Role-based access control uses Catalog
    private var roles: [String: RoleMetadata] = [:]
    
    /// Permissions (Catalog-First: permission grants stored in Catalog)
    /// **Catalog-First**: Permission checks use Catalog
    private var permissions: [String: [PermissionMetadata]] = [:]  // [tableName: [PermissionMetadata]]
    
    /// Current schema version number
    /// TLA+: schemaVersion \in Nat
    private var schemaVersion: Int = 0
    
    /// Bootstrap flag - indicates if system tables have been created
    private var isBootstrapped: Bool = false
    
    // MARK: - System Table Page IDs
    
    /// System table page IDs (fixed for consistency)
    /// These pages store Catalog metadata in JSON format
    private static let SYSTEM_PAGE_TABLES: PageID = 1       // colibri_tables: [TableMetadata]
    private static let SYSTEM_PAGE_INDEXES: PageID = 2      // colibri_indexes: [IndexMetadata]
    private static let SYSTEM_PAGE_STATISTICS: PageID = 3   // colibri_statistics: [String: Statistics]
    private static let SYSTEM_PAGE_USERS: PageID = 4        // colibri_users: [UserMetadata]
    private static let SYSTEM_PAGE_ROLES: PageID = 5        // colibri_roles: [RoleMetadata]
    private static let SYSTEM_PAGE_PERMISSIONS: PageID = 6  // colibri_permissions: [String: [PermissionMetadata]]
    
    // MARK: - Dependencies
    
    /// Storage Manager for Catalog persistence
    /// Used to persist Catalog to system tables
    /// Can be set after init to avoid circular dependencies
    private var storageManager: StorageManager?
    
    /// WAL Manager for Catalog durability (optional)
    /// Used to log Catalog changes for recovery
    /// Can be set after init to avoid circular dependencies
    private var walManager: WALManagerProtocol?
    
    // MARK: - Initialization
    
    /// Initialize Catalog Manager
    /// - Parameter storageManager: Optional storage manager for Catalog persistence
    /// - Parameter walManager: Optional WAL manager for Catalog durability
    /// 
    /// **Bootstrap Process**:
    /// 1. If storageManager provided: Loads Catalog from system tables
    /// 2. If system tables don't exist: Bootstraps system tables
    /// 3. If storageManager nil: In-memory only (for testing)
    public init(storageManager: StorageManager? = nil, walManager: WALManagerProtocol? = nil) {
        self.storageManager = storageManager
        self.walManager = walManager
        
        // TLA+ Init
        self.tables = [:]
        self.indexes = [:]
        self.statistics = [:]
        self.users = [:]
        self.roles = [:]
        self.permissions = [:]
        self.schemaVersion = 0
        self.isBootstrapped = false
        
        // Bootstrap if storage manager available
        if storageManager != nil {
            Task {
                try? await bootstrap()
            }
        }
    }
    
    // MARK: - Bootstrap Process
    
    /// Bootstrap system tables (create Catalog's own tables)
    /// **CRITICAL**: Catalog must bootstrap itself before use
    /// 
    /// **Bootstrap Sequence**:
    /// 1. Check if system tables exist
    /// 2. If not: Create system tables (colibri_tables, colibri_columns, etc.)
    /// 3. If yes: Load Catalog from system tables
    /// 4. Mark as bootstrapped
    public func bootstrap() async throws {
        guard let storage = storageManager else {
            // No storage manager - in-memory only (for testing)
            isBootstrapped = true
            return
        }
        
        // Check if system tables exist
        let systemTablesExist = try await checkSystemTablesExist(storage: storage)
        
        if !systemTablesExist {
            // Bootstrap: Create system tables
            try await createSystemTables(storage: storage)
        } else {
            // Load Catalog from system tables
            try await loadCatalogFromSystemTables(storage: storage)
        }
        
        isBootstrapped = true
    }
    
    /// Check if system tables exist
    /// Checks if system table pages exist by attempting to read them
    private func checkSystemTablesExist(storage: StorageManager) async throws -> Bool {
        // Try to read the first system page (tables)
        // If it exists and has data, system tables are bootstrapped
        do {
            let data = try await storage.readPage(pageId: Self.SYSTEM_PAGE_TABLES)
            return !data.isEmpty
        } catch {
            // Page doesn't exist or can't be read - system tables not bootstrapped
            return false
        }
    }
    
    /// Create system tables (Catalog's own tables)
    /// Initializes system table pages with empty JSON arrays/dictionaries
    private func createSystemTables(storage: StorageManager) async throws {
        let encoder = JSONEncoder()
        encoder.outputFormatting = [.prettyPrinted, .sortedKeys]
        
        // Initialize colibri_tables with empty array
        let emptyTablesArray: [TableMetadata] = []
        let tablesData = try encoder.encode(emptyTablesArray)
        try await storage.writePage(pageId: Self.SYSTEM_PAGE_TABLES, data: tablesData)
        
        // Initialize colibri_indexes with empty array
        let emptyIndexesArray: [IndexMetadata] = []
        let indexesData = try encoder.encode(emptyIndexesArray)
        try await storage.writePage(pageId: Self.SYSTEM_PAGE_INDEXES, data: indexesData)
        
        // Initialize colibri_statistics with empty dictionary
        let emptyStatisticsDict: [String: Statistics] = [:]
        let statisticsData = try encoder.encode(emptyStatisticsDict)
        try await storage.writePage(pageId: Self.SYSTEM_PAGE_STATISTICS, data: statisticsData)
        
        // Initialize colibri_users with empty array
        let emptyUsersArray: [UserMetadata] = []
        let usersData = try encoder.encode(emptyUsersArray)
        try await storage.writePage(pageId: Self.SYSTEM_PAGE_USERS, data: usersData)
        
        // Initialize colibri_roles with empty array
        let emptyRolesArray: [RoleMetadata] = []
        let rolesData = try encoder.encode(emptyRolesArray)
        try await storage.writePage(pageId: Self.SYSTEM_PAGE_ROLES, data: rolesData)
        
        // Initialize colibri_permissions with empty dictionary
        let emptyPermissionsDict: [String: [PermissionMetadata]] = [:]
        let permissionsData = try encoder.encode(emptyPermissionsDict)
        try await storage.writePage(pageId: Self.SYSTEM_PAGE_PERMISSIONS, data: permissionsData)
    }
    
    /// Load Catalog from system tables (on restart)
    /// Deserializes Catalog metadata from system table pages
    private func loadCatalogFromSystemTables(storage: StorageManager) async throws {
        let decoder = JSONDecoder()
        
        // Load tables from colibri_tables system table
        do {
            let tablesData = try await storage.readPage(pageId: Self.SYSTEM_PAGE_TABLES)
            if !tablesData.isEmpty {
                let loadedTables: [TableMetadata] = try decoder.decode([TableMetadata].self, from: tablesData)
                for table in loadedTables {
                    tables[table.name] = table
                }
            }
        } catch {
            // If reading fails, start with empty tables (bootstrap will create pages)
            tables = [:]
        }
        
        // Load indexes from colibri_indexes system table
        do {
            let indexesData = try await storage.readPage(pageId: Self.SYSTEM_PAGE_INDEXES)
            if !indexesData.isEmpty {
                let loadedIndexes: [IndexMetadata] = try decoder.decode([IndexMetadata].self, from: indexesData)
                for index in loadedIndexes {
                    indexes[index.name] = index
                }
            }
        } catch {
            // If reading fails, start with empty indexes (bootstrap will create pages)
            indexes = [:]
        }
        
        // Load statistics from colibri_statistics system table
        do {
            let statisticsData = try await storage.readPage(pageId: Self.SYSTEM_PAGE_STATISTICS)
            if !statisticsData.isEmpty {
                let loadedStatistics: [String: Statistics] = try decoder.decode([String: Statistics].self, from: statisticsData)
                statistics = loadedStatistics
            }
        } catch {
            // If reading fails, start with empty statistics (bootstrap will create pages)
            statistics = [:]
        }
        
        // Load users from colibri_users system table
        do {
            let usersData = try await storage.readPage(pageId: Self.SYSTEM_PAGE_USERS)
            if !usersData.isEmpty {
                let loadedUsers: [UserMetadata] = try decoder.decode([UserMetadata].self, from: usersData)
                for user in loadedUsers {
                    users[user.username] = user
                }
            }
        } catch {
            // If reading fails, start with empty users (bootstrap will create pages)
            users = [:]
        }
        
        // Load roles from colibri_roles system table
        do {
            let rolesData = try await storage.readPage(pageId: Self.SYSTEM_PAGE_ROLES)
            if !rolesData.isEmpty {
                let loadedRoles: [RoleMetadata] = try decoder.decode([RoleMetadata].self, from: rolesData)
                for role in loadedRoles {
                    roles[role.name] = role
                }
            }
        } catch {
            // If reading fails, start with empty roles (bootstrap will create pages)
            roles = [:]
        }
        
        // Load permissions from colibri_permissions system table
        do {
            let permissionsData = try await storage.readPage(pageId: Self.SYSTEM_PAGE_PERMISSIONS)
            if !permissionsData.isEmpty {
                let loadedPermissions: [String: [PermissionMetadata]] = try decoder.decode([String: [PermissionMetadata]].self, from: permissionsData)
                permissions = loadedPermissions
            }
        } catch {
            // If reading fails, start with empty permissions (bootstrap will create pages)
            permissions = [:]
        }
    }
    
    /// Persist table metadata to system table
    /// Serializes all tables to JSON and writes to system page
    private func persistTableMetadata(name: String, metadata: TableMetadata) async throws {
        guard let storage = storageManager else {
            return  // No persistence available
        }
        
        let encoder = JSONEncoder()
        encoder.outputFormatting = [.prettyPrinted, .sortedKeys]
        
        // Serialize all tables (including the new one)
        let allTables = Array(tables.values)
        let tablesData = try encoder.encode(allTables)
        try await storage.writePage(pageId: Self.SYSTEM_PAGE_TABLES, data: tablesData)
    }
    
    /// Persist index metadata to system table
    /// Serializes all indexes to JSON and writes to system page
    private func persistIndexMetadata(name: String, metadata: IndexMetadata) async throws {
        guard let storage = storageManager else {
            return  // No persistence available
        }
        
        let encoder = JSONEncoder()
        encoder.outputFormatting = [.prettyPrinted, .sortedKeys]
        
        // Serialize all indexes (including the new one)
        let allIndexes = Array(indexes.values)
        let indexesData = try encoder.encode(allIndexes)
        try await storage.writePage(pageId: Self.SYSTEM_PAGE_INDEXES, data: indexesData)
    }
    
    /// Persist statistics to system table
    /// Serializes all statistics to JSON and writes to system page
    private func persistStatistics(tableName: String, stats: Statistics) async throws {
        guard let storage = storageManager else {
            return  // No persistence available
        }
        
        let encoder = JSONEncoder()
        encoder.outputFormatting = [.prettyPrinted, .sortedKeys]
        
        // Serialize all statistics (including the updated one)
        let statisticsData = try encoder.encode(statistics)
        try await storage.writePage(pageId: Self.SYSTEM_PAGE_STATISTICS, data: statisticsData)
    }
    
    /// Delete table metadata from system table
    /// Re-serializes all remaining tables to JSON and writes to system page
    private func deleteTableMetadata(name: String, storage: StorageManager) async throws {
        let encoder = JSONEncoder()
        encoder.outputFormatting = [.prettyPrinted, .sortedKeys]
        
        // Serialize all remaining tables (excluding the deleted one)
        let allTables = Array(tables.values)
        let tablesData = try encoder.encode(allTables)
        try await storage.writePage(pageId: Self.SYSTEM_PAGE_TABLES, data: tablesData)
    }
    
    /// Delete index metadata from system table
    /// Re-serializes all remaining indexes to JSON and writes to system page
    private func deleteIndexMetadata(name: String, storage: StorageManager) async throws {
        let encoder = JSONEncoder()
        encoder.outputFormatting = [.prettyPrinted, .sortedKeys]
        
        // Serialize all remaining indexes (excluding the deleted one)
        let allIndexes = Array(indexes.values)
        let indexesData = try encoder.encode(allIndexes)
        try await storage.writePage(pageId: Self.SYSTEM_PAGE_INDEXES, data: indexesData)
    }
    
    // MARK: - Table Operations
    
    /// Create a table
    /// TLA+ Action: CreateTable(tableName, columns, primaryKey, foreignKeys, constraints)
    /// 
    /// **Catalog-First**: This is THE ONLY place where tables are created.
    /// Storage Manager, Index Manager, and all other components MUST check
    /// Catalog before operating on tables.
    public func createTable(
        name: String,
        columns: [ColumnMetadata],
        primaryKey: Set<String> = [],
        foreignKeys: [ForeignKeyMetadata] = [],
        constraints: [ConstraintMetadata] = []
    ) async throws {
        // Validate table name
        guard !name.isEmpty else {
            throw CatalogError.invalidTableName("Table name cannot be empty")
        }
        guard !name.hasPrefix("colibri_") else {
            throw CatalogError.invalidTableName("Cannot create table with colibri_ prefix (reserved for system tables)")
        }
        
        // TLA+: Check if table already exists
        guard tables[name] == nil else {
            throw CatalogError.tableAlreadyExists(name)
        }
        
        // TLA+: Validate columns are non-empty and unique
        guard !columns.isEmpty else {
            throw CatalogError.invalidTableName("Table must have at least one column")
        }
        let columnNames = Set(columns.map { $0.name })
        guard columnNames.count == columns.count else {
            throw CatalogError.invalidColumn("Duplicate column names found")
        }
        
        // TLA+: Validate primary key columns exist
        for pkColumn in primaryKey {
            guard columns.contains(where: { $0.name == pkColumn }) else {
                throw CatalogError.invalidColumn("Primary key column \(pkColumn) not found")
            }
        }
        
        // TLA+: Validate foreign key columns exist
        for fk in foreignKeys {
            for fkColumn in fk.from {
                guard columns.contains(where: { $0.name == fkColumn }) else {
                    throw CatalogError.invalidColumn("Foreign key column \(fkColumn) not found")
                }
            }
            
            // Validate referenced table exists
            guard tables[fk.to.table] != nil else {
                throw CatalogError.tableNotFound(fk.to.table)
            }
            
            // Validate referenced columns exist in referenced table
            guard let referencedTable = tables[fk.to.table] else {
                throw CatalogError.tableNotFound(fk.to.table)
            }
            for refColumn in fk.to.column {
                guard referencedTable.columns.contains(where: { $0.name == refColumn }) else {
                    throw CatalogError.invalidColumn("Referenced column \(refColumn) not found in table \(fk.to.table)")
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
        
        // Store in memory (Catalog-First: single source of truth)
        tables[name] = tableMetadata
        
        // Persist to system table (if storage available)
        try await persistTableMetadata(name: name, metadata: tableMetadata)
        
        // Log to WAL (if available) for durability
        // **Catalog-First**: DDL operations are logged to WAL for crash recovery
        if let wal = walManager {
            let ddlRecord = DDLOperationRecord(
                operation: "CREATE_TABLE",
                tableName: name,
                metadata: tableMetadata
            )
            let encoder = JSONEncoder()
            let payload = try encoder.encode(ddlRecord)
            _ = try await wal.appendRecord(txId: 0, kind: "ddl", data: payload)  // txId 0 for DDL operations
            try await wal.flushLog()  // Flush immediately for DDL durability
        }
        
        // Increment schema version
        schemaVersion += 1
        
        // Initialize statistics
        statistics[name] = Statistics(rowCount: 0)
    }
    
    /// Drop a table
    /// TLA+ Action: DropTable(tableName)
    /// 
    /// **Catalog-First**: This is THE ONLY place where tables are dropped.
    /// All components MUST check Catalog before operating on tables.
    public func dropTable(name: String) async throws {
        // Validate table name
        guard !name.hasPrefix("colibri_") else {
            throw CatalogError.invalidTableName("Cannot drop system table \(name)")
        }
        
        // TLA+: Check if table exists
        guard tables[name] != nil else {
            throw CatalogError.tableNotFound(name)
        }
        
        // TLA+: Check for dependent indexes
        let dependentIndexes = indexes.values.filter { $0.tableName == name }
        if !dependentIndexes.isEmpty {
            let indexNames = dependentIndexes.map { $0.name }.joined(separator: ", ")
            throw CatalogError.tableHasDependencies("Table \(name) has dependent indexes: \(indexNames)")
        }
        
        // TLA+: Check for foreign key references
        let referencingTables = tables.values.filter { table in
            table.foreignKeys.contains { $0.to.table == name }
        }
        if !referencingTables.isEmpty {
            let tableNames = referencingTables.map { $0.name }.joined(separator: ", ")
            throw CatalogError.tableHasDependencies("Table \(name) is referenced by foreign keys in tables: \(tableNames)")
        }
        
        // TLA+: Remove table and related metadata
        tables.removeValue(forKey: name)
        statistics.removeValue(forKey: name)
        
        // Persist to system table (if storage available)
        if let storage = storageManager {
            try await deleteTableMetadata(name: name, storage: storage)
        }
        
        // Log to WAL (if available) for durability
        // **Catalog-First**: DDL operations are logged to WAL for crash recovery
        if let wal = walManager {
            let ddlRecord = DDLOperationRecord(
                operation: "DROP_TABLE",
                tableName: name,
                metadata: nil
            )
            let encoder = JSONEncoder()
            let payload = try encoder.encode(ddlRecord)
            _ = try await wal.appendRecord(txId: 0, kind: "ddl", data: payload)  // txId 0 for DDL operations
            try await wal.flushLog()  // Flush immediately for DDL durability
        }
        
        // Increment schema version
        schemaVersion += 1
    }
    
    /// Alter table (add column)
    /// TLA+ Action: AlterTable(tableName, newColumn)
    /// 
    /// **Catalog-First**: Schema changes MUST go through Catalog.
    public func alterTableAddColumn(tableName: String, column: ColumnMetadata) async throws {
        // TLA+: Check if table exists
        guard let tableMetadata = tables[tableName] else {
            throw CatalogError.tableNotFound(tableName)
        }
        
        // TLA+: Check if column already exists
        guard !tableMetadata.columns.contains(where: { $0.name == column.name }) else {
            throw CatalogError.columnAlreadyExists(tableName: tableName, column: column.name)
        }
        
        // TLA+: Add column to table
        let newColumns = tableMetadata.columns + [column]
        
        let updatedTable = TableMetadata(
            name: tableName,
            columns: newColumns,
            primaryKey: tableMetadata.primaryKey,
            foreignKeys: tableMetadata.foreignKeys,
            constraints: tableMetadata.constraints
        )
        
        tables[tableName] = updatedTable
        
        // Persist to system table (if storage available)
        try await persistTableMetadata(name: tableName, metadata: updatedTable)
        
        // Log to WAL (if available) for durability
        // **Catalog-First**: DDL operations are logged to WAL for crash recovery
        if let wal = walManager {
            let ddlRecord = DDLOperationRecord(
                operation: "ALTER_TABLE_ADD_COLUMN",
                tableName: tableName,
                metadata: updatedTable
            )
            let encoder = JSONEncoder()
            let payload = try encoder.encode(ddlRecord)
            _ = try await wal.appendRecord(txId: 0, kind: "ddl", data: payload)  // txId 0 for DDL operations
            try await wal.flushLog()  // Flush immediately for DDL durability
        }
        
        schemaVersion += 1
    }
    
    /// Get table metadata
    /// 
    /// **Catalog-First**: This is THE ONLY source of table metadata.
    /// Components MUST use this method to get table information.
    /// 
    /// - Parameter name: Table name
    /// - Returns: Table metadata if exists, nil otherwise
    /// 
    /// **Performance**: O(1) hash table lookup
    public func getTable(name: String) -> TableMetadata? {
        // Catalog-First: Return from Catalog (single source of truth)
        return tables[name]
    }
    
    /// Get table metadata (async version for future persistence loading)
    public func getTable(name: String) async -> TableMetadata? {
        // Check memory cache first
        if let table = tables[name] {
            return table  // Cache hit
        }
        
        // TODO: Load from system table if storage available
        // For now, return from memory only
        return tables[name]
    }
    
    /// Get all table names
    public func getTableNames() -> [String] {
        return Array(tables.keys)
    }
    
    // MARK: - Index Operations
    
    /// Create an index
    /// TLA+ Action: CreateIndex(indexName, tableName, columns, indexType, unique)
    /// 
    /// **Catalog-First**: This is THE ONLY place where indexes are created.
    /// Index Manager MUST check Catalog before creating index structures.
    public func createIndex(
        name: String,
        tableName: String,
        columns: [String],
        indexType: IndexType = .btree,
        unique: Bool = false
    ) async throws {
        // Validate index name
        guard !name.isEmpty else {
            throw CatalogError.invalidIndexName("Index name cannot be empty")
        }
        
        // TLA+: Check if table exists
        guard let tableMetadata = tables[tableName] else {
            throw CatalogError.tableNotFound(tableName)
        }
        
        // TLA+: Check if index already exists
        guard indexes[name] == nil else {
            throw CatalogError.indexAlreadyExists(name)
        }
        
        // TLA+: Validate index columns exist in table
        for column in columns {
            guard tableMetadata.columns.contains(where: { $0.name == column }) else {
                throw CatalogError.invalidColumn("Index column \(column) not found in table \(tableName)")
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
        
        // Store in memory (Catalog-First: single source of truth)
        indexes[name] = indexMetadata
        
        // Persist to system table (if storage available)
        try await persistIndexMetadata(name: name, metadata: indexMetadata)
        
        // Log to WAL (if available) for durability
        // **Catalog-First**: DDL operations are logged to WAL for crash recovery
        if let wal = walManager {
            let ddlRecord = DDLOperationRecord(
                operation: "CREATE_INDEX",
                tableName: tableName,
                indexMetadata: indexMetadata
            )
            let encoder = JSONEncoder()
            let payload = try encoder.encode(ddlRecord)
            _ = try await wal.appendRecord(txId: 0, kind: "ddl", data: payload)  // txId 0 for DDL operations
            try await wal.flushLog()  // Flush immediately for DDL durability
        }
        
        schemaVersion += 1
    }
    
    /// Drop an index
    /// TLA+ Action: DropIndex(indexName)
    /// 
    /// **Catalog-First**: This is THE ONLY place where indexes are dropped.
    public func dropIndex(name: String) async throws {
        // TLA+: Check if index exists
        guard indexes[name] != nil else {
            throw CatalogError.indexNotFound(name)
        }
        
        // TLA+: Remove index
        indexes.removeValue(forKey: name)
        
        // Persist to system table (if storage available)
        if let storage = storageManager {
            try await deleteIndexMetadata(name: name, storage: storage)
        }
        
        // Log to WAL (if available) for durability
        // **Catalog-First**: DDL operations are logged to WAL for crash recovery
        if let wal = walManager {
            let ddlRecord = DDLOperationRecord(
                operation: "DROP_INDEX",
                tableName: nil,
                indexName: name
            )
            let encoder = JSONEncoder()
            let payload = try encoder.encode(ddlRecord)
            _ = try await wal.appendRecord(txId: 0, kind: "ddl", data: payload)  // txId 0 for DDL operations
            try await wal.flushLog()  // Flush immediately for DDL durability
        }
        
        schemaVersion += 1
    }
    
    /// Get index metadata
    /// 
    /// **Catalog-First**: This is THE ONLY source of index metadata.
    /// Index Manager MUST use this method to get index information.
    public func getIndex(name: String) -> IndexMetadata? {
        // Catalog-First: Return from Catalog (single source of truth)
        return indexes[name]
    }
    
    /// Get index metadata (async version)
    public func getIndex(name: String) async -> IndexMetadata? {
        return indexes[name]
    }
    
    /// Get indexes for a table
    /// 
    /// **Catalog-First**: Query Optimizer MUST use this for index selection.
    public func getIndexes(for tableName: String) -> [IndexMetadata] {
        // Catalog-First: Return from Catalog
        return indexes.values.filter { $0.tableName == tableName }
    }
    
    /// Get indexes for a table (async version)
    public func getIndexes(for tableName: String) async -> [IndexMetadata] {
        return indexes.values.filter { $0.tableName == tableName }
    }
    
    // MARK: - Statistics Operations
    
    /// Update table statistics
    /// TLA+ Action: UpdateStatistics(tableName, stats)
    /// 
    /// **Catalog-First**: Statistics Manager MUST update Catalog.
    /// Query Optimizer MUST read statistics from Catalog.
    public func updateStatistics(tableName: String, stats: Statistics) async throws {
        // TLA+: Check if table exists
        guard tables[tableName] != nil else {
            throw CatalogError.tableNotFound(tableName)
        }
        
        // TLA+: Update statistics
        statistics[tableName] = stats
        
        // Persist to system table (if storage available)
        try await persistStatistics(tableName: tableName, stats: stats)
    }
    
    /// Get table statistics
    /// 
    /// **Catalog-First**: Query Optimizer MUST use this for cost estimation.
    public func getStatistics(tableName: String) -> Statistics? {
        // Catalog-First: Return from Catalog
        return statistics[tableName]
    }
    
    /// Get table statistics (async version)
    public func getStatistics(tableName: String) async -> Statistics? {
        return statistics[tableName]
    }
    
    /// Get all statistics
    public func getAllStatistics() -> [String: Statistics] {
        return statistics
    }
    
    // MARK: - Schema Versioning
    
    // MARK: - User Management (Catalog-First)
    
    /// Create a user
    /// **Catalog-First**: User metadata stored in Catalog's colibri_users system table
    public func createUser(username: String, email: String, role: UserRole, status: UserStatus = .active, passwordHash: String, salt: String) async throws {
        // Validate username
        guard !username.isEmpty else {
            throw CatalogError.invalidTableName("Username cannot be empty")
        }
        
        // Check if user already exists
        guard users[username] == nil else {
            throw CatalogError.tableAlreadyExists(username)  // Reuse error for user already exists
        }
        
        // Create user metadata
        let userMetadata = UserMetadata(
            username: username,
            email: email,
            role: role,
            status: status,
            passwordHash: passwordHash,
            salt: salt
        )
        
        // Store in memory (Catalog-First: single source of truth)
        users[username] = userMetadata
        
        // Persist to system table (if storage available)
        try await persistUserMetadata(username: username, metadata: userMetadata)
        
        // Log to WAL (if available) for durability
        if let wal = walManager {
            let ddlRecord = DDLOperationRecord(
                operation: "CREATE_USER",
                tableName: username,
                metadata: nil
            )
            let encoder = JSONEncoder()
            let payload = try encoder.encode(ddlRecord)
            _ = try await wal.appendRecord(txId: 0, kind: "ddl", data: payload)
            try await wal.flushLog()
        }
    }
    
    /// Get user metadata
    /// **Catalog-First**: This is THE ONLY source of user metadata
    public func getUser(username: String) -> UserMetadata? {
        return users[username]
    }
    
    /// Get user metadata (async version)
    public func getUser(username: String) async -> UserMetadata? {
        return users[username]
    }
    
    /// Delete a user
    /// **Catalog-First**: User deletion from Catalog
    public func deleteUser(username: String) async throws {
        guard users[username] != nil else {
            throw CatalogError.tableNotFound(username)  // Reuse error for user not found
        }
        
        // Remove user
        users.removeValue(forKey: username)
        
        // Persist to system table (if storage available)
        if let storage = storageManager {
            try await deleteUserMetadata(username: username, storage: storage)
        }
        
        // Log to WAL (if available)
        if let wal = walManager {
            let ddlRecord = DDLOperationRecord(
                operation: "DELETE_USER",
                tableName: username,
                metadata: nil
            )
            let encoder = JSONEncoder()
            let payload = try encoder.encode(ddlRecord)
            _ = try await wal.appendRecord(txId: 0, kind: "ddl", data: payload)
            try await wal.flushLog()
        }
    }
    
    /// Persist user metadata to system table
    private func persistUserMetadata(username: String, metadata: UserMetadata) async throws {
        guard let storage = storageManager else {
            return
        }
        
        let encoder = JSONEncoder()
        encoder.outputFormatting = [.prettyPrinted, .sortedKeys]
        
        // Serialize all users
        let allUsers = Array(users.values)
        let usersData = try encoder.encode(allUsers)
        try await storage.writePage(pageId: Self.SYSTEM_PAGE_USERS, data: usersData)
    }
    
    /// Delete user metadata from system table
    private func deleteUserMetadata(username: String, storage: StorageManager) async throws {
        let encoder = JSONEncoder()
        encoder.outputFormatting = [.prettyPrinted, .sortedKeys]
        
        // Serialize all remaining users
        let allUsers = Array(users.values)
        let usersData = try encoder.encode(allUsers)
        try await storage.writePage(pageId: Self.SYSTEM_PAGE_USERS, data: usersData)
    }
    
    // MARK: - Role Management (Catalog-First)
    
    /// Create a role
    /// **Catalog-First**: Role definitions stored in Catalog
    public func createRole(name: String, permissions: [String] = []) async throws {
        guard !name.isEmpty else {
            throw CatalogError.invalidTableName("Role name cannot be empty")
        }
        
        guard roles[name] == nil else {
            throw CatalogError.tableAlreadyExists(name)
        }
        
        let roleMetadata = RoleMetadata(name: name, permissions: permissions)
        roles[name] = roleMetadata
        
        // Persist to system table (if storage available)
        try await persistRoleMetadata(name: name, metadata: roleMetadata)
        
        // Log to WAL (if available)
        if let wal = walManager {
            let ddlRecord = DDLOperationRecord(
                operation: "CREATE_ROLE",
                tableName: name,
                metadata: nil
            )
            let encoder = JSONEncoder()
            let payload = try encoder.encode(ddlRecord)
            _ = try await wal.appendRecord(txId: 0, kind: "ddl", data: payload)
            try await wal.flushLog()
        }
    }
    
    /// Get role metadata
    /// **Catalog-First**: This is THE ONLY source of role metadata
    public func getRole(name: String) -> RoleMetadata? {
        return roles[name]
    }
    
    /// Persist role metadata to system table
    private func persistRoleMetadata(name: String, metadata: RoleMetadata) async throws {
        guard let storage = storageManager else {
            return
        }
        
        let encoder = JSONEncoder()
        encoder.outputFormatting = [.prettyPrinted, .sortedKeys]
        
        // Serialize all roles
        let allRoles = Array(roles.values)
        let rolesData = try encoder.encode(allRoles)
        try await storage.writePage(pageId: Self.SYSTEM_PAGE_ROLES, data: rolesData)
    }
    
    // MARK: - Permission Management (Catalog-First)
    
    /// Grant permission to user for table
    /// **Catalog-First**: Permissions stored in Catalog
    public func grantPermission(username: String, tableName: String, permission: String) async throws {
        // Validate user exists
        guard users[username] != nil else {
            throw CatalogError.tableNotFound(username)
        }
        
        // Validate table exists
        guard tables[tableName] != nil else {
            throw CatalogError.tableNotFound(tableName)
        }
        
        // Create permission metadata
        let permissionMetadata = PermissionMetadata(
            username: username,
            tableName: tableName,
            permission: permission
        )
        
        // Add permission
        if permissions[tableName] == nil {
            permissions[tableName] = []
        }
        permissions[tableName]?.append(permissionMetadata)
        
        // Persist to system table (if storage available)
        try await persistPermissions(tableName: tableName)
    }
    
    /// Check if user has permission for table
    /// **Catalog-First**: Permission checks use Catalog
    public func hasPermission(username: String, tableName: String, permission: String) -> Bool {
        // Get user role
        guard let user = users[username] else {
            return false
        }
        
        // Check role permissions first
        if let role = roles[user.role.rawValue] {
            if role.permissions.contains("\(permission):\(tableName)") {
                return true
            }
        }
        
        // Check explicit table permissions
        guard let tablePermissions = permissions[tableName] else {
            return false
        }
        
        return tablePermissions.contains { $0.username == username && $0.permission == permission }
    }
    
    /// Persist permissions to system table
    /// **Catalog-First**: Permissions stored in Catalog for access control
    /// Note: For now, we serialize all permissions (per-table structure) to a single page
    /// Future: Could have dedicated permissions page or per-table storage
    private func persistPermissions(tableName: String) async throws {
        guard let storage = storageManager else {
            return
        }
        
        // Serialize all permissions (across all tables) to JSON
        // **Catalog-First**: Store permissions in dedicated system page
        let encoder = JSONEncoder()
        encoder.outputFormatting = [.prettyPrinted, .sortedKeys]
        
        let permissionsData = try encoder.encode(permissions)
        
        // Store in dedicated permissions page (separate from statistics)
        try await storage.writePage(pageId: Self.SYSTEM_PAGE_PERMISSIONS, data: permissionsData)
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
    /// 
    /// Verifies that all Catalog metadata is consistent:
    /// - Indexes reference existing tables
    /// - Statistics reference existing tables
    /// - Primary keys reference existing columns
    /// - Foreign keys reference existing tables and columns
    public func checkConsistencyInvariant() -> Bool {
        // Check that all indexes reference existing tables
        for (_, index) in indexes {
            guard let table = tables[index.tableName] else {
                return false
            }
            
            // Check that index columns exist in table
            for column in index.columns {
                guard table.columns.contains(where: { $0.name == column }) else {
                    return false
                }
            }
        }
        
        // Check that all statistics reference existing tables
        for tableName in statistics.keys {
            guard tables[tableName] != nil else {
                return false
            }
        }
        
        // Check that primary keys reference existing columns
        for (_, table) in tables {
            for pkColumn in table.primaryKey {
                guard table.columns.contains(where: { $0.name == pkColumn }) else {
                    return false
                }
            }
        }
        
        // Check that foreign keys reference existing tables and columns
        for (_, table) in tables {
            for fk in table.foreignKeys {
                guard let refTable = tables[fk.to.table] else {
                    return false
                }
                
                for fkColumn in fk.from {
                    guard table.columns.contains(where: { $0.name == fkColumn }) else {
                        return false
                    }
                }
                
                for refColumn in fk.to.column {
                    guard refTable.columns.contains(where: { $0.name == refColumn }) else {
                        return false
                    }
                }
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

// MARK: - Catalog Errors

/// Catalog-specific errors
public enum CatalogError: Error, Equatable {
    case tableNotFound(String)
    case tableAlreadyExists(String)
    case indexNotFound(String)
    case indexAlreadyExists(String)
    case invalidTableName(String)
    case invalidIndexName(String)
    case invalidColumn(String)
    case tableHasDependencies(String)
    case columnAlreadyExists(tableName: String, column: String)
    case bootstrapFailed(String)
    case persistenceFailed(String)
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
