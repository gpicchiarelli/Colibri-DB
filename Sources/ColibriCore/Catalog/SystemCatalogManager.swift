//
//  SystemCatalogManager.swift
//  System catalog manager that loads descriptors from sys_* tables and provides name resolution
//

import Foundation

// MARK: - Catalog Descriptors

/// Database descriptor loaded from sys_databases
public struct DatabaseDescriptor: Sendable, Equatable {
    public let databaseId: Int64
    public let name: String
    public let ownerUserId: Int64
    public let tablespaceId: Int64?
    public let isSystem: Bool
    public let createdAt: Date
    
    public init(databaseId: Int64, name: String, ownerUserId: Int64, tablespaceId: Int64?, isSystem: Bool, createdAt: Date) {
        self.databaseId = databaseId
        self.name = name
        self.ownerUserId = ownerUserId
        self.tablespaceId = tablespaceId
        self.isSystem = isSystem
        self.createdAt = createdAt
    }
}

/// Schema descriptor loaded from sys_schemas
public struct SchemaDescriptor: Sendable, Equatable {
    public let schemaId: Int64
    public let databaseId: Int64
    public let name: String
    public let ownerUserId: Int64
    public let createdAt: Date
    
    public init(schemaId: Int64, databaseId: Int64, name: String, ownerUserId: Int64, createdAt: Date) {
        self.schemaId = schemaId
        self.databaseId = databaseId
        self.name = name
        self.ownerUserId = ownerUserId
        self.createdAt = createdAt
    }
}

/// Table descriptor loaded from sys_tables
public struct TableDescriptor: Sendable, Equatable {
    public let tableId: Int64
    public let schemaId: Int64
    public let name: String
    public let ownerUserId: Int64
    public let kind: TableKind
    public let createdAt: Date
    
    public enum TableKind: String, Sendable {
        case base = "BASE"
        case view = "VIEW"
        case matView = "MATVIEW"
        case sys = "SYS"
    }
    
    public init(tableId: Int64, schemaId: Int64, name: String, ownerUserId: Int64, kind: TableKind, createdAt: Date) {
        self.tableId = tableId
        self.schemaId = schemaId
        self.name = name
        self.ownerUserId = ownerUserId
        self.kind = kind
        self.createdAt = createdAt
    }
}

/// Column descriptor loaded from sys_columns
public struct ColumnDescriptor: Sendable, Equatable {
    public let columnId: Int64
    public let tableId: Int64
    public let name: String
    public let ordinal: Int
    public let dataType: String
    public let nullable: Bool
    public let defaultExpr: String?
    public let collation: String?
    public let generatedKind: String?
    
    public init(columnId: Int64, tableId: Int64, name: String, ordinal: Int, dataType: String, nullable: Bool, defaultExpr: String?, collation: String?, generatedKind: String?) {
        self.columnId = columnId
        self.tableId = tableId
        self.name = name
        self.ordinal = ordinal
        self.dataType = dataType
        self.nullable = nullable
        self.defaultExpr = defaultExpr
        self.collation = collation
        self.generatedKind = generatedKind
    }
}

/// Index descriptor loaded from sys_indexes + sys_index_columns
public struct IndexDescriptor: Sendable, Equatable {
    public let indexId: Int64
    public let tableId: Int64
    public let name: String
    public let isUnique: Bool
    public let isPrimary: Bool
    public let method: String
    public let columns: [IndexColumn]
    
    public struct IndexColumn: Sendable, Equatable {
        public let columnId: Int64
        public let ordinal: Int
        public let order: String // ASC/DESC
        public let nulls: String // FIRST/LAST
    }
    
    public init(indexId: Int64, tableId: Int64, name: String, isUnique: Bool, isPrimary: Bool, method: String, columns: [IndexColumn]) {
        self.indexId = indexId
        self.tableId = tableId
        self.name = name
        self.isUnique = isUnique
        self.isPrimary = isPrimary
        self.method = method
        self.columns = columns
    }
}

/// Constraint descriptor loaded from sys_constraints + sys_constraint_columns
public struct ConstraintDescriptor: Sendable, Equatable {
    public let constraintId: Int64
    public let tableId: Int64
    public let name: String
    public let type: ConstraintType
    public let columns: [Int64] // column_ids in order
    public let refTableId: Int64?
    public let refColumns: [Int64]?
    public let checkExpr: String?
    public let matchType: String?
    public let onUpdate: String?
    public let onDelete: String?
    
    public enum ConstraintType: String, Sendable {
        case primaryKey = "PRIMARY KEY"
        case unique = "UNIQUE"
        case foreignKey = "FOREIGN KEY"
        case check = "CHECK"
        case notNull = "NOT NULL"
    }
    
    public init(constraintId: Int64, tableId: Int64, name: String, type: ConstraintType, columns: [Int64], refTableId: Int64?, refColumns: [Int64]?, checkExpr: String?, matchType: String?, onUpdate: String?, onDelete: String?) {
        self.constraintId = constraintId
        self.tableId = tableId
        self.name = name
        self.type = type
        self.columns = columns
        self.refTableId = refTableId
        self.refColumns = refColumns
        self.checkExpr = checkExpr
        self.matchType = matchType
        self.onUpdate = onUpdate
        self.onDelete = onDelete
    }
}

// MARK: - System Catalog Manager

/// System catalog manager: loads descriptors from sys_* tables and provides name resolution
public actor SystemCatalogManager {
    private let db: ColibrìDB
    private let schema = "colibri_sys"
    
    // In-memory descriptor caches (keyed by IDs)
    private var databases: [Int64: DatabaseDescriptor] = [:]
    private var schemas: [Int64: SchemaDescriptor] = [:]
    private var tables: [Int64: TableDescriptor] = [:]
    private var columns: [Int64: ColumnDescriptor] = [:]
    private var indexes: [Int64: IndexDescriptor] = [:]
    private var constraints: [Int64: ConstraintDescriptor] = [:]
    
    // Name-based indexes for fast resolution
    private var databaseByName: [String: Int64] = [:]
    private var schemaByDatabaseAndName: [Int64: [String: Int64]] = [:]
    private var tableBySchemaAndName: [Int64: [String: Int64]] = [:]
    private var columnByTableAndName: [Int64: [String: Int64]] = [:]
    private var indexByTableAndName: [Int64: [String: Int64]] = [:]
    private var constraintByTableAndName: [Int64: [String: Int64]] = [:]
    
    public init(database: ColibrìDB) {
        self.db = database
    }
    
    /// Load all catalog descriptors from sys_* tables at startup
    public func loadAll() async throws {
        let tx = try await db.beginTransaction()
        defer { Task { try? await db.abort(txId: tx) } }
        
        // Load in dependency order: databases → schemas → tables → columns → indexes → constraints
        try await loadDatabases(txId: tx)
        try await loadSchemas(txId: tx)
        try await loadTables(txId: tx)
        try await loadColumns(txId: tx)
        try await loadIndexes(txId: tx)
        try await loadConstraints(txId: tx)
    }
    
    // MARK: - Loading Methods
    
    private func loadDatabases(txId: TxID) async throws {
        let sql = "SELECT database_id, name, owner_user_id, tablespace_id, is_system, created_at FROM \(schema).sys_databases;"
        let result = try await db.executeQuery(sql, txId: txId)
        
        for row in result.rows {
            guard
                let dbId = extractInt64(row["database_id"]),
                let name = extractString(row["name"]),
                let ownerId = extractInt64(row["owner_user_id"]),
                let createdAt = extractDate(row["created_at"]),
                let isSystem = extractBool(row["is_system"])
            else { continue }
            
            let tablespaceId = extractInt64(row["tablespace_id"])
            let desc = DatabaseDescriptor(
                databaseId: dbId,
                name: name,
                ownerUserId: ownerId,
                tablespaceId: tablespaceId,
                isSystem: isSystem != 0,
                createdAt: createdAt
            )
            databases[dbId] = desc
            databaseByName[name] = dbId
        }
    }
    
    private func loadSchemas(txId: TxID) async throws {
        let sql = "SELECT schema_id, database_id, name, owner_user_id, created_at FROM \(schema).sys_schemas;"
        let result = try await db.executeQuery(sql, txId: txId)
        
        for row in result.rows {
            guard
                let schemaId = extractInt64(row["schema_id"]),
                let dbId = extractInt64(row["database_id"]),
                let name = extractString(row["name"]),
                let ownerId = extractInt64(row["owner_user_id"]),
                let createdAt = extractDate(row["created_at"])
            else { continue }
            
            let desc = SchemaDescriptor(
                schemaId: schemaId,
                databaseId: dbId,
                name: name,
                ownerUserId: ownerId,
                createdAt: createdAt
            )
            schemas[schemaId] = desc
            schemaByDatabaseAndName[dbId, default: [:]][name] = schemaId
        }
    }
    
    private func loadTables(txId: TxID) async throws {
        let sql = "SELECT table_id, schema_id, name, owner_user_id, table_kind, created_at FROM \(schema).sys_tables;"
        let result = try await db.executeQuery(sql, txId: txId)
        
        for row in result.rows {
            guard
                let tableId = extractInt64(row["table_id"]),
                let schemaId = extractInt64(row["schema_id"]),
                let name = extractString(row["name"]),
                let ownerId = extractInt64(row["owner_user_id"]),
                let kindStr = extractString(row["table_kind"]),
                let kind = TableDescriptor.TableKind(rawValue: kindStr),
                let createdAt = extractDate(row["created_at"])
            else { continue }
            
            let desc = TableDescriptor(
                tableId: tableId,
                schemaId: schemaId,
                name: name,
                ownerUserId: ownerId,
                kind: kind,
                createdAt: createdAt
            )
            tables[tableId] = desc
            tableBySchemaAndName[schemaId, default: [:]][name] = tableId
        }
    }
    
    private func loadColumns(txId: TxID) async throws {
        let sql = "SELECT column_id, table_id, name, ordinal, data_type, nullable, default_expr, collation, generated_kind FROM \(schema).sys_columns ORDER BY table_id, ordinal;"
        let result = try await db.executeQuery(sql, txId: txId)
        
        for row in result.rows {
            guard
                let colId = extractInt64(row["column_id"]),
                let tableId = extractInt64(row["table_id"]),
                let name = extractString(row["name"]),
                let ordinal = extractInt(row["ordinal"]),
                let dataType = extractString(row["data_type"]),
                let nullable = extractBool(row["nullable"])
            else { continue }
            
            let desc = ColumnDescriptor(
                columnId: colId,
                tableId: tableId,
                name: name,
                ordinal: ordinal,
                dataType: dataType,
                nullable: nullable != 0,
                defaultExpr: extractString(row["default_expr"]),
                collation: extractString(row["collation"]),
                generatedKind: extractString(row["generated_kind"])
            )
            columns[colId] = desc
            columnByTableAndName[tableId, default: [:]][name] = colId
        }
    }
    
    private func loadIndexes(txId: TxID) async throws {
        // First load index definitions
        let sql1 = "SELECT index_id, table_id, name, is_unique, is_primary, method FROM \(schema).sys_indexes;"
        let result1 = try await db.executeQuery(sql1, txId: txId)
        
        var indexDefs: [Int64: (tableId: Int64, name: String, isUnique: Bool, isPrimary: Bool, method: String)] = [:]
        for row in result1.rows {
            guard
                let idxId = extractInt64(row["index_id"]),
                let tableId = extractInt64(row["table_id"]),
                let name = extractString(row["name"]),
                let isUnique = extractBool(row["is_unique"]),
                let isPrimary = extractBool(row["is_primary"]),
                let method = extractString(row["method"])
            else { continue }
            
            indexDefs[idxId] = (tableId, name, isUnique != 0, isPrimary != 0, method)
            indexByTableAndName[tableId, default: [:]][name] = idxId
        }
        
        // Then load index columns
        let sql2 = "SELECT index_id, column_id, ordinal, \"order\", nulls FROM \(schema).sys_index_columns ORDER BY index_id, ordinal;"
        let result2 = try await db.executeQuery(sql2, txId: txId)
        
        var indexColumns: [Int64: [IndexDescriptor.IndexColumn]] = [:]
        for row in result2.rows {
            guard
                let idxId = extractInt64(row["index_id"]),
                let colId = extractInt64(row["column_id"]),
                let ordinal = extractInt(row["ordinal"]),
                let order = extractString(row["order"]),
                let nulls = extractString(row["nulls"])
            else { continue }
            
            indexColumns[idxId, default: []].append(
                IndexDescriptor.IndexColumn(columnId: colId, ordinal: ordinal, order: order, nulls: nulls)
            )
        }
        
        // Combine into descriptors
        for (idxId, def) in indexDefs {
            let cols = indexColumns[idxId] ?? []
            indexes[idxId] = IndexDescriptor(
                indexId: idxId,
                tableId: def.tableId,
                name: def.name,
                isUnique: def.isUnique,
                isPrimary: def.isPrimary,
                method: def.method,
                columns: cols.sorted { $0.ordinal < $1.ordinal }
            )
        }
    }
    
    private func loadConstraints(txId: TxID) async throws {
        // Load constraint definitions
        let sql1 = "SELECT constraint_id, table_id, name, constraint_type, check_expr, referenced_table_id, match_type, on_update, on_delete FROM \(schema).sys_constraints;"
        let result1 = try await db.executeQuery(sql1, txId: txId)
        
        var constraintDefs: [Int64: (tableId: Int64, name: String, type: ConstraintDescriptor.ConstraintType, checkExpr: String?, refTableId: Int64?, matchType: String?, onUpdate: String?, onDelete: String?)] = [:]
        for row in result1.rows {
            guard
                let constId = extractInt64(row["constraint_id"]),
                let tableId = extractInt64(row["table_id"]),
                let name = extractString(row["name"]),
                let typeStr = extractString(row["constraint_type"]),
                let type = ConstraintDescriptor.ConstraintType(rawValue: typeStr)
            else { continue }
            
            constraintDefs[constId] = (
                tableId,
                name,
                type,
                extractString(row["check_expr"]),
                extractInt64(row["referenced_table_id"]),
                extractString(row["match_type"]),
                extractString(row["on_update"]),
                extractString(row["on_delete"])
            )
            constraintByTableAndName[tableId, default: [:]][name] = constId
        }
        
        // Load constraint columns
        let sql2 = "SELECT constraint_id, column_id, ordinal, referenced_column_id FROM \(schema).sys_constraint_columns ORDER BY constraint_id, ordinal;"
        let result2 = try await db.executeQuery(sql2, txId: txId)
        
        var constraintCols: [Int64: [Int64]] = [:]
        var constraintRefCols: [Int64: [Int64]] = [:]
        for row in result2.rows {
            guard
                let constId = extractInt64(row["constraint_id"]),
                let colId = extractInt64(row["column_id"]),
                let ordinal = extractInt(row["ordinal"])
            else { continue }
            
            var cols = constraintCols[constId] ?? []
            while cols.count < ordinal {
                cols.append(0) // Placeholder
            }
            if cols.count == ordinal {
                cols.append(colId)
            } else {
                cols[ordinal] = colId
            }
            constraintCols[constId] = cols
            
            if let refColId = extractInt64(row["referenced_column_id"]) {
                var refCols = constraintRefCols[constId] ?? []
                while refCols.count < ordinal {
                    refCols.append(0)
                }
                if refCols.count == ordinal {
                    refCols.append(refColId)
                } else {
                    refCols[ordinal] = refColId
                }
                constraintRefCols[constId] = refCols
            }
        }
        
        // Combine into descriptors
        for (constId, def) in constraintDefs {
            let cols = constraintCols[constId]?.filter { $0 != 0 } ?? []
            let refCols: [Int64]? = {
                guard let arr = constraintRefCols[constId] else { return nil }
                let filtered = arr.filter { $0 != 0 }
                return filtered.isEmpty ? nil : filtered
            }()
            constraints[constId] = ConstraintDescriptor(
                constraintId: constId,
                tableId: def.tableId,
                name: def.name,
                type: def.type,
                columns: cols,
                refTableId: def.refTableId,
                refColumns: refCols,
                checkExpr: def.checkExpr,
                matchType: def.matchType,
                onUpdate: def.onUpdate,
                onDelete: def.onDelete
            )
        }
    }
    
    // MARK: - Name Resolution
    
    /// Resolve database.schema.table to table_id
    public func resolveTable(database: String?, schema: String?, table: String) throws -> Int64? {
        var dbId: Int64?
        if let dbName = database {
            dbId = databaseByName[dbName]
            guard dbId != nil else { return nil }
        } else {
            // Default to first database (or system database)
            dbId = databaseByName["colibri_sys"] ?? databases.keys.first
        }
        
        guard let databaseId = dbId else { return nil }
        
        var schemaId: Int64?
        if let schemaName = schema {
            schemaId = schemaByDatabaseAndName[databaseId]?[schemaName]
            guard schemaId != nil else { return nil }
        } else {
            // Default to first schema in database
            schemaId = schemas.values.first(where: { $0.databaseId == databaseId })?.schemaId
        }
        
        guard let resolvedSchemaId = schemaId else { return nil }
        return tableBySchemaAndName[resolvedSchemaId]?[table]
    }
    
    /// Get table descriptor by ID
    public func getTable(byId tableId: Int64) -> TableDescriptor? {
        return tables[tableId]
    }
    
    /// Get columns for a table
    public func getColumns(forTableId tableId: Int64) -> [ColumnDescriptor] {
        return columns.values.filter { $0.tableId == tableId }.sorted { $0.ordinal < $1.ordinal }
    }
    
    /// Get indexes for a table
    public func getIndexes(forTableId tableId: Int64) -> [IndexDescriptor] {
        return indexes.values.filter { $0.tableId == tableId }
    }
    
    /// Get constraints for a table
    public func getConstraints(forTableId tableId: Int64) -> [ConstraintDescriptor] {
        return constraints.values.filter { $0.tableId == tableId }
    }
    
    // MARK: - Helper Extractors
    
    private func extractInt64(_ value: Value?) -> Int64? {
        guard let v = value, case .int(let i) = v else { return nil }
        return i
    }
    
    private func extractString(_ value: Value?) -> String? {
        guard let v = value, case .string(let s) = v else { return nil }
        return s
    }
    
    private func extractInt(_ value: Value?) -> Int? {
        guard let i64 = extractInt64(value) else { return nil }
        return Int(i64)
    }
    
    private func extractBool(_ value: Value?) -> Int? {
        guard let v = value, case .bool(let b) = v else {
            // Also support integer 0/1
            if let i = extractInt(value) { return i }
            return nil
        }
        return b ? 1 : 0
    }
    
    private func extractDate(_ value: Value?) -> Date? {
        guard let v = value else { return nil }
        switch v {
        case .date(let d): return d
        case .double(let ts): return Date(timeIntervalSince1970: ts)
        default: return nil
        }
    }
}

