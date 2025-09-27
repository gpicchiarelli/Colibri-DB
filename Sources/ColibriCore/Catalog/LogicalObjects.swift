//
//  LogicalObjects.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Logical objects definitions for the catalog system.

import Foundation

// MARK: - Database Entry

/// Represents a database in the catalog
public struct DatabaseEntry {
    public let id: UUID
    public let name: String
    public let owner: String
    public let created: Date
    public let lastModified: Date
    public let status: DatabaseStatus
    public let defaultTablespace: String
    public let characterSet: String
    public let collation: String
    
    public init(id: UUID, name: String, owner: String, created: Date, lastModified: Date, 
                status: DatabaseStatus, defaultTablespace: String, characterSet: String, collation: String) {
        self.id = id
        self.name = name
        self.owner = owner
        self.created = created
        self.lastModified = lastModified
        self.status = status
        self.defaultTablespace = defaultTablespace
        self.characterSet = characterSet
        self.collation = collation
    }
}

public enum DatabaseStatus: String, CaseIterable {
    case active = "ACTIVE"
    case inactive = "INACTIVE"
    case maintenance = "MAINTENANCE"
    case dropped = "DROPPED"
}

// MARK: - Table Entry

/// Represents a table in the catalog
public struct TableEntry {
    public let id: UUID
    public let name: String
    public let database: String
    public let schema: CatalogTableSchema
    public let created: Date
    public let lastModified: Date
    public let status: TableStatus
    public let tablespace: String
    public let rowCount: UInt64
    public let sizeBytes: UInt64
    
    public init(id: UUID, name: String, database: String, schema: CatalogTableSchema, created: Date, 
                lastModified: Date, status: TableStatus, tablespace: String, rowCount: UInt64, sizeBytes: UInt64) {
        self.id = id
        self.name = name
        self.database = database
        self.schema = schema
        self.created = created
        self.lastModified = lastModified
        self.status = status
        self.tablespace = tablespace
        self.rowCount = rowCount
        self.sizeBytes = sizeBytes
    }
}

public enum TableStatus: String, CaseIterable {
    case active = "ACTIVE"
    case inactive = "INACTIVE"
    case maintenance = "MAINTENANCE"
    case dropped = "DROPPED"
}

// MARK: - Table Schema

/// Represents the schema of a table
public struct CatalogTableSchema {
    public let columns: [CatalogColumnDefinition]
    public let primaryKey: PrimaryKeyDefinition?
    public let uniqueKeys: [UniqueKeyDefinition]
    public let foreignKeys: [ForeignKeyDefinition]
    public let checkConstraints: [CheckConstraintDefinition]
    
    public init(columns: [CatalogColumnDefinition], primaryKey: PrimaryKeyDefinition? = nil, 
                uniqueKeys: [UniqueKeyDefinition] = [], foreignKeys: [ForeignKeyDefinition] = [], 
                checkConstraints: [CheckConstraintDefinition] = []) {
        self.columns = columns
        self.primaryKey = primaryKey
        self.uniqueKeys = uniqueKeys
        self.foreignKeys = foreignKeys
        self.checkConstraints = checkConstraints
    }
}

// MARK: - Column Definition

/// Represents a column definition in a table schema
public struct CatalogColumnDefinition {
    public let name: String
    public let type: DataType
    public let nullable: Bool
    public let defaultValue: Value?
    public let autoIncrement: Bool
    public let comment: String?
    
    public init(name: String, type: DataType, nullable: Bool = true, defaultValue: Value? = nil, 
                autoIncrement: Bool = false, comment: String? = nil) {
        self.name = name
        self.type = type
        self.nullable = nullable
        self.defaultValue = defaultValue
        self.autoIncrement = autoIncrement
        self.comment = comment
    }
}

// MARK: - Data Type

/// Represents a data type in the system
public enum DataType: String, CaseIterable {
    case string = "STRING"
    case int = "INT"
    case long = "LONG"
    case double = "DOUBLE"
    case decimal = "DECIMAL"
    case boolean = "BOOLEAN"
    case date = "DATE"
    case timestamp = "TIMESTAMP"
    case blob = "BLOB"
    case json = "JSON"
    case enumType = "ENUM"
    
    public var size: Int {
        switch self {
        case .string: return 0 // Variable length
        case .int: return 4
        case .long: return 8
        case .double: return 8
        case .decimal: return 16
        case .boolean: return 1
        case .date: return 8
        case .timestamp: return 8
        case .blob: return 0 // Variable length
        case .json: return 0 // Variable length
        case .enumType: return 4
        }
    }
}

// MARK: - Primary Key Definition

/// Represents a primary key definition
public struct PrimaryKeyDefinition {
    public let name: String
    public let columns: [String]
    public let clustered: Bool
    
    public init(name: String, columns: [String], clustered: Bool = true) {
        self.name = name
        self.columns = columns
        self.clustered = clustered
    }
}

// MARK: - Unique Key Definition

/// Represents a unique key definition
public struct UniqueKeyDefinition {
    public let name: String
    public let columns: [String]
    
    public init(name: String, columns: [String]) {
        self.name = name
        self.columns = columns
    }
}

// MARK: - Foreign Key Definition

/// Represents a foreign key definition
public struct ForeignKeyDefinition {
    public let name: String
    public let columns: [String]
    public let referencedTable: String
    public let referencedColumns: [String]
    public let onDelete: ForeignKeyAction
    public let onUpdate: ForeignKeyAction
    
    public init(name: String, columns: [String], referencedTable: String, referencedColumns: [String], 
                onDelete: ForeignKeyAction = .restrict, onUpdate: ForeignKeyAction = .restrict) {
        self.name = name
        self.columns = columns
        self.referencedTable = referencedTable
        self.referencedColumns = referencedColumns
        self.onDelete = onDelete
        self.onUpdate = onUpdate
    }
}

public enum ForeignKeyAction: String, CaseIterable {
    case restrict = "RESTRICT"
    case cascade = "CASCADE"
    case setNull = "SET NULL"
    case setDefault = "SET DEFAULT"
    case noAction = "NO ACTION"
}

// MARK: - Check Constraint Definition

/// Represents a check constraint definition
public struct CheckConstraintDefinition {
    public let name: String
    public let expression: String
    public let enabled: Bool
    
    public init(name: String, expression: String, enabled: Bool = true) {
        self.name = name
        self.expression = expression
        self.enabled = enabled
    }
}

// MARK: - Index Entry

/// Represents an index in the catalog
public struct IndexEntry {
    public let id: UUID
    public let name: String
    public let table: String
    public let database: String
    public let columns: [String]
    public let type: IndexType
    public let options: IndexOptions
    public let created: Date
    public let lastModified: Date
    public let status: IndexStatus
    public let sizeBytes: UInt64
    public let rowCount: UInt64
    
    public init(id: UUID, name: String, table: String, database: String, columns: [String], 
                type: IndexType, options: IndexOptions, created: Date, lastModified: Date, 
                status: IndexStatus, sizeBytes: UInt64, rowCount: UInt64) {
        self.id = id
        self.name = name
        self.table = table
        self.database = database
        self.columns = columns
        self.type = type
        self.options = options
        self.created = created
        self.lastModified = lastModified
        self.status = status
        self.sizeBytes = sizeBytes
        self.rowCount = rowCount
    }
}

public enum CatalogIndexType: String, CaseIterable {
    case btree = "BTREE"
    case hash = "HASH"
    case art = "ART"
    case lsm = "LSM"
    case skipList = "SKIPLIST"
    case fractalTree = "FRACTALTREE"
}

public enum IndexStatus: String, CaseIterable {
    case active = "ACTIVE"
    case building = "BUILDING"
    case rebuilding = "REBUILDING"
    case dropped = "DROPPED"
    case error = "ERROR"
}

// MARK: - Index Options

/// Represents options for index creation
public struct IndexOptions {
    public let unique: Bool
    public let clustered: Bool
    public let fillFactor: Int
    public let compression: CompressionType
    public let bloomFilter: Bool
    public let statistics: Bool
    
    public init(unique: Bool = false, clustered: Bool = false, fillFactor: Int = 100, 
                compression: CompressionType = .none, bloomFilter: Bool = false, statistics: Bool = true) {
        self.unique = unique
        self.clustered = clustered
        self.fillFactor = fillFactor
        self.compression = compression
        self.bloomFilter = bloomFilter
        self.statistics = statistics
    }
}

public enum CompressionType: String, CaseIterable {
    case none = "NONE"
    case lz4 = "LZ4"
    case zstd = "ZSTD"
    case gzip = "GZIP"
}

// MARK: - View Entry

/// Represents a view in the catalog
public struct ViewEntry {
    public let id: UUID
    public let name: String
    public let database: String
    public let definition: String
    public let created: Date
    public let lastModified: Date
    public let status: ViewStatus
    
    public init(id: UUID, name: String, database: String, definition: String, created: Date, 
                lastModified: Date, status: ViewStatus) {
        self.id = id
        self.name = name
        self.database = database
        self.definition = definition
        self.created = created
        self.lastModified = lastModified
        self.status = status
    }
}

public enum ViewStatus: String, CaseIterable {
    case active = "ACTIVE"
    case invalid = "INVALID"
    case dropped = "DROPPED"
}

// MARK: - Sequence Entry

/// Represents a sequence in the catalog
public struct SequenceEntry {
    public let id: UUID
    public let name: String
    public let database: String
    public let options: SequenceOptions
    public let currentValue: Int64
    public let created: Date
    public let lastModified: Date
    public let status: SequenceStatus
    
    public init(id: UUID, name: String, database: String, options: SequenceOptions, 
                currentValue: Int64, created: Date, lastModified: Date, status: SequenceStatus) {
        self.id = id
        self.name = name
        self.database = database
        self.options = options
        self.currentValue = currentValue
        self.created = created
        self.lastModified = lastModified
        self.status = status
    }
}

public enum SequenceStatus: String, CaseIterable {
    case active = "ACTIVE"
    case exhausted = "EXHAUSTED"
    case dropped = "DROPPED"
}

// MARK: - Sequence Options

/// Represents options for sequence creation
public struct SequenceOptions {
    public let startValue: Int64
    public let minValue: Int64
    public let maxValue: Int64
    public let increment: Int64
    public let cycle: Bool
    public let cache: Int
    
    public init(startValue: Int64 = 1, minValue: Int64 = 1, maxValue: Int64 = 9223372036854775807, 
                increment: Int64 = 1, cycle: Bool = false, cache: Int = 1) {
        self.startValue = startValue
        self.minValue = minValue
        self.maxValue = maxValue
        self.increment = increment
        self.cycle = cycle
        self.cache = cache
    }
}

// MARK: - Tablespace Entry

/// Represents a tablespace in the catalog
public struct TablespaceEntry {
    public let id: UUID
    public let name: String
    public let database: String
    public let path: String
    public let sizeBytes: UInt64
    public let maxSizeBytes: UInt64
    public let created: Date
    public let lastModified: Date
    public let status: TablespaceStatus
    
    public init(id: UUID, name: String, database: String, path: String, sizeBytes: UInt64, 
                maxSizeBytes: UInt64, created: Date, lastModified: Date, status: TablespaceStatus) {
        self.id = id
        self.name = name
        self.database = database
        self.path = path
        self.sizeBytes = sizeBytes
        self.maxSizeBytes = maxSizeBytes
        self.created = created
        self.lastModified = lastModified
        self.status = status
    }
}

public enum TablespaceStatus: String, CaseIterable {
    case active = "ACTIVE"
    case full = "FULL"
    case maintenance = "MAINTENANCE"
    case dropped = "DROPPED"
}
