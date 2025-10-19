//
//  SchemaEvolution.swift
//  Based on: spec/SchemaEvolution.tla
//

import Foundation

public enum SchemaChangeType {
    case addColumn
    case dropColumn
    case alterColumn
    case renameColumn
    case addIndex
    case dropIndex
}

public struct SchemaChange {
    public let id: UUID
    public let type: SchemaChangeType
    public let table: String
    public let details: [String: Any]
    public let appliedAt: Date
    public let version: Int
    
    public init(type: SchemaChangeType, table: String, details: [String: Any], version: Int) {
        self.id = UUID()
        self.type = type
        self.table = table
        self.details = details
        self.appliedAt = Date()
        self.version = version
    }
}

public actor SchemaEvolutionManager {
    private var schemaVersion: Int = 1
    private var changeHistory: [SchemaChange] = []
    private let catalog: Catalog
    
    public init(catalog: Catalog) {
        self.catalog = catalog
    }
    
    public func addColumn(table: String, column: ColumnDefinition) async throws {
        guard var tableDefinition = await catalog.getTable(table) else {
            throw DBError.notFound
        }
        
        var newColumns = tableDefinition.columns
        newColumns.append(column)
        
        let newTableDef = TableDefinition(
            name: tableDefinition.name,
            columns: newColumns,
            primaryKey: tableDefinition.primaryKey,
            indexes: tableDefinition.indexes
        )
        
        try await catalog.dropTable(table)
        try await catalog.createTable(newTableDef)
        
        schemaVersion += 1
        
        let change = SchemaChange(
            type: .addColumn,
            table: table,
            details: ["column": column.name],
            version: schemaVersion
        )
        changeHistory.append(change)
    }
    
    public func dropColumn(table: String, columnName: String) async throws {
        guard var tableDefinition = await catalog.getTable(table) else {
            throw DBError.notFound
        }
        
        let newColumns = tableDefinition.columns.filter { $0.name != columnName }
        
        let newTableDef = TableDefinition(
            name: tableDefinition.name,
            columns: newColumns,
            primaryKey: tableDefinition.primaryKey,
            indexes: tableDefinition.indexes
        )
        
        try await catalog.dropTable(table)
        try await catalog.createTable(newTableDef)
        
        schemaVersion += 1
        
        let change = SchemaChange(
            type: .dropColumn,
            table: table,
            details: ["column": columnName],
            version: schemaVersion
        )
        changeHistory.append(change)
    }
    
    public func getSchemaVersion() -> Int {
        return schemaVersion
    }
    
    public func getChangeHistory() -> [SchemaChange] {
        return changeHistory
    }
}

