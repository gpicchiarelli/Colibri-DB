//
//  SQLExecutor.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-26.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: SQL statement executor for basic DDL/DML operations.

import Foundation

/// SQL Executor for executing parsed SQL statements
public final class SQLExecutor {
    private let database: Database
    
    public init(database: Database) {
        self.database = database
    }
    
    /// Executes a parsed SQL statement
    public func execute(_ statement: SimpleSQLStatement) throws {
        switch statement {
        case .createTable(let name, let columns):
            try executeCreateTable(name: name, columns: columns)
        case .dropTable(let name):
            try executeDropTable(name: name)
        case .insert(let table, let values):
            try executeInsert(table: table, values: values)
        case .select(let table, let columns):
            try executeSelect(table: table, columns: columns)
        case .delete(let table, let whereClause):
            try executeDelete(table: table, whereClause: whereClause)
        }
    }
    
    /// Executes CREATE TABLE statement
    private func executeCreateTable(name: String, columns: [String]) throws {
        // Convert column definitions to schema
        var columnDefinitions: [CatalogColumnDefinition] = []
        for column in columns {
            let parts = column.components(separatedBy: " ")
            let columnName = parts[0]
            let columnType = parts.count > 1 ? parts[1] : "string"
            
            let dataType: DataType
            switch columnType.uppercased() {
            case "INT", "INTEGER":
                dataType = .int
            case "STRING", "TEXT", "VARCHAR":
                dataType = .string
            case "DOUBLE", "FLOAT", "REAL":
                dataType = .double
            case "BOOL", "BOOLEAN":
                dataType = .boolean
            case "DATE", "TIMESTAMP":
                dataType = .date
            case "BLOB", "BINARY":
                dataType = .blob
            case "JSON":
                dataType = .json
            case "DECIMAL", "NUMERIC":
                dataType = .decimal
            default:
                dataType = .string
            }
            
            let columnDef = CatalogColumnDefinition(
                name: columnName,
                type: dataType,
                nullable: true,
                defaultValue: nil
            )
            columnDefinitions.append(columnDef)
        }
        
        let schema = CatalogTableSchema(columns: columnDefinitions)
        try database.createTable(name, in: "default", schema: schema)
    }
    
    /// Executes DROP TABLE statement
    private func executeDropTable(name: String) throws {
        try database.dropTable(name, in: "default")
    }
    
    /// Executes INSERT statement
    private func executeInsert(table: String, values: [String: String]) throws {
        var row: Row = [:]
        
        for (column, value) in values {
            let parsedValue = parseValue(value)
            row[column] = parsedValue
        }
        
        _ = try database.insert(into: table, row: row)
    }
    
    /// Executes SELECT statement
    private func executeSelect(table: String, columns: [String]?) throws {
        // For now, just print a message since select method doesn't exist
        print("SELECT not implemented yet")
    }
    
    /// Executes DELETE statement
    private func executeDelete(table: String, whereClause: String?) throws {
        // For now, just print a message since delete method doesn't exist
        print("DELETE not implemented yet")
    }
    
    /// Parses a string value into a Value
    private func parseValue(_ value: String) -> Value {
        // Handle NULL
        if value.uppercased() == "NULL" {
            return .null
        }
        
        // Handle quoted strings
        if value.hasPrefix("'") && value.hasSuffix("'") {
            let startIndex = value.index(after: value.startIndex)
            let endIndex = value.index(before: value.endIndex)
            return .string(String(value[startIndex..<endIndex]))
        }
        
        // Handle numbers
        if let intValue = Int64(value) {
            return .int(intValue)
        }
        
        if let doubleValue = Double(value) {
            return .double(doubleValue)
        }
        
        // Handle booleans
        if value.uppercased() == "TRUE" {
            return .bool(true)
        }
        if value.uppercased() == "FALSE" {
            return .bool(false)
        }
        
        // Default to string
        return .string(value)
    }
}
