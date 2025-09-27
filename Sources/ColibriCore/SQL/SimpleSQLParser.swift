//
//  SimpleSQLParser.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-26.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Simplified SQL parser for basic DDL/DML operations.

import Foundation

/// Simple SQL statement types
public enum SimpleSQLStatement {
    case createTable(name: String, columns: [String])
    case dropTable(name: String)
    case insert(table: String, values: [String: String])
    case select(table: String, columns: [String]?)
    case delete(table: String, whereClause: String?)
}

/// Simple SQL Parser
public final class SimpleSQLParser {
    private let sql: String
    
    public init(sql: String) {
        self.sql = sql.trimmingCharacters(in: .whitespacesAndNewlines)
    }
    
    /// Parses the SQL statement
    public func parse() throws -> SimpleSQLStatement {
        let tokens = sql.components(separatedBy: .whitespacesAndNewlines).filter { !$0.isEmpty }
        guard !tokens.isEmpty else {
            throw SimpleSQLParseError.emptyStatement
        }
        
        let command = tokens[0].uppercased()
        
        switch command {
        case "CREATE":
            return try parseCreate(tokens)
        case "DROP":
            return try parseDrop(tokens)
        case "INSERT":
            return try parseInsert(tokens)
        case "SELECT":
            return try parseSelect(tokens)
        case "DELETE":
            return try parseDelete(tokens)
        default:
            throw SimpleSQLParseError.unsupportedCommand(command)
        }
    }
    
    private func parseCreate(_ tokens: [String]) throws -> SimpleSQLStatement {
        guard tokens.count >= 3 && tokens[1].uppercased() == "TABLE" else {
            throw SimpleSQLParseError.invalidSyntax("Expected CREATE TABLE")
        }
        
        let tableName = tokens[2]
        return .createTable(name: tableName, columns: [])
    }
    
    private func parseDrop(_ tokens: [String]) throws -> SimpleSQLStatement {
        guard tokens.count >= 3 && tokens[1].uppercased() == "TABLE" else {
            throw SimpleSQLParseError.invalidSyntax("Expected DROP TABLE")
        }
        
        let tableName = tokens[2]
        return .dropTable(name: tableName)
    }
    
    private func parseInsert(_ tokens: [String]) throws -> SimpleSQLStatement {
        guard tokens.count >= 4 && tokens[1].uppercased() == "INTO" else {
            throw SimpleSQLParseError.invalidSyntax("Expected INSERT INTO")
        }
        
        let tableName = tokens[2]
        
        // Simple VALUES parsing - expects VALUES (col1=val1, col2=val2, ...)
        var values: [String: String] = [:]
        
        if tokens.count > 3 && tokens[3].uppercased() == "VALUES" {
            let valuesString = tokens.dropFirst(4).joined(separator: " ")
            let pairs = valuesString.components(separatedBy: ",")
            
            for pair in pairs {
                let trimmed = pair.trimmingCharacters(in: .whitespaces)
                if trimmed.contains("=") {
                    let parts = trimmed.components(separatedBy: "=")
                    if parts.count == 2 {
                        let key = parts[0].trimmingCharacters(in: .whitespaces)
                        let value = parts[1].trimmingCharacters(in: .whitespaces)
                        values[key] = value
                    }
                }
            }
        }
        
        return .insert(table: tableName, values: values)
    }
    
    private func parseSelect(_ tokens: [String]) throws -> SimpleSQLStatement {
        guard tokens.count >= 4 && tokens[1].uppercased() == "FROM" else {
            throw SimpleSQLParseError.invalidSyntax("Expected SELECT ... FROM")
        }
        
        let tableName = tokens[3]
        let columns: [String]? = tokens[1] == "*" ? nil : [tokens[1]]
        
        return .select(table: tableName, columns: columns)
    }
    
    private func parseDelete(_ tokens: [String]) throws -> SimpleSQLStatement {
        guard tokens.count >= 3 && tokens[1].uppercased() == "FROM" else {
            throw SimpleSQLParseError.invalidSyntax("Expected DELETE FROM")
        }
        
        let tableName = tokens[2]
        let whereClause: String? = tokens.count > 3 ? tokens.dropFirst(3).joined(separator: " ") : nil
        
        return .delete(table: tableName, whereClause: whereClause)
    }
}

/// Simple SQL Parse Errors
public enum SimpleSQLParseError: Error, CustomStringConvertible {
    case emptyStatement
    case unsupportedCommand(String)
    case invalidSyntax(String)
    
    public var description: String {
        switch self {
        case .emptyStatement:
            return "Empty SQL statement"
        case .unsupportedCommand(let cmd):
            return "Unsupported command: \(cmd)"
        case .invalidSyntax(let msg):
            return "Invalid syntax: \(msg)"
        }
    }
}

/// Simple SQL Executor
public final class SimpleSQLExecutor {
    private let database: Database
    
    public init(database: Database) {
        self.database = database
    }
    
    /// Executes a simple SQL statement
    public func execute(_ statement: SimpleSQLStatement) throws -> String {
        switch statement {
        case .createTable(let name, _):
            try database.createTable(name)
            return "Table '\(name)' created successfully"
            
        case .dropTable(let name):
            try database.dropTable(name)
            return "Table '\(name)' dropped successfully"
            
        case .insert(let table, let values):
            let row = parseValuesToRow(values)
            let _ = try database.insert(into: table, row: row)
            return "1 row inserted into '\(table)'"
            
        case .select(let table, let columns):
            let rows = try database.scan(table)
            return formatSelectResults(rows, columns: columns)
            
        case .delete(let table, let whereClause):
            // Simplified delete - delete all rows
            let rows = try database.scan(table)
            var deletedCount = 0
            
            for (_, row) in rows {
                // Simple WHERE clause parsing - expects "column=value"
                if let whereClause = whereClause {
                    if whereClause.contains("=") {
                        let parts = whereClause.components(separatedBy: "=")
                        if parts.count == 2 {
                            let column = parts[0].trimmingCharacters(in: .whitespaces)
                            let value = parts[1].trimmingCharacters(in: .whitespaces)
                            if row[column]?.description == value {
                                _ = try database.deleteEquals(table: table, column: column, value: parseValue(value))
                                deletedCount += 1
                            }
                        }
                    }
                } else {
                    // Delete all rows
                    _ = try database.deleteEquals(table: table, column: "id", value: row["id"] ?? .null)
                    deletedCount += 1
                }
            }
            
            return "\(deletedCount) rows deleted from '\(table)'"
        }
    }
    
    private func parseValuesToRow(_ values: [String: String]) -> Row {
        var row: Row = [:]
        
        for (key, value) in values {
            row[key] = parseValue(value)
        }
        
        return row
    }
    
    private func parseValue(_ value: String) -> Value {
        if value.uppercased() == "NULL" {
            return .null
        } else if value.uppercased() == "TRUE" {
            return .bool(true)
        } else if value.uppercased() == "FALSE" {
            return .bool(false)
        } else if let intValue = Int64(value) {
            return .int(intValue)
        } else if let doubleValue = Double(value) {
            return .double(doubleValue)
        } else {
            return .string(value)
        }
    }
    
    private func formatSelectResults(_ rows: [(RID, Row)], columns: [String]?) -> String {
        if rows.isEmpty {
            return "No rows found"
        }
        
        let allColumns = columns ?? Array(rows.first!.1.keys).sorted()
        var result = ""
        
        // Header
        result += allColumns.joined(separator: " | ") + "\n"
        result += String(repeating: "-", count: allColumns.joined(separator: " | ").count) + "\n"
        
        // Rows
        for (_, row) in rows {
            let values = allColumns.map { column in
                let value = row[column] ?? .null
                return formatValueForDisplay(value)
            }
            result += values.joined(separator: " | ") + "\n"
        }
        
        result += "\n(\(rows.count) rows)"
        return result
    }
    
    private func formatValueForDisplay(_ value: Value) -> String {
        switch value {
        case .string(let s): return s
        case .int(let i): return String(i)
        case .double(let d): return String(d)
        case .bool(let b): return b ? "true" : "false"
        case .null: return "NULL"
        case .date(let d): return ISO8601DateFormatter().string(from: d)
        case .decimal(let d): return d.description
        case .blob(let d): return "<BLOB:\(d.count) bytes>"
        case .json(let d): return String(data: d, encoding: .utf8) ?? "<INVALID JSON>"
        case .enumValue(let enumName, let value): return "\(enumName).\(value)"
        }
    }
}
