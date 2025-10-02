//
//  ConstraintManager.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-09-26.
//
// ColibrDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Constraint manager for database-level constraint enforcement.

import Foundation

/// Manages constraints across all tables in the database
public final class ConstraintManager {
    private var tableSchemas: [String: TableSchema] = [:]
    private let lock = NSLock()
    
    public init() {}
    
    /// Registers a table schema with its constraints
    public func registerTable(_ schema: TableSchema) {
        lock.lock()
        defer { lock.unlock() }
        tableSchemas[schema.name] = schema
    }
    
    /// Unregisters a table schema
    public func unregisterTable(_ tableName: String) {
        lock.lock()
        defer { lock.unlock() }
        tableSchemas.removeValue(forKey: tableName)
    }
    
    /// Gets the schema for a table
    public func getSchema(for tableName: String) -> TableSchema? {
        lock.lock()
        defer { lock.unlock() }
        return tableSchemas[tableName]
    }
    
    /// Validates a row against all constraints for a table
    public func validateRow(_ row: Row, for tableName: String) throws -> [ConstraintValidationResult] {
        guard let schema = getSchema(for: tableName) else {
            return [] // No constraints if no schema
        }
        
        return try schema.validateRow(row)
    }
    
    /// Gets all constraint violations for a row
    public func getViolations(_ row: Row, for tableName: String) throws -> [String] {
        let results = try validateRow(row, for: tableName)
        return results.compactMap { result in
            switch result {
            case .valid: return nil
            case .violation(let message): return message
            }
        }
    }
    
    /// Validates a row and throws if there are violations
    public func enforceConstraints(_ row: Row, for tableName: String) throws {
        let violations = try getViolations(row, for: tableName)
        if !violations.isEmpty {
            throw DBError.constraintViolation("Constraint violations: \(violations.joined(separator: ", "))")
        }
    }
    
    /// Adds a constraint to an existing table
    public func addConstraint(_ constraint: Constraint, to tableName: String) throws {
        lock.lock()
        defer { lock.unlock() }
        
        guard let schema = tableSchemas[tableName] else {
            throw DBError.notFound("Table \(tableName) not found")
        }
        
        // Check for constraint name conflicts
        if schema.constraints.contains(where: { $0.name == constraint.name }) {
            throw DBError.conflict("Constraint '\(constraint.name)' already exists")
        }
        
        // Add the constraint
        var newConstraints = schema.constraints
        newConstraints.append(constraint)
        
        let newSchema = TableSchema(
            name: schema.name,
            columns: schema.columns,
            constraints: newConstraints,
            indexes: schema.indexes
        )
        
        tableSchemas[tableName] = newSchema
    }
    
    /// Removes a constraint from a table
    public func removeConstraint(_ constraintName: String, from tableName: String) throws {
        lock.lock()
        defer { lock.unlock() }
        
        guard let schema = tableSchemas[tableName] else {
            throw DBError.notFound("Table \(tableName) not found")
        }
        
        let newConstraints = schema.constraints.filter { $0.name != constraintName }
        
        if newConstraints.count == schema.constraints.count {
            throw DBError.notFound("Constraint '\(constraintName)' not found")
        }
        
        let newSchema = TableSchema(
            name: schema.name,
            columns: schema.columns,
            constraints: newConstraints,
            indexes: schema.indexes
        )
        
        tableSchemas[tableName] = newSchema
    }
    
    /// Gets all constraints for a table
    public func getConstraints(for tableName: String) -> [Constraint] {
        lock.lock()
        defer { lock.unlock() }
        return tableSchemas[tableName]?.constraints ?? []
    }
    
    /// Gets all primary key constraints
    public func getPrimaryKeys() -> [String: PrimaryKeyConstraint] {
        lock.lock()
        defer { lock.unlock() }
        
        var primaryKeys: [String: PrimaryKeyConstraint] = [:]
        for (tableName, schema) in tableSchemas {
            for constraint in schema.constraints {
                if let pk = constraint as? PrimaryKeyConstraint {
                    primaryKeys[tableName] = pk
                }
            }
        }
        return primaryKeys
    }
    
    /// Gets all unique constraints
    public func getUniqueConstraints() -> [String: [UniqueConstraint]] {
        lock.lock()
        defer { lock.unlock() }
        
        var uniqueConstraints: [String: [UniqueConstraint]] = [:]
        for (tableName, schema) in tableSchemas {
            let unique = schema.constraints.compactMap { $0 as? UniqueConstraint }
            if !unique.isEmpty {
                uniqueConstraints[tableName] = unique
            }
        }
        return uniqueConstraints
    }
    
    /// Gets all foreign key constraints
    public func getForeignKeys() -> [String: [ForeignKeyConstraint]] {
        lock.lock()
        defer { lock.unlock() }
        
        var foreignKeys: [String: [ForeignKeyConstraint]] = [:]
        for (tableName, schema) in tableSchemas {
            let fks = schema.constraints.compactMap { $0 as? ForeignKeyConstraint }
            if !fks.isEmpty {
                foreignKeys[tableName] = fks
            }
        }
        return foreignKeys
    }
    
    /// Validates all constraints for a table (useful for bulk operations)
    public func validateTable(_ tableName: String, rows: [(RID, Row)]) throws -> [String] {
        var allViolations: [String] = []
        
        for (rid, row) in rows {
            let violations = try getViolations(row, for: tableName)
            for violation in violations {
                allViolations.append("Row \(rid): \(violation)")
            }
        }
        
        return allViolations
    }
    
    /// Creates a default schema for a table (if no schema is provided)
    public func createDefaultSchema(for tableName: String, columns: [String]) -> TableSchema {
        let columnDefinitions = columns.map { ColumnDefinition(name: $0, type: "TEXT", isNullable: true) }
        return TableSchema(name: tableName, columns: columnDefinitions, constraints: [], indexes: [])
    }
    
    /// Updates a table schema
    public func updateSchema(_ schema: TableSchema) {
        lock.lock()
        defer { lock.unlock() }
        tableSchemas[schema.name] = schema
    }
    
    /// Gets all table names with schemas
    public func getTableNames() -> [String] {
        lock.lock()
        defer { lock.unlock() }
        return Array(tableSchemas.keys)
    }
    
    /// Clears all schemas (useful for testing)
    public func clearAll() {
        lock.lock()
        defer { lock.unlock() }
        tableSchemas.removeAll()
    }
}

/// Extension to add constraint-related errors
extension DBError {
    public static func constraintNotFound(_ message: String) -> DBError {
        return .notFound(message)
    }
}
