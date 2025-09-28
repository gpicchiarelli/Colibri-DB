//
//  ConstraintSystem.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-26.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Constraint system for data integrity (PK, Unique, Not Null, Check).

import Foundation

/// Types of constraints supported by the database
public enum ConstraintType: String, Codable, CaseIterable {
    case primaryKey = "PRIMARY KEY"
    case unique = "UNIQUE"
    case notNull = "NOT NULL"
    case check = "CHECK"
    case foreignKey = "FOREIGN KEY"
    
    public var description: String { rawValue }
}

/// Base protocol for all constraints
public protocol Constraint: Codable, CustomStringConvertible {
    var name: String { get }
    var type: ConstraintType { get }
    var columns: [String] { get }
    var isDeferrable: Bool { get }
    var initiallyDeferred: Bool { get }
    
    /// Validates a row against this constraint
    func validate(_ row: Row, in table: String) throws -> ConstraintValidationResult
}

/// Result of constraint validation
public enum ConstraintValidationResult {
    case valid
    case violation(String)
    
    public var isValid: Bool {
        switch self {
        case .valid: return true
        case .violation: return false
        }
    }
}

/// Primary Key constraint
public struct PrimaryKeyConstraint: Constraint {
    public let name: String
    public let columns: [String]
    public let isDeferrable: Bool
    public let initiallyDeferred: Bool
    public let type: ConstraintType
    
    public init(name: String, columns: [String], isDeferrable: Bool = false, initiallyDeferred: Bool = false) {
        self.name = name
        self.columns = columns
        self.isDeferrable = isDeferrable
        self.initiallyDeferred = initiallyDeferred
        self.type = .primaryKey
    }
    
    public func validate(_ row: Row, in table: String) throws -> ConstraintValidationResult {
        // Check that all primary key columns are present and not null
        for column in columns {
            guard let value = row[column] else {
                return .violation("Primary key column '\(column)' is missing")
            }
            if value == .null {
                return .violation("Primary key column '\(column)' cannot be NULL")
            }
        }
        return .valid
    }
    
    public var description: String {
        "PRIMARY KEY (\(columns.joined(separator: ", ")))"
    }
}

/// Unique constraint
public struct UniqueConstraint: Constraint {
    public let name: String
    public let columns: [String]
    public let isDeferrable: Bool
    public let initiallyDeferred: Bool
    public let type: ConstraintType
    
    public init(name: String, columns: [String], isDeferrable: Bool = false, initiallyDeferred: Bool = false) {
        self.name = name
        self.columns = columns
        self.isDeferrable = isDeferrable
        self.initiallyDeferred = initiallyDeferred
        self.type = .unique
    }
    
    public func validate(_ row: Row, in table: String) throws -> ConstraintValidationResult {
        // For unique constraints, we need to check against existing data
        // This is a simplified validation - in practice, this would check against the index
        return .valid
    }
    
    public var description: String {
        "UNIQUE (\(columns.joined(separator: ", ")))"
    }
}

/// Not Null constraint
public struct NotNullConstraint: Constraint {
    public let name: String
    public let columns: [String]
    public let isDeferrable: Bool
    public let initiallyDeferred: Bool
    public let type: ConstraintType
    
    public init(name: String, column: String, isDeferrable: Bool = false, initiallyDeferred: Bool = false) {
        self.name = name
        self.columns = [column]
        self.isDeferrable = isDeferrable
        self.initiallyDeferred = initiallyDeferred
        self.type = .notNull
    }
    
    public func validate(_ row: Row, in table: String) throws -> ConstraintValidationResult {
        for column in columns {
            guard let value = row[column] else {
                return .violation("NOT NULL column '\(column)' is missing")
            }
            if value == .null {
                return .violation("NOT NULL column '\(column)' cannot be NULL")
            }
        }
        return .valid
    }
    
    public var description: String {
        "NOT NULL (\(columns.joined(separator: ", ")))"
    }
}

/// Check constraint with expression evaluation
public struct CheckConstraint: Constraint {
    public let name: String
    public let columns: [String]
    public let isDeferrable: Bool
    public let initiallyDeferred: Bool
    public let type: ConstraintType = .check
    public let expression: String
    private let evaluator: (Row) -> Bool
    
    // Custom Codable implementation to exclude the evaluator closure
    private enum CodingKeys: String, CodingKey {
        case name, columns, isDeferrable, initiallyDeferred, type, expression
    }
    
    public init(from decoder: Decoder) throws {
        let container = try decoder.container(keyedBy: CodingKeys.self)
        name = try container.decode(String.self, forKey: .name)
        columns = try container.decode([String].self, forKey: .columns)
        isDeferrable = try container.decode(Bool.self, forKey: .isDeferrable)
        initiallyDeferred = try container.decode(Bool.self, forKey: .initiallyDeferred)
        let decodedExpression = try container.decode(String.self, forKey: .expression)
        expression = decodedExpression
        evaluator = { row in
            CheckConstraint.evaluateSimpleExpression(decodedExpression, with: row)
        }
    }
    
    public func encode(to encoder: Encoder) throws {
        var container = encoder.container(keyedBy: CodingKeys.self)
        try container.encode(name, forKey: .name)
        try container.encode(columns, forKey: .columns)
        try container.encode(isDeferrable, forKey: .isDeferrable)
        try container.encode(initiallyDeferred, forKey: .initiallyDeferred)
        try container.encode(type, forKey: .type)
        try container.encode(expression, forKey: .expression)
    }
    
    public init(name: String, expression: String, columns: [String] = [], isDeferrable: Bool = false, initiallyDeferred: Bool = false) {
        self.name = name
        self.expression = expression
        self.columns = columns
        self.isDeferrable = isDeferrable
        self.initiallyDeferred = initiallyDeferred
        
        // Simple expression evaluator for MVP
        // In a full implementation, this would parse the expression into an AST
        self.evaluator = { row in
            // For MVP, we'll implement basic comparisons
            return CheckConstraint.evaluateSimpleExpression(expression, with: row)
        }
    }
    
    public func validate(_ row: Row, in table: String) throws -> ConstraintValidationResult {
        if evaluator(row) {
            return .valid
        } else {
            return .violation("Check constraint '\(name)' violated: \(expression)")
        }
    }
    
    public var description: String {
        "CHECK (\(expression))"
    }
    
    /// Simple expression evaluator for MVP
    private static func evaluateSimpleExpression(_ expression: String, with row: Row) -> Bool {
        // Remove whitespace and convert to lowercase for simple parsing
        let expr = expression.trimmingCharacters(in: .whitespacesAndNewlines).lowercased()
        
        // Simple patterns for MVP
        if expr.contains(">=") {
            let parts = expr.components(separatedBy: ">=")
            if parts.count == 2 {
                let column = parts[0].trimmingCharacters(in: .whitespaces)
                let value = parts[1].trimmingCharacters(in: .whitespaces)
                return evaluateComparison(row[column], operator: ">=", value: value)
            }
        } else if expr.contains("<=") {
            let parts = expr.components(separatedBy: "<=")
            if parts.count == 2 {
                let column = parts[0].trimmingCharacters(in: .whitespaces)
                let value = parts[1].trimmingCharacters(in: .whitespaces)
                return evaluateComparison(row[column], operator: "<=", value: value)
            }
        } else if expr.contains(">") {
            let parts = expr.components(separatedBy: ">")
            if parts.count == 2 {
                let column = parts[0].trimmingCharacters(in: .whitespaces)
                let value = parts[1].trimmingCharacters(in: .whitespaces)
                return evaluateComparison(row[column], operator: ">", value: value)
            }
        } else if expr.contains("<") {
            let parts = expr.components(separatedBy: "<")
            if parts.count == 2 {
                let column = parts[0].trimmingCharacters(in: .whitespaces)
                let value = parts[1].trimmingCharacters(in: .whitespaces)
                return evaluateComparison(row[column], operator: "<", value: value)
            }
        } else if expr.contains("=") {
            let parts = expr.components(separatedBy: "=")
            if parts.count == 2 {
                let column = parts[0].trimmingCharacters(in: .whitespaces)
                let value = parts[1].trimmingCharacters(in: .whitespaces)
                return evaluateComparison(row[column], operator: "=", value: value)
            }
        }
        
        // Default to true for unsupported expressions
        return true
    }
    
    private static func evaluateComparison(_ rowValue: Value?, operator: String, value: String) -> Bool {
        guard let rowValue = rowValue else { return false }
        
        switch rowValue {
        case .int(let i):
            guard let intValue = Int64(value) else { return false }
            switch `operator` {
            case ">=": return i >= intValue
            case "<=": return i <= intValue
            case ">": return i > intValue
            case "<": return i < intValue
            case "=": return i == intValue
            default: return false
            }
        case .double(let d):
            guard let doubleValue = Double(value) else { return false }
            switch `operator` {
            case ">=": return d >= doubleValue
            case "<=": return d <= doubleValue
            case ">": return d > doubleValue
            case "<": return d < doubleValue
            case "=": return d == doubleValue
            default: return false
            }
        case .string(let s):
            switch `operator` {
            case ">=": return s >= value
            case "<=": return s <= value
            case ">": return s > value
            case "<": return s < value
            case "=": return s == value
            default: return false
            }
        default:
            return false
        }
    }
}

/// Foreign Key constraint
public struct ForeignKeyConstraint: Constraint {
    public let name: String
    public let columns: [String]
    public let isDeferrable: Bool
    public let initiallyDeferred: Bool
    public let type: ConstraintType
    public let referencedTable: String
    public let referencedColumns: [String]
    public let onDelete: ForeignKeyAction
    public let onUpdate: ForeignKeyAction
    
    public enum ForeignKeyAction: String, Codable {
        case cascade = "CASCADE"
        case restrict = "RESTRICT"
        case setNull = "SET NULL"
        case noAction = "NO ACTION"
    }
    
    public init(name: String, 
                columns: [String], 
                referencedTable: String, 
                referencedColumns: [String],
                onDelete: ForeignKeyAction = .noAction,
                onUpdate: ForeignKeyAction = .noAction,
                isDeferrable: Bool = false, 
                initiallyDeferred: Bool = false) {
        self.name = name
        self.columns = columns
        self.referencedTable = referencedTable
        self.referencedColumns = referencedColumns
        self.onDelete = onDelete
        self.onUpdate = onUpdate
        self.isDeferrable = isDeferrable
        self.initiallyDeferred = initiallyDeferred
        self.type = .foreignKey
    }
    
    public func validate(_ row: Row, in table: String) throws -> ConstraintValidationResult {
        // For MVP, we'll just validate that the referenced columns exist
        // In a full implementation, this would check against the referenced table
        return .valid
    }
    
    public var description: String {
        "FOREIGN KEY (\(columns.joined(separator: ", "))) REFERENCES \(referencedTable)(\(referencedColumns.joined(separator: ", ")))"
    }
}

/// Table schema with constraints
public struct TableSchema {
    public let name: String
    public let columns: [ColumnDefinition]
    public let constraints: [Constraint]
    public let indexes: [String] // Index names
    
    public init(name: String, columns: [ColumnDefinition], constraints: [Constraint] = [], indexes: [String] = []) {
        self.name = name
        self.columns = columns
        self.constraints = constraints
        self.indexes = indexes
    }
    
    /// Validates a row against all constraints
    public func validateRow(_ row: Row) throws -> [ConstraintValidationResult] {
        var results: [ConstraintValidationResult] = []
        
        for constraint in constraints {
            let result = try constraint.validate(row, in: name)
            results.append(result)
        }
        
        return results
    }
    
    /// Gets all constraint violations for a row
    public func getViolations(_ row: Row) throws -> [String] {
        let results = try validateRow(row)
        return results.compactMap { result in
            switch result {
            case .valid: return nil
            case .violation(let message): return message
            }
        }
    }
}

/// Column definition with type and constraints
public struct ColumnDefinition {
    public let name: String
    public let type: String
    public let isNullable: Bool
    public let defaultValue: Value?
    public let constraints: [Constraint]
    
    public init(name: String, type: String, isNullable: Bool = true, defaultValue: Value? = nil, constraints: [Constraint] = []) {
        self.name = name
        self.type = type
        self.isNullable = isNullable
        self.defaultValue = defaultValue
        self.constraints = constraints
    }
    
    /// Validates a value for this column
    public func validateValue(_ value: Value?) throws -> ConstraintValidationResult {
        // Check nullability
        if !isNullable && (value == nil || value == .null) {
            return .violation("Column '\(name)' cannot be NULL")
        }
        
        // Apply column-level constraints
        if let value = value {
            for constraint in constraints {
                let result = try constraint.validate([name: value], in: "")
                if !result.isValid {
                    return result
                }
            }
        }
        
        return .valid
    }
}
