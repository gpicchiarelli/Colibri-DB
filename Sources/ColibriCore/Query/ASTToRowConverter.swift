//
//  ASTToRowConverter.swift
//  ColibrìDB Query Converter
//
//  Converts ASTNode values to Row for INSERT/UPDATE operations
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//

import Foundation

/// Converter from AST values to Row
public struct ASTToRowConverter: Sendable {
    
    public init() {}
    
    /// Convert INSERT VALUES AST to Row
    /// AST structure: INSERT INTO table (cols) VALUES (values)
    /// values: [ASTNode] where each node is a literal or expression
    public func convertInsertValues(_ values: [ASTNode], columns: [String], tableDef: TableDefinition) throws -> Row {
        var row: Row = [:]
        
        // If columns are specified, use them; otherwise use all columns in schema order
        let targetColumns = columns.isEmpty ? tableDef.columns.map { $0.name } : columns
        
        // Check that we have enough values
        guard values.count <= targetColumns.count else {
            throw ASTToRowConverterError.tooManyValues
        }
        
        // Convert each value
        for (index, valueNode) in values.enumerated() {
            if index < targetColumns.count {
                let columnName = targetColumns[index]
                let value = try evaluateValueExpression(valueNode)
                row[columnName] = value
            }
        }
        
        // Fill missing columns with defaults or NULL
        for columnDef in tableDef.columns {
            if row[columnDef.name] == nil {
                if let defaultValue = columnDef.defaultValue {
                    row[columnDef.name] = defaultValue
                } else if columnDef.nullable {
                    row[columnDef.name] = .null
                } else {
                    throw ASTToRowConverterError.missingRequiredColumn(column: columnDef.name)
                }
            }
        }
        
        return row
    }
    
    /// Evaluate value expression to Value (public for UPDATE/DELETE)
    public func evaluateValueExpression(_ expr: ASTNode) throws -> Value {
        switch expr.kind {
        case "literal":
            return try parseLiteral(expr)
        case "column_ref":
            // Column reference in VALUES is not allowed in standard SQL
            throw ASTToRowConverterError.invalidExpression("Column reference not allowed in INSERT VALUES")
        case "binary_op":
            // Evaluate arithmetic expressions
            return try evaluateArithmeticExpression(expr)
        case "unary_op":
            // Evaluate unary operations (e.g., -5)
            return try evaluateUnaryExpression(expr)
        default:
            throw ASTToRowConverterError.invalidExpression("Unsupported expression type: \(expr.kind)")
        }
    }
    
    /// Parse literal AST node to Value
    private func parseLiteral(_ expr: ASTNode) throws -> Value {
        guard let valueStr = expr.attributes["value"] else {
            throw ASTToRowConverterError.invalidExpression("Literal missing value")
        }
        
        // Try integer
        if let intVal = Int64(valueStr) {
            return .int(intVal)
        }
        
        // Try double
        if let doubleVal = Double(valueStr) {
            return .double(doubleVal)
        }
        
        // Try boolean
        if valueStr.lowercased() == "true" {
            return .bool(true)
        }
        if valueStr.lowercased() == "false" {
            return .bool(false)
        }
        
        // Try NULL
        if valueStr.uppercased() == "NULL" {
            return .null
        }
        
        // Remove quotes for strings
        var stringVal = valueStr
        if stringVal.hasPrefix("'") && stringVal.hasSuffix("'") {
            stringVal = String(stringVal.dropFirst().dropLast())
        } else if stringVal.hasPrefix("\"") && stringVal.hasSuffix("\"") {
            stringVal = String(stringVal.dropFirst().dropLast())
        }
        
        return .string(stringVal)
    }
    
    /// Evaluate arithmetic expression
    private func evaluateArithmeticExpression(_ expr: ASTNode) throws -> Value {
        guard expr.children.count >= 2 else {
            throw ASTToRowConverterError.invalidExpression("Arithmetic expression needs 2 operands")
        }
        
        let left = try evaluateValueExpression(expr.children[0])
        let right = try evaluateValueExpression(expr.children[1])
        let op = expr.attributes["operator"] ?? "+"
        
        return try evaluateArithmetic(left, right, operator: op)
    }
    
    /// Evaluate unary expression
    private func evaluateUnaryExpression(_ expr: ASTNode) throws -> Value {
        guard expr.children.count >= 1 else {
            throw ASTToRowConverterError.invalidExpression("Unary expression needs 1 operand")
        }
        
        let value = try evaluateValueExpression(expr.children[0])
        let op = expr.attributes["operator"] ?? ""
        
        if op == "-" {
            switch value {
            case .int(let v):
                return .int(-v)
            case .double(let v):
                return .double(-v)
            default:
                throw ASTToRowConverterError.invalidExpression("Cannot negate non-numeric value")
            }
        }
        
        return value
    }
    
    /// Evaluate arithmetic operation
    private func evaluateArithmetic(_ left: Value, _ right: Value, operator op: String) throws -> Value {
        switch (left, right, op) {
        case (.int(let l), .int(let r), "+"):
            return .int(l + r)
        case (.int(let l), .int(let r), "-"):
            return .int(l - r)
        case (.int(let l), .int(let r), "*"):
            return .int(l * r)
        case (.int(let l), .int(let r), "/"):
            guard r != 0 else { throw ASTToRowConverterError.invalidExpression("Division by zero") }
            return .int(l / r)
        case (.double(let l), .double(let r), "+"):
            return .double(l + r)
        case (.double(let l), .double(let r), "-"):
            return .double(l - r)
        case (.double(let l), .double(let r), "*"):
            return .double(l * r)
        case (.double(let l), .double(let r), "/"):
            guard r != 0 else { throw ASTToRowConverterError.invalidExpression("Division by zero") }
            return .double(l / r)
        case (.int(let l), .double(let r), _):
            return try evaluateArithmetic(.double(Double(l)), .double(r), operator: op)
        case (.double(let l), .int(let r), _):
            return try evaluateArithmetic(.double(l), .double(Double(r)), operator: op)
        default:
            throw ASTToRowConverterError.invalidExpression("Cannot perform arithmetic on \(left) and \(right)")
        }
    }
}

// MARK: - Converter Errors

public enum ASTToRowConverterError: Error, LocalizedError {
    case tooManyValues
    case missingRequiredColumn(column: String)
    case invalidExpression(String)
    
    public var errorDescription: String? {
        switch self {
        case .tooManyValues:
            return "Too many values in INSERT statement"
        case .missingRequiredColumn(let column):
            return "Missing required column: \(column)"
        case .invalidExpression(let message):
            return "Invalid expression: \(message)"
        }
    }
}

