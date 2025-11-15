//
//  ASTToLogicalPlanConverter.swift
//  ColibrìDB Query Converter
//
//  Converts ASTNode to LogicalPlan for query optimization
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//

import Foundation

/// Converter from AST to LogicalPlan
public struct ASTToLogicalPlanConverter: Sendable {
    
    public init() {}
    
    /// Convert ASTNode to LogicalPlan
    /// Throws if AST is not a valid SELECT query
    public func convert(_ ast: ASTNode) throws -> LogicalPlan {
        guard ast.kind.uppercased() == "SELECT" else {
            throw ConverterError.notASelectQuery
        }
        
        // Extract table name from FROM clause
        let table = try extractTableName(from: ast)
        
        // Extract projection columns from SELECT clause
        let projection = try extractProjection(from: ast)
        
        // Extract WHERE predicate
        let predicate = try extractPredicate(from: ast)
        
        // Extract filter key (for index optimization)
        let filterInfo = try extractFilterInfo(from: ast)
        
        // Extract ORDER BY columns
        let sortColumns = try extractSortColumns(from: ast)
        
        // Extract LIMIT
        let limit = try extractLimit(from: ast)
        
        return LogicalPlan(
            table: table,
            predicate: predicate,
            filterKey: filterInfo?.value,
            filterColumn: filterInfo?.column,
            projection: projection,
            sortColumns: sortColumns,
            limit: limit
        )
    }
    
    // MARK: - Extraction Methods
    
    /// Extract table name from FROM clause
    private func extractTableName(from ast: ASTNode) throws -> String {
        // Find FROM clause
        guard let fromClause = ast.children.first(where: { $0.kind == "from_clause" }) else {
            throw ConverterError.missingFromClause
        }
        
        // Get first table reference
        guard let tableRef = fromClause.children.first(where: { $0.kind == "table_ref" }) else {
            throw ConverterError.missingTableReference
        }
        
        // Extract table name from attributes
        guard let tableName = tableRef.attributes["name"] else {
            throw ConverterError.invalidTableReference
        }
        
        return tableName
    }
    
    /// Extract projection columns from SELECT clause
    private func extractProjection(from ast: ASTNode) throws -> [String]? {
        // Find SELECT list
        guard let selectList = ast.children.first(where: { $0.kind == "select_list" }) else {
            // No explicit SELECT list means SELECT *
            return nil
        }
        
        var columns: [String] = []
        
        for child in selectList.children {
            if child.kind == "column_ref" {
                // Column reference
                if let columnName = child.attributes["name"] {
                    columns.append(columnName)
                } else if let alias = child.attributes["alias"] {
                    columns.append(alias)
                }
            } else if child.kind == "star" {
                // SELECT * - return nil to indicate all columns
                return nil
            }
        }
        
        return columns.isEmpty ? nil : columns
    }
    
    /// Extract WHERE predicate and convert to closure (public for UPDATE/DELETE)
    public func extractPredicate(from ast: ASTNode) throws -> (@Sendable (Row) -> Bool)? {
        // Find WHERE clause
        guard let whereClause = ast.children.first(where: { $0.kind == "where_clause" }) else {
            return nil
        }
        
        // Get predicate expression
        guard let predicateExpr = whereClause.children.first else {
            return nil
        }
        
        // Convert AST expression to closure
        return try createPredicateClosure(from: predicateExpr)
    }
    
    /// Create predicate closure from AST expression
    private func createPredicateClosure(from expr: ASTNode) throws -> @Sendable (Row) -> Bool {
        switch expr.kind {
        case "binary_op":
            let op = expr.attributes["operator"] ?? "="
            // Check if it's a logical operator
            if op.uppercased() == "AND" {
                return try createAndPredicate(from: expr)
            } else if op.uppercased() == "OR" {
                return try createOrPredicate(from: expr)
            } else {
                // Regular comparison operator
                return try createBinaryOpPredicate(from: expr)
            }
        case "unary_op":
            let op = expr.attributes["operator"] ?? ""
            if op.uppercased() == "NOT" {
                return try createNotPredicate(from: expr)
            }
            return { @Sendable _ in true }
        case "column_ref":
            // Simple column reference (always true for now)
            return { @Sendable _ in true }
        case "literal":
            // Literal (always true for now)
            return { @Sendable _ in true }
        default:
            // For now, return a closure that always returns true
            // TODO: Implement full expression evaluation
            return { @Sendable _ in true }
        }
    }
    
    /// Create AND predicate
    private func createAndPredicate(from expr: ASTNode) throws -> @Sendable (Row) -> Bool {
        guard expr.children.count >= 2 else {
            throw ConverterError.invalidExpression
        }
        
        let leftPredicate = try createPredicateClosure(from: expr.children[0])
        let rightPredicate = try createPredicateClosure(from: expr.children[1])
        
        return { @Sendable row in
            leftPredicate(row) && rightPredicate(row)
        }
    }
    
    /// Create OR predicate
    private func createOrPredicate(from expr: ASTNode) throws -> @Sendable (Row) -> Bool {
        guard expr.children.count >= 2 else {
            throw ConverterError.invalidExpression
        }
        
        let leftPredicate = try createPredicateClosure(from: expr.children[0])
        let rightPredicate = try createPredicateClosure(from: expr.children[1])
        
        return { @Sendable row in
            leftPredicate(row) || rightPredicate(row)
        }
    }
    
    /// Create NOT predicate
    private func createNotPredicate(from expr: ASTNode) throws -> @Sendable (Row) -> Bool {
        guard expr.children.count >= 1 else {
            throw ConverterError.invalidExpression
        }
        
        let childPredicate = try createPredicateClosure(from: expr.children[0])
        
        return { @Sendable row in
            !childPredicate(row)
        }
    }
    
    /// Create binary operator predicate
    private func createBinaryOpPredicate(from expr: ASTNode) throws -> @Sendable (Row) -> Bool {
        guard expr.children.count >= 2 else {
            throw ConverterError.invalidExpression
        }
        
        let left = expr.children[0]
        let right = expr.children[1]
        let op = expr.attributes["operator"] ?? "="
        
        // Capture values needed for evaluation (not self or ASTNode)
        let leftExpr = left
        let rightExpr = right
        let opValue = op
        
        return { @Sendable row in
            // Evaluate left side
            let leftValue = Self.evaluateExpressionStatic(leftExpr, in: row)
            
            // Evaluate right side
            let rightValue = Self.evaluateExpressionStatic(rightExpr, in: row)
            
            // Compare based on operator
            return Self.compareValuesStatic(leftValue, rightValue, operator: opValue)
        }
    }
    
    /// Evaluate expression in context of a row (static version for Sendable)
    private static func evaluateExpressionStatic(_ expr: ASTNode, in row: Row) -> Value? {
        switch expr.kind {
        case "column_ref":
            // Get column value from row
            if let columnName = expr.attributes["name"] {
                return row[columnName]
            }
            return nil
            
        case "literal":
            // Parse literal value
            if let valueStr = expr.attributes["value"] {
                return parseLiteralStatic(valueStr)
            }
            return nil
            
        case "binary_op":
            // Evaluate binary arithmetic operations
            let op = expr.attributes["operator"] ?? ""
            if ["+", "-", "*", "/"].contains(op) {
                guard expr.children.count >= 2 else { return nil }
                let left = evaluateExpressionStatic(expr.children[0], in: row)
                let right = evaluateExpressionStatic(expr.children[1], in: row)
                return evaluateArithmeticStatic(left, right, operator: op)
            }
            return nil
            
        case "unary_op":
            // Evaluate unary operations
            let op = expr.attributes["operator"] ?? ""
            if op == "-" && expr.children.count >= 1 {
                if let value = evaluateExpressionStatic(expr.children[0], in: row) {
                    return negateValueStatic(value)
                }
            }
            return nil
            
        default:
            return nil
        }
    }
    
    /// Evaluate arithmetic operations (static version)
    private static func evaluateArithmeticStatic(_ left: Value?, _ right: Value?, operator op: String) -> Value? {
        guard let left = left, let right = right else { return nil }
        
        switch (left, right, op) {
        case (.int(let l), .int(let r), "+"):
            return .int(l + r)
        case (.int(let l), .int(let r), "-"):
            return .int(l - r)
        case (.int(let l), .int(let r), "*"):
            return .int(l * r)
        case (.int(let l), .int(let r), "/"):
            return r != 0 ? .int(l / r) : nil
        case (.double(let l), .double(let r), "+"):
            return .double(l + r)
        case (.double(let l), .double(let r), "-"):
            return .double(l - r)
        case (.double(let l), .double(let r), "*"):
            return .double(l * r)
        case (.double(let l), .double(let r), "/"):
            return r != 0 ? .double(l / r) : nil
        case (.int(let l), .double(let r), _):
            return evaluateArithmeticStatic(.double(Double(l)), .double(r), operator: op)
        case (.double(let l), .int(let r), _):
            return evaluateArithmeticStatic(.double(l), .double(Double(r)), operator: op)
        default:
            return nil
        }
    }
    
    /// Negate a value (static version)
    private static func negateValueStatic(_ value: Value) -> Value? {
        switch value {
        case .int(let v):
            return .int(-v)
        case .double(let v):
            return .double(-v)
        default:
            return nil
        }
    }
    
    /// Parse literal string to Value (static version)
    private static func parseLiteralStatic(_ str: String) -> Value? {
        // Try integer
        if let intVal = Int64(str) {
            return .int(intVal)
        }
        
        // Try double
        if let doubleVal = Double(str) {
            return .double(doubleVal)
        }
        
        // Try boolean
        if str.lowercased() == "true" {
            return .bool(true)
        }
        if str.lowercased() == "false" {
            return .bool(false)
        }
        
        // Try NULL
        if str.uppercased() == "NULL" {
            return .null
        }
        
        // Remove quotes for strings
        var stringVal = str
        if stringVal.hasPrefix("'") && stringVal.hasSuffix("'") {
            stringVal = String(stringVal.dropFirst().dropLast())
        } else if stringVal.hasPrefix("\"") && stringVal.hasSuffix("\"") {
            stringVal = String(stringVal.dropFirst().dropLast())
        }
        
        return .string(stringVal)
    }
    
    /// Compare two values with operator (static version)
    private static func compareValuesStatic(_ left: Value?, _ right: Value?, operator op: String) -> Bool {
        guard let left = left, let right = right else {
            return false
        }
        
        switch op {
        case "=", "==":
            return left == right
        case "<>", "!=":
            return left != right
        case "<":
            return compareLessThanStatic(left, right)
        case "<=":
            return compareLessThanStatic(left, right) || left == right
        case ">":
            return compareLessThanStatic(right, left)
        case ">=":
            return compareLessThanStatic(right, left) || left == right
        case "LIKE", "like":
            return compareLikeStatic(left, right)
        case "IN", "in":
            // IN operator would need special handling with list of values
            return false
        case "IS NULL", "is null":
            return left == .null
        case "IS NOT NULL", "is not null":
            return left != .null
        default:
            return false
        }
    }
    
    /// Compare two values for less than (static version)
    private static func compareLessThanStatic(_ left: Value, _ right: Value) -> Bool {
        switch (left, right) {
        case (.int(let l), .int(let r)):
            return l < r
        case (.double(let l), .double(let r)):
            return l < r
        case (.int(let l), .double(let r)):
            return Double(l) < r
        case (.double(let l), .int(let r)):
            return l < Double(r)
        case (.string(let l), .string(let r)):
            return l < r
        default:
            return false
        }
    }
    
    /// Compare values with LIKE operator (pattern matching) (static version)
    private static func compareLikeStatic(_ left: Value?, _ right: Value?) -> Bool {
        guard let left = left, let right = right,
              case .string(let leftStr) = left,
              case .string(let rightStr) = right else {
            return false
        }
        
        // Convert SQL LIKE pattern to regex
        // % matches any sequence, _ matches single character
        var pattern = rightStr
            .replacingOccurrences(of: "%", with: ".*")
            .replacingOccurrences(of: "_", with: ".")
        
        // Escape special regex characters
        pattern = NSRegularExpression.escapedPattern(for: pattern)
            .replacingOccurrences(of: "\\.\\*", with: ".*")
            .replacingOccurrences(of: "\\.", with: ".")
        
        // Match pattern
        do {
            let regex = try NSRegularExpression(pattern: "^\(pattern)$", options: .caseInsensitive)
            let range = NSRange(location: 0, length: leftStr.utf16.count)
            return regex.firstMatch(in: leftStr, options: [], range: range) != nil
        } catch {
            return false
        }
    }
    
    private struct FilterInfo {
        let column: String
        let value: Value
    }
    
    /// Extract filter info (column + literal) for potential index use
    private func extractFilterInfo(from ast: ASTNode) throws -> FilterInfo? {
        guard let whereClause = ast.children.first(where: { $0.kind == "where_clause" }) else {
            return nil
        }
        
        guard let predicateExpr = whereClause.children.first,
              predicateExpr.kind == "binary_op",
              predicateExpr.attributes["operator"] == "=",
              predicateExpr.children.count >= 2 else {
            return nil
        }
        
        let left = predicateExpr.children[0]
        let right = predicateExpr.children[1]
        
        guard left.kind == "column_ref",
              let columnName = left.attributes["name"] else {
            return nil
        }
        
        guard right.kind == "literal",
              let valueStr = right.attributes["value"],
              let value = Self.parseLiteralStatic(valueStr) else {
            return nil
        }
        
        return FilterInfo(column: columnName, value: value)
    }
    
    /// Extract ORDER BY columns
    private func extractSortColumns(from ast: ASTNode) throws -> [String]? {
        // Find ORDER BY clause
        guard let orderByClause = ast.children.first(where: { $0.kind == "order_by_clause" }) else {
            return nil
        }
        
        var columns: [String] = []
        
        for child in orderByClause.children {
            if child.kind == "sort_item" {
                if let columnName = child.attributes["column"] {
                    columns.append(columnName)
                }
            }
        }
        
        return columns.isEmpty ? nil : columns
    }
    
    /// Extract LIMIT value
    private func extractLimit(from ast: ASTNode) throws -> Int? {
        // Find LIMIT clause
        guard let limitClause = ast.children.first(where: { $0.kind == "limit_clause" }) else {
            return nil
        }
        
        // Get limit value
        if let limitStr = limitClause.attributes["count"],
           let limit = Int(limitStr) {
            return limit
        }
        
        return nil
    }
}

// MARK: - Converter Errors

public enum ConverterError: Error, LocalizedError {
    case notASelectQuery
    case missingFromClause
    case missingTableReference
    case invalidTableReference
    case invalidExpression
    
    public var errorDescription: String? {
        switch self {
        case .notASelectQuery:
            return "AST is not a SELECT query"
        case .missingFromClause:
            return "SELECT query missing FROM clause"
        case .missingTableReference:
            return "FROM clause missing table reference"
        case .invalidTableReference:
            return "Invalid table reference in FROM clause"
        case .invalidExpression:
            return "Invalid expression in predicate"
        }
    }
}

