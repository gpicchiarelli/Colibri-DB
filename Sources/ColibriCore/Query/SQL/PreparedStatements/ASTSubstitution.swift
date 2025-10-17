//
//  ASTSubstitution.swift
//  ColibrDB
//
//  Safe AST parameter substitution
//

import Foundation

/// Safe parameter substitution in SQL AST
/// 
/// This is the critical security component. Parameters are substituted
/// directly in the AST as literal value nodes, NEVER as SQL code strings.
/// This makes SQL injection mathematically impossible.
public struct ASTSubstitutor {
    
    /// Safely substitute parameters in AST with bound values
    ///
    /// - Parameters:
    ///   - ast: Original SQL statement AST with parameter placeholders
    ///   - parameters: Validated parameter values to substitute
    /// - Returns: New AST with parameters replaced by literal values
    /// - Throws: DBError if parameters are missing or invalid
    public static func substitute(
        _ ast: SQLStatement,
        parameters: [String: Value]
    ) throws -> SQLStatement {
        
        var mutableAST = ast
        
        // Substitute in all parts of the statement
        switch ast.type {
        case .select:
            mutableAST = try substituteInSelect(ast, parameters: parameters)
        case .insert:
            mutableAST = try substituteInInsert(ast, parameters: parameters)
        case .update:
            mutableAST = try substituteInUpdate(ast, parameters: parameters)
        case .delete:
            mutableAST = try substituteInDelete(ast, parameters: parameters)
        default:
            // Other statement types don't typically have parameters
            break
        }
        
        // Verify no unbound parameters remain
        try verifyAllParametersBound(mutableAST)
        
        return mutableAST
    }
    
    // MARK: - Statement-specific Substitution
    
    private static func substituteInSelect(
        _ stmt: SQLStatement,
        parameters: [String: Value]
    ) throws -> SQLStatement {
        var modified = stmt
        
        // Substitute in WHERE clause if present
        if let whereExpr = stmt.whereClause {
            modified.whereClause = try substituteInExpression(whereExpr, parameters: parameters)
        }
        
        // Substitute in HAVING clause if present
        if let havingExpr = stmt.havingClause {
            modified.havingClause = try substituteInExpression(havingExpr, parameters: parameters)
        }
        
        // Substitute in select expressions if they contain parameters
        if let selectExprs = stmt.selectExpressions {
            modified.selectExpressions = try selectExprs.map { expr in
                try substituteInExpression(expr, parameters: parameters)
            }
        }
        
        return modified
    }
    
    private static func substituteInInsert(
        _ stmt: SQLStatement,
        parameters: [String: Value]
    ) throws -> SQLStatement {
        var modified = stmt
        
        // Substitute in VALUES clause
        if let values = stmt.insertValues {
            modified.insertValues = try values.map { row in
                try row.map { expr in
                    try substituteInExpression(expr, parameters: parameters)
                }
            }
        }
        
        return modified
    }
    
    private static func substituteInUpdate(
        _ stmt: SQLStatement,
        parameters: [String: Value]
    ) throws -> SQLStatement {
        var modified = stmt
        
        // Substitute in SET clause
        if let setValues = stmt.setValues {
            modified.setValues = try setValues.mapValues { expr in
                try substituteInExpression(expr, parameters: parameters)
            }
        }
        
        // Substitute in WHERE clause
        if let whereExpr = stmt.whereClause {
            modified.whereClause = try substituteInExpression(whereExpr, parameters: parameters)
        }
        
        return modified
    }
    
    private static func substituteInDelete(
        _ stmt: SQLStatement,
        parameters: [String: Value]
    ) throws -> SQLStatement {
        var modified = stmt
        
        // Substitute in WHERE clause
        if let whereExpr = stmt.whereClause {
            modified.whereClause = try substituteInExpression(whereExpr, parameters: parameters)
        }
        
        return modified
    }
    
    // MARK: - Expression Substitution (Recursive)
    
    /// Recursively substitute parameters in an expression
    public static func substituteInExpression(
        _ expr: SQLExpression,
        parameters: [String: Value]
    ) throws -> SQLExpression {
        
        switch expr {
        case .parameter(let name, _):
            // 🔒 CRITICAL: Replace parameter with literal value
            guard let value = parameters[name] else {
                throw DBError.invalidArgument("Parameter '\(name)' not bound")
            }
            
            // Convert Value to SQLLiteral
            let literal = try valueToSQLLiteral(value)
            return .literal(literal)
            
        case .binary(let left, let op, let right):
            // Recursively substitute in both sides
            let newLeft = try substituteInExpression(left, parameters: parameters)
            let newRight = try substituteInExpression(right, parameters: parameters)
            return .binary(newLeft, op, newRight)
            
        case .unary(let op, let operand):
            let newOperand = try substituteInExpression(operand, parameters: parameters)
            return .unary(op, newOperand)
            
        case .function(let name, let args):
            let newArgs = try args.map { arg in
                try substituteInExpression(arg, parameters: parameters)
            }
            return .function(name, newArgs)
            
        case .caseWhen(let whenClauses, let elseExpr):
            let newWhenClauses = try whenClauses.map { clause in
                SQLExpression.SQLWhenClause(
                    condition: try substituteInExpression(clause.condition, parameters: parameters),
                    result: try substituteInExpression(clause.result, parameters: parameters)
                )
            }
            let newElseExpr = try elseExpr.map { try substituteInExpression($0, parameters: parameters) }
            return .caseWhen(newWhenClauses, newElseExpr)
            
        case .literal, .column:
            // No parameters in literals or column references
            return expr
        }
    }
    
    // MARK: - Value Conversion
    
    /// Convert ColibriDB Value to SQL literal (type-safe)
    private static func valueToSQLLiteral(_ value: Value) throws -> SQLLiteral {
        switch value {
        case .int(let v):
            return .integer(v)
        case .double(let v):
            return .double(v)
        case .bool(let v):
            return .boolean(v)
        case .string(let v):
            return .string(v)
        case .null:
            return .null
        case .decimal(let v):
            return .double(Double(truncating: v as NSNumber))
        case .date(let v):
            let formatter = ISO8601DateFormatter()
            return .string(formatter.string(from: v))
        }
    }
    
    // MARK: - Validation
    
    /// Verify that all parameters in AST have been substituted
    private static func verifyAllParametersBound(_ stmt: SQLStatement) throws {
        let unboundParams = extractUnboundParameters(from: stmt)
        
        guard unboundParams.isEmpty else {
            throw DBError.invalidArgument("Unbound parameters: \(unboundParams.joined(separator: ", "))")
        }
    }
    
    /// Extract any remaining parameter placeholders from AST
    private static func extractUnboundParameters(from stmt: SQLStatement) -> [String] {
        var params: [String] = []
        
        // Check WHERE clause
        if let whereExpr = stmt.whereClause {
            params.append(contentsOf: extractParametersFromExpression(whereExpr))
        }
        
        // Check HAVING clause
        if let havingExpr = stmt.havingClause {
            params.append(contentsOf: extractParametersFromExpression(havingExpr))
        }
        
        // Check select expressions
        if let selectExprs = stmt.selectExpressions {
            for expr in selectExprs {
                params.append(contentsOf: extractParametersFromExpression(expr))
            }
        }
        
        // Check insert values
        if let insertValues = stmt.insertValues {
            for row in insertValues {
                for expr in row {
                    params.append(contentsOf: extractParametersFromExpression(expr))
                }
            }
        }
        
        // Check update SET values
        if let setValues = stmt.setValues {
            for expr in setValues.values {
                params.append(contentsOf: extractParametersFromExpression(expr))
            }
        }
        
        return params
    }
    
    /// Recursively extract parameter names from expression
    private static func extractParametersFromExpression(_ expr: SQLExpression) -> [String] {
        switch expr {
        case .parameter(let name, _):
            return [name]
            
        case .binary(let left, _, let right):
            return extractParametersFromExpression(left) + extractParametersFromExpression(right)
            
        case .unary(_, let operand):
            return extractParametersFromExpression(operand)
            
        case .function(_, let args):
            return args.flatMap { extractParametersFromExpression($0) }
            
        case .caseWhen(let whenClauses, let elseExpr):
            var params: [String] = []
            for clause in whenClauses {
                params.append(contentsOf: extractParametersFromExpression(clause.condition))
                params.append(contentsOf: extractParametersFromExpression(clause.result))
            }
            if let elseExpr = elseExpr {
                params.append(contentsOf: extractParametersFromExpression(elseExpr))
            }
            return params
            
        case .literal, .column:
            return []
        }
    }
}

