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
        
        let mutableAST: SQLStatement
        
        // Substitute in all parts of the statement
        switch ast {
        case .select(let stmt):
            mutableAST = .select(try substituteInSelect(stmt, parameters: parameters))
        case .insert(let stmt):
            mutableAST = .insert(try substituteInInsert(stmt, parameters: parameters))
        case .update(let stmt):
            mutableAST = .update(try substituteInUpdate(stmt, parameters: parameters))
        case .delete(let stmt):
            mutableAST = .delete(try substituteInDelete(stmt, parameters: parameters))
        case .createTable, .createIndex, .dropTable, .dropIndex, .explain:
            // Other statement types don't typically have parameters
            mutableAST = ast
        }
        
        // Verify no unbound parameters remain
        try verifyAllParametersBound(mutableAST)
        
        return mutableAST
    }
    
    // MARK: - Statement-specific Substitution
    
    private static func substituteInSelect(
        _ stmt: SelectStatement,
        parameters: [String: Value]
    ) throws -> SelectStatement {
        // Substitute in WHERE clause if present
        let newWhereClause = try stmt.whereClause.map { try substituteInExpression($0, parameters: parameters) }
        
        // Substitute in HAVING clause if present
        let newHaving = try stmt.having.map { try substituteInExpression($0, parameters: parameters) }
        
        // Substitute in select expressions if they contain parameters
        let newColumns = try stmt.columns.map { col in
            SelectColumn(
                expression: try substituteInExpression(col.expression, parameters: parameters),
                alias: col.alias
            )
        }
        
        return SelectStatement(
            columns: newColumns,
            from: stmt.from,
            whereClause: newWhereClause,
            groupBy: stmt.groupBy,
            having: newHaving,
            orderBy: stmt.orderBy,
            limit: stmt.limit,
            offset: stmt.offset
        )
    }
    
    private static func substituteInInsert(
        _ stmt: InsertStatement,
        parameters: [String: Value]
    ) throws -> InsertStatement {
        // Substitute in VALUES clause
        let newValues = try stmt.values.map { expr in
            try substituteInExpression(expr, parameters: parameters)
        }
        
        return InsertStatement(
            tableName: stmt.tableName,
            columns: stmt.columns,
            values: newValues
        )
    }
    
    private static func substituteInUpdate(
        _ stmt: UpdateStatement,
        parameters: [String: Value]
    ) throws -> UpdateStatement {
        // Substitute in SET clause
        let newSetClauses = try stmt.setClauses.map { setClause in
            SetClause(
                column: setClause.column,
                value: try substituteInExpression(setClause.value, parameters: parameters)
            )
        }
        
        // Substitute in WHERE clause
        let newWhereClause = try stmt.whereClause.map { try substituteInExpression($0, parameters: parameters) }
        
        return UpdateStatement(
            tableName: stmt.tableName,
            setClauses: newSetClauses,
            whereClause: newWhereClause
        )
    }
    
    private static func substituteInDelete(
        _ stmt: DeleteStatement,
        parameters: [String: Value]
    ) throws -> DeleteStatement {
        // Substitute in WHERE clause
        let newWhereClause = try stmt.whereClause.map { try substituteInExpression($0, parameters: parameters) }
        
        return DeleteStatement(
            tableName: stmt.tableName,
            whereClause: newWhereClause
        )
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
        
        switch stmt {
        case .select(let selectStmt):
            // Check WHERE clause
            if let whereExpr = selectStmt.whereClause {
                params.append(contentsOf: extractParametersFromExpression(whereExpr))
            }
            
            // Check HAVING clause
            if let havingExpr = selectStmt.having {
                params.append(contentsOf: extractParametersFromExpression(havingExpr))
            }
            
            // Check select expressions
            for col in selectStmt.columns {
                params.append(contentsOf: extractParametersFromExpression(col.expression))
            }
            
        case .insert(let insertStmt):
            // Check insert values
            for expr in insertStmt.values {
                params.append(contentsOf: extractParametersFromExpression(expr))
            }
            
        case .update(let updateStmt):
            // Check update SET values
            for setClause in updateStmt.setClauses {
                params.append(contentsOf: extractParametersFromExpression(setClause.value))
            }
            
            // Check WHERE clause
            if let whereExpr = updateStmt.whereClause {
                params.append(contentsOf: extractParametersFromExpression(whereExpr))
            }
            
        case .delete(let deleteStmt):
            // Check WHERE clause
            if let whereExpr = deleteStmt.whereClause {
                params.append(contentsOf: extractParametersFromExpression(whereExpr))
            }
            
        case .createTable, .createIndex, .dropTable, .dropIndex, .explain:
            // These statements don't have parameters
            break
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

