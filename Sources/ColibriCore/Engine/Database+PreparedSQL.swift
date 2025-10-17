//
//  Database+PreparedSQL.swift
//  ColibrDB
//
//  Integration layer for prepared statements with database execution
//

import Foundation

extension Database {
    
    /// Execute parsed SQL AST (internal use by prepared statements)
    /// 
    /// This is called after parameters have been safely substituted into the AST.
    /// At this point, the AST contains only literal values, no user-controlled code.
    ///
    /// - Parameter ast: Validated SQL statement with parameters substituted
    /// - Returns: Query results
    /// - Throws: DBError if execution fails
    internal func executeParsedSQL(_ ast: SQLStatement) throws -> [[String: Value]] {
        
        // Route to appropriate handler based on statement type
        switch ast.type {
        case .select:
            return try executeParsedSelect(ast)
            
        case .insert:
            try executeParsedInsert(ast)
            return []
            
        case .update:
            try executeParsedUpdate(ast)
            return []
            
        case .delete:
            try executeParsedDelete(ast)
            return []
            
        case .createTable, .dropTable, .createIndex, .dropIndex:
            // DDL statements don't return data
            try executeParsedDDL(ast)
            return []
            
        default:
            throw DBError.notImplemented("Statement type \(ast.type) not yet supported in prepared statements")
        }
    }
    
    // MARK: - SELECT Execution
    
    private func executeParsedSelect(_ ast: SQLStatement) throws -> [[String: Value]] {
        guard let tableName = ast.tableName else {
            throw DBError.invalidArgument("SELECT statement missing table name")
        }
        
        // Build QueryRequest from AST
        var predicates: [QueryPredicate] = []
        
        // Extract WHERE predicates
        if let whereExpr = ast.whereClause {
            predicates = try extractPredicates(from: whereExpr)
        }
        
        // Extract projection
        let projection = ast.selectColumns?.isEmpty == false ? ast.selectColumns : nil
        
        let request = QueryRequest(
            root: QueryTableRef(
                name: tableName,
                predicates: predicates,
                projection: projection
            ),
            limit: ast.limit
        )
        
        // Execute via query planner
        return try executePlan(request: request, tid: nil)
    }
    
    // MARK: - INSERT Execution
    
    private func executeParsedInsert(_ ast: SQLStatement) throws {
        guard let tableName = ast.tableName else {
            throw DBError.invalidArgument("INSERT statement missing table name")
        }
        
        guard let values = ast.insertValues?.first else {
            throw DBError.invalidArgument("INSERT statement missing values")
        }
        
        guard let columns = ast.insertColumns else {
            throw DBError.invalidArgument("INSERT statement missing columns")
        }
        
        // Build row from columns and values
        var row: Row = [:]
        for (index, column) in columns.enumerated() {
            guard index < values.count else { break }
            
            let value = try evaluateExpression(values[index])
            row[column] = value
        }
        
        // Execute insert
        let tid = try begin()
        _ = try insert(table: tableName, row: row, tid: tid)
        try commit(tid)
    }
    
    // MARK: - UPDATE Execution
    
    private func executeParsedUpdate(_ ast: SQLStatement) throws {
        guard let tableName = ast.tableName else {
            throw DBError.invalidArgument("UPDATE statement missing table name")
        }
        
        guard let setValues = ast.setValues else {
            throw DBError.invalidArgument("UPDATE statement missing SET clause")
        }
        
        // Build new row values
        var newValues: Row = [:]
        for (column, expr) in setValues {
            let value = try evaluateExpression(expr)
            newValues[column] = value
        }
        
        // Get rows to update (from WHERE clause)
        let rowsToUpdate: [(RID, Row)]
        if let whereExpr = ast.whereClause {
            let predicates = try extractPredicates(from: whereExpr)
            let request = QueryRequest(root: QueryTableRef(name: tableName, predicates: predicates))
            let results = try executePlan(request: request, tid: nil)
            
            // Convert to RID format (simplified - need actual RID tracking)
            rowsToUpdate = []  // TODO: Get RIDs from scan
        } else {
            rowsToUpdate = try scan(table: tableName)
        }
        
        // Execute updates
        let tid = try begin()
        for (rid, oldRow) in rowsToUpdate {
            var updatedRow = oldRow
            for (key, value) in newValues {
                updatedRow[key] = value
            }
            try update(table: tableName, rid: rid, newRow: updatedRow, tid: tid)
        }
        try commit(tid)
    }
    
    // MARK: - DELETE Execution
    
    private func executeParsedDelete(_ ast: SQLStatement) throws {
        guard let tableName = ast.tableName else {
            throw DBError.invalidArgument("DELETE statement missing table name")
        }
        
        // Get rows to delete
        let rowsToDelete: [(RID, Row)]
        if let whereExpr = ast.whereClause {
            let predicates = try extractPredicates(from: whereExpr)
            let request = QueryRequest(root: QueryTableRef(name: tableName, predicates: predicates))
            let results = try executePlan(request: request, tid: nil)
            rowsToDelete = []  // TODO: Get RIDs
        } else {
            rowsToDelete = try scan(table: tableName)
        }
        
        // Execute deletes
        let tid = try begin()
        for (rid, _) in rowsToDelete {
            try delete(table: tableName, rid: rid, tid: tid)
        }
        try commit(tid)
    }
    
    // MARK: - DDL Execution
    
    private func executeParsedDDL(_ ast: SQLStatement) throws {
        switch ast.type {
        case .createTable:
            guard let tableName = ast.tableName else {
                throw DBError.invalidArgument("CREATE TABLE missing table name")
            }
            try createTable(tableName)
            
        case .dropTable:
            guard let tableName = ast.tableName else {
                throw DBError.invalidArgument("DROP TABLE missing table name")
            }
            try dropTable(tableName)
            
        default:
            throw DBError.notImplemented("DDL type \(ast.type) not yet implemented")
        }
    }
    
    // MARK: - Helper Methods
    
    /// Evaluate an expression to a concrete value
    private func evaluateExpression(_ expr: SQLExpression) throws -> Value {
        switch expr {
        case .literal(let lit):
            return literalToValue(lit)
            
        case .parameter:
            // Should never happen - parameters already substituted
            throw DBError.invalidArgument("Unsubstituted parameter in execution")
            
        case .column(let name):
            throw DBError.invalidArgument("Cannot evaluate column reference '\(name)' without row context")
            
        case .binary, .unary, .function, .caseWhen:
            throw DBError.notImplemented("Complex expression evaluation not yet supported")
        }
    }
    
    /// Convert SQL literal to ColibriDB Value
    private func literalToValue(_ literal: SQLLiteral) -> Value {
        switch literal {
        case .integer(let v):
            return .int(v)
        case .double(let v):
            return .double(v)
        case .string(let v):
            return .string(v)
        case .boolean(let v):
            return .bool(v)
        case .null:
            return .null
        }
    }
    
    /// Extract predicates from WHERE expression
    private func extractPredicates(from expr: SQLExpression) throws -> [QueryPredicate] {
        var predicates: [QueryPredicate] = []
        
        // Recursively extract predicates from expression
        switch expr {
        case .binary(let left, let op, let right):
            // Simple equality: column = value
            if case .column(let columnName) = left,
               case .literal(let lit) = right {
                let value = literalToValue(lit)
                let predOp: QueryPredicateOperator
                
                switch op {
                case .equals:
                    predOp = .equals
                case .greaterThanOrEqual:
                    predOp = .greaterOrEqual
                case .lessThanOrEqual:
                    predOp = .lessOrEqual
                default:
                    throw DBError.notImplemented("Operator \(op) not yet supported in prepared statements")
                }
                
                predicates.append(QueryPredicate(column: columnName, op: predOp, value: value))
            }
            // AND clause: recurse both sides
            else if op == .and {
                predicates.append(contentsOf: try extractPredicates(from: left))
                predicates.append(contentsOf: try extractPredicates(from: right))
            }
            
        default:
            // Complex expressions not yet supported
            break
        }
        
        return predicates
    }
}

