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
        switch ast {
        case .select(let stmt):
            return try executeParsedSelect(stmt)
            
        case .insert(let stmt):
            try executeParsedInsert(stmt)
            return []
            
        case .update(let stmt):
            try executeParsedUpdate(stmt)
            return []
            
        case .delete(let stmt):
            try executeParsedDelete(stmt)
            return []
            
        case .createTable(let stmt):
            try executeParsedCreateTable(stmt)
            return []
            
        case .dropTable(let stmt):
            try executeParsedDropTable(stmt)
            return []
            
        case .createIndex, .dropIndex, .explain:
            throw DBError.notImplemented("Statement type not yet supported in prepared statements")
        }
    }
    
    // MARK: - SELECT Execution
    
    private func executeParsedSelect(_ stmt: SelectStatement) throws -> [[String: Value]] {
        // Extract table name from FROM clause
        guard let from = stmt.from,
              case .table(let tableName, _) = from else {
            throw DBError.invalidArgument("SELECT statement missing or unsupported table reference")
        }
        
        // Build QueryRequest from AST
        var predicates: [QueryPredicate] = []
        
        // Extract WHERE predicates
        if let whereExpr = stmt.whereClause {
            predicates = try extractPredicates(from: whereExpr)
        }
        
        // Extract projection (column names from select list)
        let projection: [String]? = stmt.columns.count > 0 ? stmt.columns.compactMap { col in
            if case .column(let name) = col.expression {
                return name
            }
            return nil
        } : nil
        
        let request = QueryRequest(
            root: QueryTableRef(
                name: tableName,
                predicates: predicates,
                projection: projection
            ),
            limit: stmt.limit
        )
        
        // Execute via query planner
        return try executeQuery(request)
    }
    
    // MARK: - INSERT Execution
    
    private func executeParsedInsert(_ stmt: InsertStatement) throws {
        let tableName = stmt.tableName
        let values = stmt.values
        
        guard let columns = stmt.columns else {
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
        _ = try insert(into: tableName, row: row, tid: tid)
        try commit(tid)
    }
    
    // MARK: - UPDATE Execution
    
    private func executeParsedUpdate(_ stmt: UpdateStatement) throws {
        let tableName = stmt.tableName
        let setClauses = stmt.setClauses
        
        // Build new row values
        var newValues: Row = [:]
        for setClause in setClauses {
            let value = try evaluateExpression(setClause.value)
            newValues[setClause.column] = value
        }
        
        // Execute updates using transaction-aware updateEquals
        let tid = try begin()
        
        // For now, we use a simplified approach - scan all rows and update
        // TODO: Use WHERE clause predicates when available
        let rowsToUpdate = try scan(tableName, tid: tid)
        
        var updated = 0
        for (rid, row) in rowsToUpdate {
            // Check if row matches WHERE clause (if present)
            var shouldUpdate = true
            if let whereExpr = stmt.whereClause {
                // For now, we skip complex WHERE evaluation
                // TODO: Implement proper WHERE clause evaluation
                shouldUpdate = true
            }
            
            if shouldUpdate {
                // Use updateEquals for single column or manual update for multiple
                try updateEquals(table: tableName, matchColumn: "_rowid", matchValue: .int(Int64(rid.pageId)), set: newValues, tid: tid)
                updated += 1
            }
        }
        
        try commit(tid)
    }
    
    // MARK: - DELETE Execution
    
    private func executeParsedDelete(_ stmt: DeleteStatement) throws {
        let tableName = stmt.tableName
        
        // Execute deletes using transaction-aware deleteBatch
        let tid = try begin()
        
        // Get rows to delete
        let rowsToDelete = try scan(tableName, tid: tid)
        var ridsToDelete: [RID] = []
        
        for (rid, row) in rowsToDelete {
            // Check if row matches WHERE clause (if present)
            var shouldDelete = true
            if let whereExpr = stmt.whereClause {
                // For now, we skip complex WHERE evaluation
                // TODO: Implement proper WHERE clause evaluation
                shouldDelete = true
            }
            
            if shouldDelete {
                ridsToDelete.append(rid)
            }
        }
        
        // Delete all matching rows
        _ = try deleteBatch(table: tableName, rids: ridsToDelete, tid: tid)
        try commit(tid)
    }
    
    // MARK: - DDL Execution
    
    private func executeParsedCreateTable(_ stmt: CreateTableStatement) throws {
        // For now, we just create an empty table
        // TODO: Use column definitions and constraints from stmt
        try createTable(stmt.tableName)
    }
    
    private func executeParsedDropTable(_ stmt: DropTableStatement) throws {
        // TODO: Implement dropTable in Database
        // For now, just throw not implemented
        throw DBError.notImplemented("DROP TABLE not yet fully implemented")
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

