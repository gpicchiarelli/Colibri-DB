//
//  SQLQueryInterface.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-27.
//
// Theme: Complete SQL query interface connecting parser to database engine.

import Foundation

// MARK: - SQL Query Result
public struct SQLQueryResult: Codable, Sendable {
    public let statementType: SQLStatementType
    public let affectedRows: Int
    public let message: String
    public let columns: [String]
    public let rows: [[Value]]
    
    public init(statementType: SQLStatementType, affectedRows: Int = 0, message: String = "", columns: [String] = [], rows: [[Value]] = []) {
        self.statementType = statementType
        self.affectedRows = affectedRows
        self.message = message
        self.columns = columns
        self.rows = rows
    }
}

public enum SQLStatementType: String, Codable, Sendable {
    case createTable = "CREATE TABLE"
    case createIndex = "CREATE INDEX"
    case dropTable = "DROP TABLE"
    case dropIndex = "DROP INDEX"
    case insert = "INSERT"
    case update = "UPDATE"
    case delete = "DELETE"
    case select = "SELECT"
    case explain = "EXPLAIN"
}

// MARK: - SQL Query Interface
public final class SQLQueryInterface {
    private let database: Database
    
    public init(database: Database) {
        self.database = database
    }
    
    public func execute(_ sql: String) throws -> SQLQueryResult {
        let statement = try SQLParser.parse(sql)
        return try executeStatement(statement)
    }
    
    private func executeStatement(_ statement: SQLStatement) throws -> SQLQueryResult {
        switch statement {
        case .createTable(let createTable):
            return try executeCreateTable(createTable)
        case .createIndex(let createIndex):
            return try executeCreateIndex(createIndex)
        case .dropTable(let dropTable):
            return try executeDropTable(dropTable)
        case .dropIndex(let dropIndex):
            return try executeDropIndex(dropIndex)
        case .insert(let insert):
            return try executeInsert(insert)
        case .update(let update):
            return try executeUpdate(update)
        case .delete(let delete):
            return try executeDelete(delete)
        case .select(let select):
            return try executeSelect(select)
        case .explain(let explain):
            return try executeExplain(explain)
        }
    }
    
    // MARK: - DDL Execution
    private func executeCreateTable(_ statement: CreateTableStatement) throws -> SQLQueryResult {
        // Register table in catalog first, then create physical if needed
        if let sc = database.systemCatalog {
            _ = sc.registerTable(name: statement.tableName,
                                  schema: "public",
                                  storage: database.config.storageEngine,
                                  physicalPath: nil,
                                  pageSize: database.config.pageSizeBytes,
                                  inMemory: database.config.storageEngine == "InMemory")
        }
        try database.createTable(statement.tableName)
        
        return SQLQueryResult(
            statementType: .createTable,
            message: "Table '\(statement.tableName)' created successfully"
        )
    }

    private func executeCreateIndex(_ statement: CreateIndexStatement) throws -> SQLQueryResult {
        // Ensure table exists in catalog before physical creation
        guard database.isTableRegistered(statement.tableName) else {
            throw SQLQueryError.tableNotFound(statement.tableName)
        }
        try database.createIndex(name: statement.name,
                                 on: statement.tableName,
                                 columns: statement.columns,
                                 using: statement.usingKind ?? "BTree")
        return SQLQueryResult(
            statementType: .createIndex,
            message: "Index '\(statement.name)' created on \(statement.tableName)"
        )
    }

    private func executeDropIndex(_ statement: DropIndexStatement) throws -> SQLQueryResult {
        // Ensure table exists for namespacing
        guard database.isTableRegistered(statement.tableName) else {
            if statement.ifExists { return SQLQueryResult(statementType: .dropIndex, message: "Index not found (table missing)") }
            throw SQLQueryError.tableNotFound(statement.tableName)
        }
        do {
            try database.dropIndex(table: statement.tableName, name: statement.indexName)
        } catch DBError.notFound {
            if !statement.ifExists { throw DBError.notFound("Index \(statement.indexName)") }
        }
        return SQLQueryResult(
            statementType: .dropIndex,
            message: "Index '\(statement.indexName)' dropped on \(statement.tableName)"
        )
    }
    
    private func executeDropTable(_ statement: DropTableStatement) throws -> SQLQueryResult {
        // MVP: mark as dropped in catalog only (physical drop not implemented here)
        if let sc = database.systemCatalog {
            sc.removeLogical(name: statement.tableName, kind: .table)
        }
        return SQLQueryResult(
            statementType: .dropTable,
            message: "Table '\(statement.tableName)' dropped successfully"
        )
    }
    
    // MARK: - DML Execution
    private func executeInsert(_ statement: InsertStatement) throws -> SQLQueryResult {
        var row: Row = [:]
        if let cols = statement.columns {
            guard cols.count == statement.values.count else {
                throw SQLQueryError.invalidOperation("INSERT columns/values arity mismatch")
            }
            for (name, expr) in zip(cols, statement.values) {
                row[name] = try evaluateExpression(expr, inRow: nil)
            }
        } else {
            // Fallback: name columns as column_0, column_1, ...
            row = try buildRowFromValues(statement.values)
        }
        let rid = try database.insert(into: statement.tableName, row: row)
        
        return SQLQueryResult(
            statementType: .insert,
            affectedRows: 1,
            message: "Row inserted with RID: \(rid)"
        )
    }
    
    private func executeUpdate(_ statement: UpdateStatement) throws -> SQLQueryResult {
        // MVP: support WHERE column = literal only
        guard let (matchColumn, matchValue) = try extractEqualsPredicate(statement.whereClause) else {
            throw SQLQueryError.unsupportedOperation("UPDATE supports only WHERE column = literal in MVP")
        }
        var setValues: [String: Value] = [:]
        for sc in statement.setClauses {
            setValues[sc.column] = try evaluateExpression(sc.value, inRow: nil)
        }
        let affected = try database.updateEquals(table: statement.tableName,
                                                 matchColumn: matchColumn,
                                                 matchValue: matchValue,
                                                 set: setValues,
                                                 tid: nil)
        return SQLQueryResult(
            statementType: .update,
            affectedRows: affected,
            message: "Updated rows: \(affected)"
        )
    }
    
    private func executeDelete(_ statement: DeleteStatement) throws -> SQLQueryResult {
        // MVP: support WHERE column = literal only
        guard let (matchColumn, matchValue) = try extractEqualsPredicate(statement.whereClause) else {
            throw SQLQueryError.unsupportedOperation("DELETE supports only WHERE column = literal in MVP")
        }
        let affected = try database.deleteEquals(table: statement.tableName, column: matchColumn, value: matchValue)
        return SQLQueryResult(
            statementType: .delete,
            affectedRows: affected,
            message: "Deleted rows: \(affected)"
        )
    }
    
    // MARK: - Query Execution
    private func executeSelect(_ statement: SelectStatement) throws -> SQLQueryResult {
        guard let from = statement.from else {
            throw SQLQueryError.invalidQuery("SELECT statement requires FROM clause")
        }
        
        let tableName = extractTableName(from)
        let rows = try database.scan(tableName)
        
        // Convert to result format
        var resultRows: [[Value]] = []
        var columns: [String] = []
        
        // Filter by WHERE if any (MVP evaluator)
        var filtered: [(RID, Row)] = rows
        if let whereExpr = statement.whereClause {
            filtered = rows.filter { (_, row) in
                (try? evaluateWhere(whereExpr, inRow: row)) == true
            }
        }

        if !filtered.isEmpty {
            // Extract column names from first row
            let firstRow = filtered.first!.1
            columns = Array(firstRow.keys).sorted()
            
            for (_, row) in filtered {
                var resultRow: [Value] = []
                for column in columns {
                    resultRow.append(row[column] ?? .null)
                }
                resultRows.append(resultRow)
            }
        }
        
        return SQLQueryResult(
            statementType: .select,
            message: "Query executed successfully",
            columns: columns,
            rows: resultRows
        )
    }
    
    private func executeExplain(_ statement: ExplainStatement) throws -> SQLQueryResult {
        // For now, just return the statement type
        return SQLQueryResult(
            statementType: .explain,
            message: "EXPLAIN not yet implemented"
        )
    }
    
    // MARK: - Helper Methods
    private func buildRowFromValues(_ values: [SQLExpression]) throws -> Row {
        var row: Row = [:]
        
        for (index, expression) in values.enumerated() {
            let columnName = "column_\(index)"
            let value = try evaluateExpression(expression, inRow: nil)
            row[columnName] = value
        }
        
        return row
    }
    
    // MARK: - Expression evaluation
    private func evaluateExpression(_ expression: SQLExpression, inRow row: Row?) throws -> Value {
        switch expression {
        case .literal(let literal):
            switch literal {
            case .string(let s): return .string(s)
            case .integer(let i): return .int(i)
            case .double(let d): return .double(d)
            case .boolean(let b): return .bool(b)
            case .null: return .null
            }
        case .column(let name):
            if let row = row { return row[name] ?? .null }
            return .null
        case .binary(let left, let op, let right):
            let leftValue = try evaluateExpression(left, inRow: row)
            let rightValue = try evaluateExpression(right, inRow: row)
            return try evaluateBinaryOperation(leftValue, op, rightValue)
        case .unary(let op, let operand):
            let operandValue = try evaluateExpression(operand, inRow: row)
            return try evaluateUnaryOperation(op, operandValue)
        case .function(let name, let args):
            return try evaluateFunction(name, args)
        case .caseWhen(let whenClauses, let elseExpression):
            return try evaluateCaseWhen(whenClauses, elseExpression)
        }
    }
    
    private func evaluateBinaryOperation(_ left: Value, _ op: SQLBinaryOperator, _ right: Value) throws -> Value {
        switch op {
        case .equals:
            return .bool(left == right)
        case .notEquals:
            return .bool(left != right)
        case .plus:
            if case .int(let l) = left, case .int(let r) = right {
                return .int(l + r)
            } else if case .double(let l) = left, case .double(let r) = right {
                return .double(l + r)
            } else {
                throw SQLQueryError.invalidOperation("Cannot add \(left) and \(right)")
            }
        case .minus:
            if case .int(let l) = left, case .int(let r) = right {
                return .int(l - r)
            } else if case .double(let l) = left, case .double(let r) = right {
                return .double(l - r)
            } else {
                throw SQLQueryError.invalidOperation("Cannot subtract \(left) and \(right)")
            }
        case .multiply:
            if case .int(let l) = left, case .int(let r) = right {
                return .int(l * r)
            } else if case .double(let l) = left, case .double(let r) = right {
                return .double(l * r)
            } else {
                throw SQLQueryError.invalidOperation("Cannot multiply \(left) and \(right)")
            }
        case .divide:
            if case .int(let l) = left, case .int(let r) = right {
                return .int(l / r)
            } else if case .double(let l) = left, case .double(let r) = right {
                return .double(l / r)
            } else {
                throw SQLQueryError.invalidOperation("Cannot divide \(left) and \(right)")
            }
        default:
            throw SQLQueryError.unsupportedOperation("Binary operation \(op) not yet implemented")
        }
    }
    
    private func evaluateUnaryOperation(_ op: SQLUnaryOperator, _ operand: Value) throws -> Value {
        switch op {
        case .not:
            if case .bool(let b) = operand {
                return .bool(!b)
            } else {
                throw SQLQueryError.invalidOperation("NOT operation requires boolean operand")
            }
        case .minus:
            if case .int(let i) = operand {
                return .int(-i)
            } else if case .double(let d) = operand {
                return .double(-d)
            } else {
                throw SQLQueryError.invalidOperation("Unary minus requires numeric operand")
            }
        case .plus:
            return operand
        }
    }
    
    private func evaluateFunction(_ name: String, _ args: [SQLExpression]) throws -> Value {
        switch name.uppercased() {
        case "COUNT":
            // For now, return 0 - in a real implementation, this would count rows
            return .int(0)
        case "SUM":
            // For now, return 0 - in a real implementation, this would sum values
            return .int(0)
        case "AVG":
            // For now, return 0 - in a real implementation, this would average values
            return .double(0.0)
        case "MIN":
            // For now, return null - in a real implementation, this would find minimum
            return .null
        case "MAX":
            // For now, return null - in a real implementation, this would find maximum
            return .null
        default:
            throw SQLQueryError.unsupportedFunction("Function \(name) not yet implemented")
        }
    }
    
    private func evaluateCaseWhen(_ whenClauses: [SQLExpression.SQLWhenClause], _ elseExpression: SQLExpression?) throws -> Value {
        for whenClause in whenClauses {
            let condition = try evaluateExpression(whenClause.condition, inRow: nil)
            if case .bool(true) = condition {
                return try evaluateExpression(whenClause.result, inRow: nil)
            }
        }
        
        if let elseExpr = elseExpression {
            return try evaluateExpression(elseExpr, inRow: nil)
        }
        
        return .null
    }
    
    private func extractTableName(_ tableRef: TableReference) -> String {
        switch tableRef {
        case .table(let name, _):
            return name
        case .join(let left, _, _, _):
            return extractTableName(left)
        }
    }

    // MARK: - WHERE evaluation helpers (MVP)
    private func evaluateWhere(_ expr: SQLExpression, inRow row: Row) throws -> Bool {
        let v = try evaluateExpression(expr, inRow: row)
        if case .bool(let b) = v { return b }
        // If expression is equality/relational, evaluateBinaryOperation already returns bool
        return false
    }

    private func extractEqualsPredicate(_ expr: SQLExpression?) throws -> (String, Value)? {
        guard let expr = expr else { return nil }
        switch expr {
        case .binary(let l, .equals, let r):
            if case .column(let name) = l {
                let rv = try evaluateExpression(r, inRow: nil)
                return (name, rv)
            }
            if case .column(let name) = r {
                let lv = try evaluateExpression(l, inRow: nil)
                return (name, lv)
            }
            return nil
        default:
            return nil
        }
    }
}

// MARK: - SQL Query Errors
public enum SQLQueryError: Error, Equatable {
    case invalidQuery(String)
    case invalidOperation(String)
    case unsupportedOperation(String)
    case unsupportedFunction(String)
    case tableNotFound(String)
    case columnNotFound(String)
    case typeMismatch(String)
}

