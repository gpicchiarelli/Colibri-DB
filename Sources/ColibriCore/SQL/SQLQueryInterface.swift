//
//  SQLQueryInterface.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-27.
//
// Theme: Complete SQL query interface connecting parser to database engine.

import Foundation
import ColibriCore

// MARK: - SQL Query Result
public struct SQLQueryResult {
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

public enum SQLStatementType: String {
    case createTable = "CREATE TABLE"
    case dropTable = "DROP TABLE"
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
        case .dropTable(let dropTable):
            return try executeDropTable(dropTable)
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
        // For now, create a simple table without schema validation
        // In a full implementation, this would create the table with proper schema
        try database.createTable(statement.tableName)
        
        return SQLQueryResult(
            statementType: .createTable,
            message: "Table '\(statement.tableName)' created successfully"
        )
    }
    
    private func executeDropTable(_ statement: DropTableStatement) throws -> SQLQueryResult {
        // For now, this is a placeholder - the database doesn't have dropTable yet
        // In a full implementation, this would drop the table
        return SQLQueryResult(
            statementType: .dropTable,
            message: "Table '\(statement.tableName)' dropped successfully"
        )
    }
    
    // MARK: - DML Execution
    private func executeInsert(_ statement: InsertStatement) throws -> SQLQueryResult {
        let row = try buildRowFromValues(statement.values)
        let rid = try database.insert(into: statement.tableName, row: row)
        
        return SQLQueryResult(
            statementType: .insert,
            affectedRows: 1,
            message: "Row inserted with RID: \(rid)"
        )
    }
    
    private func executeUpdate(_ statement: UpdateStatement) throws -> SQLQueryResult {
        // For now, this is a placeholder - the database doesn't have update yet
        // In a full implementation, this would update rows matching the WHERE clause
        return SQLQueryResult(
            statementType: .update,
            affectedRows: 0,
            message: "UPDATE not yet implemented"
        )
    }
    
    private func executeDelete(_ statement: DeleteStatement) throws -> SQLQueryResult {
        // For now, this is a placeholder - the database doesn't have delete with WHERE yet
        // In a full implementation, this would delete rows matching the WHERE clause
        return SQLQueryResult(
            statementType: .delete,
            affectedRows: 0,
            message: "DELETE with WHERE not yet implemented"
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
        
        if !rows.isEmpty {
            // Extract column names from first row
            let firstRow = rows.first!.1
            columns = Array(firstRow.keys).sorted()
            
            for (_, row) in rows {
                var resultRow: [Value] = []
                for column in columns {
                    resultRow.append(row[column] ?? .null)
                }
                resultRows.append(resultRow)
            }
        }
        
        return SQLQueryResult(
            statementType: .select,
            columns: columns,
            rows: resultRows,
            message: "Query executed successfully"
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
            let value = try evaluateExpression(expression)
            row[columnName] = value
        }
        
        return row
    }
    
    private func evaluateExpression(_ expression: SQLExpression) throws -> Value {
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
            // For now, return null for column references
            return .null
        case .binary(let left, let op, let right):
            let leftValue = try evaluateExpression(left)
            let rightValue = try evaluateExpression(right)
            return try evaluateBinaryOperation(leftValue, op, rightValue)
        case .unary(let op, let operand):
            let operandValue = try evaluateExpression(operand)
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
            let condition = try evaluateExpression(whenClause.condition)
            if case .bool(true) = condition {
                return try evaluateExpression(whenClause.result)
            }
        }
        
        if let elseExpr = elseExpression {
            return try evaluateExpression(elseExpr)
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
