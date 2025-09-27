//
//  SQLTypes.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-27.
//
// Theme: Complete SQL type system for DDL/DML/DCL statements.

import Foundation

// MARK: - SQL Data Types
public enum SQLDataType: Equatable, Hashable {
    case int
    case bigint
    case text
    case varchar(Int?)
    case boolean
    case double
    case decimal(Int?, Int?)
    case date
    case timestamp
    case blob
    
    public var name: String {
        switch self {
        case .int: return "INT"
        case .bigint: return "BIGINT"
        case .text: return "TEXT"
        case .varchar(let max): return max.map { "VARCHAR(\($0))" } ?? "VARCHAR"
        case .boolean: return "BOOLEAN"
        case .double: return "DOUBLE"
        case .decimal(let precision, let scale): 
            if let p = precision, let s = scale {
                return "DECIMAL(\(p),\(s))"
            } else if let p = precision {
                return "DECIMAL(\(p))"
            } else {
                return "DECIMAL"
            }
        case .date: return "DATE"
        case .timestamp: return "TIMESTAMP"
        case .blob: return "BLOB"
        }
    }
}

// MARK: - SQL Column Definition
public struct SQLColumnDefinition: Equatable, Hashable {
    public let name: String
    public let dataType: SQLDataType
    public let nullable: Bool
    public let defaultValue: SQLExpression?
    public let primaryKey: Bool
    public let unique: Bool
    
    public init(name: String, dataType: SQLDataType, nullable: Bool = true, defaultValue: SQLExpression? = nil, primaryKey: Bool = false, unique: Bool = false) {
        self.name = name
        self.dataType = dataType
        self.nullable = nullable
        self.defaultValue = defaultValue
        self.primaryKey = primaryKey
        self.unique = unique
    }
}

// MARK: - SQL Expressions
public indirect enum SQLExpression: Equatable, Hashable {
    case literal(SQLLiteral)
    case column(String)
    case binary(SQLExpression, SQLBinaryOperator, SQLExpression)
    case unary(SQLUnaryOperator, SQLExpression)
    case function(String, [SQLExpression])
    case caseWhen([SQLWhenClause], SQLExpression?)
    
    public struct SQLWhenClause: Equatable, Hashable {
        public let condition: SQLExpression
        public let result: SQLExpression
        
        public init(condition: SQLExpression, result: SQLExpression) {
            self.condition = condition
            self.result = result
        }
    }
}

public enum SQLLiteral: Equatable, Hashable {
    case string(String)
    case integer(Int64)
    case double(Double)
    case boolean(Bool)
    case null
}

public enum SQLBinaryOperator: String, CaseIterable {
    case equals = "="
    case notEquals = "!="
    case lessThan = "<"
    case lessThanOrEqual = "<="
    case greaterThan = ">"
    case greaterThanOrEqual = ">="
    case like = "LIKE"
    case and = "AND"
    case or = "OR"
    case plus = "+"
    case minus = "-"
    case multiply = "*"
    case divide = "/"
    case modulo = "%"
}

public enum SQLUnaryOperator: String, CaseIterable {
    case not = "NOT"
    case minus = "-"
    case plus = "+"
}

// MARK: - SQL Statements
public indirect enum SQLStatement: Equatable, Hashable {
    case createTable(CreateTableStatement)
    case dropTable(DropTableStatement)
    case insert(InsertStatement)
    case update(UpdateStatement)
    case delete(DeleteStatement)
    case select(SelectStatement)
    case explain(ExplainStatement)
}

// MARK: - DDL Statements
public struct CreateTableStatement: Equatable, Hashable {
    public let tableName: String
    public let columns: [SQLColumnDefinition]
    public let constraints: [SQLConstraint]
    
    public init(tableName: String, columns: [SQLColumnDefinition], constraints: [SQLConstraint] = []) {
        self.tableName = tableName
        self.columns = columns
        self.constraints = constraints
    }
}

public struct DropTableStatement: Equatable, Hashable {
    public let tableName: String
    public let ifExists: Bool
    
    public init(tableName: String, ifExists: Bool = false) {
        self.tableName = tableName
        self.ifExists = ifExists
    }
}

// MARK: - DML Statements
public struct InsertStatement: Equatable, Hashable {
    public let tableName: String
    public let columns: [String]?
    public let values: [SQLExpression]
    
    public init(tableName: String, columns: [String]? = nil, values: [SQLExpression]) {
        self.tableName = tableName
        self.columns = columns
        self.values = values
    }
}

public struct UpdateStatement: Equatable, Hashable {
    public let tableName: String
    public let setClauses: [SetClause]
    public let whereClause: SQLExpression?
    
    public init(tableName: String, setClauses: [SetClause], whereClause: SQLExpression? = nil) {
        self.tableName = tableName
        self.setClauses = setClauses
        self.whereClause = whereClause
    }
}

public struct SetClause: Equatable, Hashable {
    public let column: String
    public let value: SQLExpression
    
    public init(column: String, value: SQLExpression) {
        self.column = column
        self.value = value
    }
}

public struct DeleteStatement: Equatable, Hashable {
    public let tableName: String
    public let whereClause: SQLExpression?
    
    public init(tableName: String, whereClause: SQLExpression? = nil) {
        self.tableName = tableName
        self.whereClause = whereClause
    }
}

// MARK: - Query Statements
public struct SelectStatement: Equatable, Hashable {
    public let columns: [SelectColumn]
    public let from: TableReference?
    public let whereClause: SQLExpression?
    public let groupBy: [SQLExpression]?
    public let having: SQLExpression?
    public let orderBy: [OrderByClause]?
    public let limit: Int?
    public let offset: Int?
    
    public init(columns: [SelectColumn], from: TableReference? = nil, whereClause: SQLExpression? = nil, groupBy: [SQLExpression]? = nil, having: SQLExpression? = nil, orderBy: [OrderByClause]? = nil, limit: Int? = nil, offset: Int? = nil) {
        self.columns = columns
        self.from = from
        self.whereClause = whereClause
        self.groupBy = groupBy
        self.having = having
        self.orderBy = orderBy
        self.limit = limit
        self.offset = offset
    }
}

public struct SelectColumn: Equatable, Hashable {
    public let expression: SQLExpression
    public let alias: String?
    
    public init(expression: SQLExpression, alias: String? = nil) {
        self.expression = expression
        self.alias = alias
    }
}

public indirect enum TableReference: Equatable, Hashable {
    case table(String, String?) // table name, alias
    case join(TableReference, JoinType, TableReference, SQLExpression?)
    
    public enum JoinType: String, CaseIterable {
        case inner = "INNER"
        case left = "LEFT"
        case right = "RIGHT"
        case full = "FULL"
    }
}

public struct OrderByClause: Equatable, Hashable {
    public let expression: SQLExpression
    public let ascending: Bool
    
    public init(expression: SQLExpression, ascending: Bool = true) {
        self.expression = expression
        self.ascending = ascending
    }
}

// MARK: - Utility Statements
public struct ExplainStatement: Equatable, Hashable {
    public let statement: SQLStatement
    
    public init(statement: SQLStatement) {
        self.statement = statement
    }
}

// MARK: - Constraints
public enum SQLConstraint: Equatable, Hashable {
    case primaryKey([String])
    case foreignKey([String], String, [String])
    case unique([String])
    case check(SQLExpression)
    case notNull(String)
}

// MARK: - SQL Parse Errors
public enum SQLParseError: Error, Equatable {
    case unexpectedToken(String)
    case expectedToken(String, actual: String?)
    case invalidSyntax(String)
    case unsupportedFeature(String)
    case endOfInput
}
