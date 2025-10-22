//
//  SQLParser.swift
//  Based on: spec/SQLParser.tla
//

import Foundation

public enum SQLToken {
    case select, from, `where`, insert, into, values, update, set, delete
    case create, table, drop, alter, index
    case and, or, not
    case equals, notEquals, lessThan, greaterThan, lessOrEqual, greaterOrEqual
    case identifier(String), number(Double), string(String)
    case comma, semicolon, leftParen, rightParen
    case asterisk, dot
}

public enum SQLParserStatement {
    case select(columns: [String], table: String, whereClause: SQLParserExpression?)
    case insert(table: String, columns: [String], values: [Value])
    case update(table: String, assignments: [(String, Value)], whereClause: SQLParserExpression?)
    case delete(table: String, whereClause: SQLParserExpression?)
    case createTable(name: String, columns: [ColumnDefinition])
    case dropTable(name: String)
}

public enum SQLParserExpression {
    case column(String)
    case literal(Value)
    case binaryOp(BinaryOperator, SQLParserExpression, SQLParserExpression)
    case unaryOp(UnaryOperator, SQLParserExpression)
}

public enum BinaryOperator {
    case equals, notEquals, lessThan, greaterThan, lessOrEqual, greaterOrEqual
    case and, or
}

public enum UnaryOperator {
    case not
}

public struct SQLParser {
    private var tokens: [SQLToken] = []
    private var position = 0
    
    public init() {}
    
    public mutating func parse(_ sql: String) throws -> SQLStatement {
        tokens = try tokenize(sql)
        position = 0
        return try parseStatement()
    }
    
    private func tokenize(_ sql: String) throws -> [SQLToken] {
        var tokens: [SQLToken] = []
        var current = ""
        var inString = false
        
        for char in sql {
            if inString {
                if char == "'" {
                    tokens.append(.string(current))
                    current = ""
                    inString = false
                } else {
                    current.append(char)
                }
            } else {
                if char.isWhitespace {
                    if !current.isEmpty {
                        tokens.append(try parseToken(current))
                        current = ""
                    }
                } else if char == "'" {
                    inString = true
                } else if "(),;*=<>.".contains(char) {
                    if !current.isEmpty {
                        tokens.append(try parseToken(current))
                        current = ""
                    }
                    tokens.append(try parseSymbol(char))
                } else {
                    current.append(char)
                }
            }
        }
        
        if !current.isEmpty {
            tokens.append(try parseToken(current))
        }
        
        return tokens
    }
    
    private func parseToken(_ token: String) throws -> SQLToken {
        let lower = token.lowercased()
        
        switch lower {
        case "select": return .select
        case "from": return .from
        case "where": return .where
        case "insert": return .insert
        case "into": return .into
        case "values": return .values
        case "update": return .update
        case "set": return .set
        case "delete": return .delete
        case "create": return .create
        case "table": return .table
        case "drop": return .drop
        case "alter": return .alter
        case "index": return .index
        case "and": return .and
        case "or": return .or
        case "not": return .not
        default:
            if let number = Double(token) {
                return .number(number)
            }
            return .identifier(token)
        }
    }
    
    private func parseSymbol(_ char: Character) throws -> SQLToken {
        switch char {
        case ",": return .comma
        case ";": return .semicolon
        case "(": return .leftParen
        case ")": return .rightParen
        case "*": return .asterisk
        case ".": return .dot
        case "=": return .equals
        case "<": return .lessThan
        case ">": return .greaterThan
        default: throw DBError.invalidData
        }
    }
    
    private mutating func parseStatement() throws -> SQLStatement {
        guard position < tokens.count else {
            throw DBError.invalidData
        }
        
        switch tokens[position] {
        case .select:
            return try parseSelect()
        case .insert:
            return try parseInsert()
        case .update:
            return try parseUpdate()
        case .delete:
            return try parseDelete()
        case .create:
            return try parseCreate()
        case .drop:
            return try parseDrop()
        default:
            throw DBError.invalidData
        }
    }
    
    private mutating func parseSelect() throws -> SQLStatement {
        position += 1
        
        var columns: [String] = []
        
        if case .asterisk = tokens[position] {
            columns = ["*"]
            position += 1
        } else {
            while position < tokens.count {
                if case .identifier(let name) = tokens[position] {
                    columns.append(name)
                    position += 1
                    
                    if case .comma = tokens[position] {
                        position += 1
                    } else {
                        break
                    }
                }
            }
        }
        
        guard case .from = tokens[position] else {
            throw DBError.invalidData
        }
        position += 1
        
        guard case .identifier(let tableName) = tokens[position] else {
            throw DBError.invalidData
        }
        position += 1
        
        var whereClause: Expression? = nil
        
        if position < tokens.count, case .where = tokens[position] {
            position += 1
            whereClause = try parseExpression()
        }
        
        return .select(columns: columns, table: tableName, whereClause: whereClause)
    }
    
    private mutating func parseInsert() throws -> SQLStatement {
        position += 1
        
        guard case .into = tokens[position] else {
            throw DBError.invalidData
        }
        position += 1
        
        guard case .identifier(let tableName) = tokens[position] else {
            throw DBError.invalidData
        }
        position += 1
        
        return .insert(table: tableName, columns: [], values: [])
    }
    
    private mutating func parseUpdate() throws -> SQLStatement {
        position += 1
        
        guard case .identifier(let tableName) = tokens[position] else {
            throw DBError.invalidData
        }
        position += 1
        
        guard case .set = tokens[position] else {
            throw DBError.invalidData
        }
        position += 1
        
        return .update(table: tableName, assignments: [], whereClause: nil)
    }
    
    private mutating func parseDelete() throws -> SQLStatement {
        position += 1
        
        guard case .from = tokens[position] else {
            throw DBError.invalidData
        }
        position += 1
        
        guard case .identifier(let tableName) = tokens[position] else {
            throw DBError.invalidData
        }
        position += 1
        
        return .delete(table: tableName, whereClause: nil)
    }
    
    private mutating func parseCreate() throws -> SQLStatement {
        position += 1
        
        guard case .table = tokens[position] else {
            throw DBError.invalidData
        }
        position += 1
        
        guard case .identifier(let tableName) = tokens[position] else {
            throw DBError.invalidData
        }
        position += 1
        
        return .createTable(name: tableName, columns: [])
    }
    
    private mutating func parseDrop() throws -> SQLStatement {
        position += 1
        
        guard case .table = tokens[position] else {
            throw DBError.invalidData
        }
        position += 1
        
        guard case .identifier(let tableName) = tokens[position] else {
            throw DBError.invalidData
        }
        position += 1
        
        return .dropTable(name: tableName)
    }
    
    private mutating func parseExpression() throws -> Expression {
        return .column("dummy")
    }
}

