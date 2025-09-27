//
//  SQLLexer.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-27.
//
// Theme: SQL tokenizer converting text to structured tokens.

import Foundation

// MARK: - SQL Tokens
public enum SQLToken: Equatable, Hashable {
    case keyword(String)
    case identifier(String)
    case literal(SQLLiteral)
    case operator_(String)
    case punctuation(String)
    case eof
    
    public var isKeyword: Bool {
        if case .keyword = self { return true }
        return false
    }
    
    public var isIdentifier: Bool {
        if case .identifier = self { return true }
        return false
    }
    
    public var isLiteral: Bool {
        if case .literal = self { return true }
        return false
    }
    
    public var isOperator: Bool {
        if case .operator_ = self { return true }
        return false
    }
    
    public var isPunctuation: Bool {
        if case .punctuation = self { return true }
        return false
    }
}

// MARK: - SQL Lexer
public struct SQLLexer {
    private let input: String
    private var position: String.Index
    private var currentChar: Character?
    
    public init(input: String) {
        self.input = input
        self.position = input.startIndex
        self.currentChar = input.isEmpty ? nil : input[position]
    }
    
    public mutating func tokenize() throws -> [SQLToken] {
        var tokens: [SQLToken] = []
        
        while let char = currentChar {
            // Skip whitespace
            if char.isWhitespace {
                advance()
                continue
            }
            
            // Comments
            if char == "-" && peek() == "-" {
                skipLineComment()
                continue
            }
            
            if char == "/" && peek() == "*" {
                try skipBlockComment()
                continue
            }
            
            // String literals
            if char == "'" {
                let token = try scanStringLiteral()
                tokens.append(token)
                continue
            }
            
            // Numeric literals
            if char.isNumber {
                let token = try scanNumericLiteral()
                tokens.append(token)
                continue
            }
            
            // Identifiers and keywords
            if char.isLetter || char == "_" {
                let token = scanIdentifierOrKeyword()
                tokens.append(token)
                continue
            }
            
            // Operators and punctuation
            if let token = scanOperatorOrPunctuation() {
                tokens.append(token)
                continue
            }
            
            throw SQLParseError.unexpectedToken(String(char))
        }
        
        tokens.append(.eof)
        return tokens
    }
    
    // MARK: - Character Navigation
    private mutating func advance() {
        if position < input.endIndex {
            position = input.index(after: position)
            currentChar = position < input.endIndex ? input[position] : nil
        } else {
            currentChar = nil
        }
    }
    
    private func peek() -> Character? {
        let nextIndex = input.index(after: position)
        return nextIndex < input.endIndex ? input[nextIndex] : nil
    }
    
    // MARK: - Token Scanning
    private mutating func scanStringLiteral() throws -> SQLToken {
        advance() // Skip opening quote
        var value = ""
        
        while let char = currentChar {
            if char == "'" {
                advance() // Skip closing quote
                return .literal(.string(value))
            }
            
            if char == "\\" {
                advance()
                guard let nextChar = currentChar else {
                    throw SQLParseError.invalidSyntax("Incomplete escape sequence")
                }
                value.append(escapeCharacter(nextChar))
                advance()
            } else {
                value.append(char)
                advance()
            }
        }
        
        throw SQLParseError.invalidSyntax("Unterminated string literal")
    }
    
    private func escapeCharacter(_ char: Character) -> Character {
        switch char {
        case "n": return "\n"
        case "t": return "\t"
        case "r": return "\r"
        case "\\": return "\\"
        case "'": return "'"
        default: return char
        }
    }
    
    private mutating func scanNumericLiteral() throws -> SQLToken {
        var value = ""
        var hasDecimal = false
        
        while let char = currentChar {
            if char.isNumber {
                value.append(char)
                advance()
            } else if char == "." && !hasDecimal {
                hasDecimal = true
                value.append(char)
                advance()
            } else {
                break
            }
        }
        
        if hasDecimal {
            guard let doubleValue = Double(value) else {
                throw SQLParseError.invalidSyntax("Invalid decimal number: \(value)")
            }
            return .literal(.double(doubleValue))
        } else {
            guard let intValue = Int64(value) else {
                throw SQLParseError.invalidSyntax("Invalid integer: \(value)")
            }
            return .literal(.integer(intValue))
        }
    }
    
    private mutating func scanIdentifierOrKeyword() -> SQLToken {
        var value = ""
        
        while let char = currentChar {
            if char.isLetter || char.isNumber || char == "_" {
                value.append(char)
                advance()
            } else {
                break
            }
        }
        
        let upperValue = value.uppercased()
        if SQLKeywords.contains(upperValue) {
            return .keyword(upperValue)
        } else {
            return .identifier(value)
        }
    }
    
    private mutating func scanOperatorOrPunctuation() -> SQLToken? {
        guard let char = currentChar else { return nil }
        
        // Two-character operators
        if let nextChar = peek() {
            let twoChar = String(char) + String(nextChar)
            if SQLTwoCharOperators.contains(twoChar) {
                advance()
                advance()
                return .operator_(twoChar)
            }
        }
        
        // Single-character operators and punctuation
        if SQLSingleCharOperators.contains(String(char)) {
            advance()
            return .operator_(String(char))
        }
        
        if SQLPunctuation.contains(String(char)) {
            advance()
            return .punctuation(String(char))
        }
        
        return nil
    }
    
    // MARK: - Comment Handling
    private mutating func skipLineComment() {
        while let char = currentChar, char != "\n" {
            advance()
        }
        if currentChar == "\n" {
            advance()
        }
    }
    
    private mutating func skipBlockComment() throws {
        advance() // Skip first /
        advance() // Skip *
        
        while let char = currentChar {
            if char == "*" && peek() == "/" {
                advance() // Skip *
                advance() // Skip /
                return
            }
            advance()
        }
        
        throw SQLParseError.invalidSyntax("Unterminated block comment")
    }
}

// MARK: - SQL Keywords
private let SQLKeywords: Set<String> = [
    "SELECT", "FROM", "WHERE", "GROUP", "BY", "HAVING", "ORDER", "LIMIT", "OFFSET",
    "INSERT", "INTO", "VALUES", "UPDATE", "SET", "DELETE",
    "CREATE", "TABLE", "DROP", "ALTER", "INDEX",
    "PRIMARY", "KEY", "FOREIGN", "UNIQUE", "NOT", "NULL", "DEFAULT",
    "INT", "BIGINT", "TEXT", "VARCHAR", "BOOLEAN", "DOUBLE", "DECIMAL", "DATE", "TIMESTAMP", "BLOB",
    "AND", "OR", "NOT", "LIKE", "IN", "BETWEEN", "IS", "EXISTS",
    "INNER", "LEFT", "RIGHT", "FULL", "JOIN", "ON", "USING",
    "CASE", "WHEN", "THEN", "ELSE", "END",
    "COUNT", "SUM", "AVG", "MIN", "MAX", "DISTINCT",
    "ASC", "DESC", "EXPLAIN", "IF", "EXISTS"
]

private let SQLTwoCharOperators: Set<String> = [
    "!=", "<=", ">=", "||", "&&"
]

private let SQLSingleCharOperators: Set<String> = [
    "=", "<", ">", "+", "-", "*", "/", "%", "&", "|", "^", "~"
]

private let SQLPunctuation: Set<String> = [
    "(", ")", ",", ";", ".", "[", "]", "{", "}"
]
