//
//  SQLTokenizer.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-26.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: SQL tokenizer for parsing SQL statements into tokens.

import Foundation

/// SQL token types
public enum SQLTokenType: Sendable {
    case keyword
    case identifier
    case string
    case number
    case punctuation
    case whitespace
    case comment
}

/// SQL token
public struct SQLToken: CustomStringConvertible, Sendable {
    public let type: SQLTokenType
    public let value: String
    public let position: Int
    
    public init(type: SQLTokenType, value: String, position: Int) {
        self.type = type
        self.value = value
        self.position = position
    }
    
    public var description: String {
        return "\(type): '\(value)'"
    }
}

/// SQL Keywords
private let SQL_KEYWORDS: Set<String> = [
    "SELECT", "FROM", "WHERE", "GROUP", "BY", "HAVING", "ORDER", "LIMIT", "OFFSET",
    "INSERT", "INTO", "VALUES", "UPDATE", "SET", "DELETE", "CREATE", "TABLE", "INDEX",
    "ALTER", "DROP", "ADD", "COLUMN", "CONSTRAINT", "PRIMARY", "KEY", "UNIQUE", "CHECK",
    "FOREIGN", "REFERENCES", "NOT", "NULL", "DEFAULT", "IF", "EXISTS", "DISTINCT",
    "INNER", "LEFT", "RIGHT", "FULL", "JOIN", "ON", "AS", "CASE", "WHEN", "THEN", "ELSE", "END",
    "AND", "OR", "LIKE", "IN", "BETWEEN", "IS", "EXISTS", "ALL", "ANY", "SOME",
    "UNION", "INTERSECT", "EXCEPT", "ASC", "DESC", "NULLS", "FIRST", "LAST",
    "EXPLAIN", "SHOW", "DESCRIBE", "USE", "DATABASE", "SCHEMA", "GRANT", "REVOKE",
    "COMMIT", "ROLLBACK", "BEGIN", "TRANSACTION", "SAVEPOINT", "RELEASE",
    "TRUE", "FALSE", "UNKNOWN", "CAST", "CONVERT", "EXTRACT", "CURRENT_DATE",
    "CURRENT_TIME", "CURRENT_TIMESTAMP", "LOCALTIME", "LOCALTIMESTAMP",
    "COUNT", "SUM", "AVG", "MIN", "MAX", "STDDEV", "VARIANCE", "COALESCE",
    "NULLIF", "UPPER", "LOWER", "LENGTH", "SUBSTRING", "TRIM", "LTRIM", "RTRIM",
    "REPLACE", "CONCAT", "POSITION", "CHAR_LENGTH", "OCTET_LENGTH"
]

/// SQL Punctuation
private let SQL_PUNCTUATION: Set<String> = [
    "(", ")", ",", ";", ".", "=", "!=", "<>", "<", ">", "<=", ">=", "+", "-", "*", "/", "%",
    "||", "&", "|", "^", "~", "<<", ">>", "AND", "OR", "NOT", "LIKE", "IN", "BETWEEN",
    "IS", "EXISTS", "ALL", "ANY", "SOME", "UNION", "INTERSECT", "EXCEPT"
]

/// SQL Tokenizer
public final class SQLTokenizer {
    private let input: String
    private var currentIndex: String.Index
    private var position: Int = 0
    
    public init(input: String) {
        self.input = input
        self.currentIndex = input.startIndex
    }
    
    /// Tokenizes the input SQL string
    public static func tokenize(_ sql: String) throws -> [SQLToken] {
        let tokenizer = SQLTokenizer(input: sql)
        return try tokenizer.tokenize()
    }
    
    private func tokenize() throws -> [SQLToken] {
        var tokens: [SQLToken] = []
        
        while currentIndex < input.endIndex {
            let char = input[currentIndex]
            
            // Skip whitespace
            if char.isWhitespace {
                let whitespace = try consumeWhitespace()
                if !whitespace.isEmpty {
                    tokens.append(SQLToken(type: .whitespace, value: whitespace, position: position - whitespace.count))
                }
                continue
            }
            
            // Handle comments
            if char == "-" && peekNext() == "-" {
                let comment = try consumeLineComment()
                tokens.append(SQLToken(type: .comment, value: comment, position: position - comment.count))
                continue
            }
            
            if char == "/" && peekNext() == "*" {
                let comment = try consumeBlockComment()
                tokens.append(SQLToken(type: .comment, value: comment, position: position - comment.count))
                continue
            }
            
            // Handle strings
            if char == "'" || char == "\"" {
                let string = try consumeString(quote: char)
                tokens.append(SQLToken(type: .string, value: string, position: position - string.count))
                continue
            }
            
            // Handle numbers
            if char.isNumber || (char == "-" && peekNext().isNumber) {
                let number = try consumeNumber()
                tokens.append(SQLToken(type: .number, value: number, position: position - number.count))
                continue
            }
            
            // Handle punctuation and operators
            if SQL_PUNCTUATION.contains(String(char)) || isOperatorStart(char) {
                let punctuation = try consumePunctuation()
                tokens.append(SQLToken(type: .punctuation, value: punctuation, position: position - punctuation.count))
                continue
            }
            
            // Handle identifiers and keywords
            if char.isLetter || char == "_" || char == "$" {
                let identifier = try consumeIdentifier()
                let tokenType: SQLTokenType = SQL_KEYWORDS.contains(identifier.uppercased()) ? .keyword : .identifier
                tokens.append(SQLToken(type: tokenType, value: identifier, position: position - identifier.count))
                continue
            }
            
            // Unknown character
            throw SQLTokenizerError.unexpectedCharacter(char, position)
        }
        
        return tokens
    }
    
    private func consumeWhitespace() throws -> String {
        var result = ""
        
        while currentIndex < input.endIndex && input[currentIndex].isWhitespace {
            result.append(input[currentIndex])
            advance()
        }
        
        return result
    }
    
    private func consumeLineComment() throws -> String {
        var result = ""
        
        // Consume --
        result.append(input[currentIndex])
        advance()
        result.append(input[currentIndex])
        advance()
        
        // Consume until end of line
        while currentIndex < input.endIndex && input[currentIndex] != "\n" {
            result.append(input[currentIndex])
            advance()
        }
        
        return result
    }
    
    private func consumeBlockComment() throws -> String {
        var result = ""
        
        // Consume /*
        result.append(input[currentIndex])
        advance()
        result.append(input[currentIndex])
        advance()
        
        // Consume until */
        while currentIndex < input.endIndex {
            if input[currentIndex] == "*" && peekNext() == "/" {
                result.append(input[currentIndex])
                advance()
                result.append(input[currentIndex])
                advance()
                break
            }
            result.append(input[currentIndex])
            advance()
        }
        
        return result
    }
    
    private func consumeString(quote: Character) throws -> String {
        var result = ""
        
        // Consume opening quote
        result.append(input[currentIndex])
        advance()
        
        // Consume string content
        while currentIndex < input.endIndex {
            let char = input[currentIndex]
            
            if char == quote {
                // Check for escaped quote
                if peekNext() == quote {
                    result.append(input[currentIndex])
                    advance()
                    result.append(input[currentIndex])
                    advance()
                } else {
                    // End of string
                    result.append(input[currentIndex])
                    advance()
                    break
                }
            } else {
                result.append(input[currentIndex])
                advance()
            }
        }
        
        return result
    }
    
    private func consumeNumber() throws -> String {
        var result = ""
        
        // Handle negative sign
        if input[currentIndex] == "-" {
            result.append(input[currentIndex])
            advance()
        }
        
        // Consume digits
        while currentIndex < input.endIndex && input[currentIndex].isNumber {
            result.append(input[currentIndex])
            advance()
        }
        
        // Handle decimal point
        if currentIndex < input.endIndex && input[currentIndex] == "." {
            result.append(input[currentIndex])
            advance()
            
            while currentIndex < input.endIndex && input[currentIndex].isNumber {
                result.append(input[currentIndex])
                advance()
            }
        }
        
        // Handle scientific notation
        if currentIndex < input.endIndex && (input[currentIndex] == "e" || input[currentIndex] == "E") {
            result.append(input[currentIndex])
            advance()
            
            if currentIndex < input.endIndex && (input[currentIndex] == "+" || input[currentIndex] == "-") {
                result.append(input[currentIndex])
                advance()
            }
            
            while currentIndex < input.endIndex && input[currentIndex].isNumber {
                result.append(input[currentIndex])
                advance()
            }
        }
        
        return result
    }
    
    private func consumePunctuation() throws -> String {
        var result = ""
        
        // Handle multi-character operators
        if currentIndex < input.endIndex {
            let char = input[currentIndex]
            let nextChar = peekNext()
            
            // Two-character operators
            if let twoChar = twoCharacterOperator(char, nextChar) {
                result.append(input[currentIndex])
                advance()
                result.append(input[currentIndex])
                advance()
                return twoChar
            }
            
            // Single character operators
            if SQL_PUNCTUATION.contains(String(char)) {
                result.append(input[currentIndex])
                advance()
                return String(char)
            }
        }
        
        throw SQLTokenizerError.unexpectedCharacter(input[currentIndex], position)
    }
    
    private func consumeIdentifier() throws -> String {
        var result = ""
        
        while currentIndex < input.endIndex {
            let char = input[currentIndex]
            
            if char.isLetter || char.isNumber || char == "_" || char == "$" {
                result.append(input[currentIndex])
                advance()
            } else {
                break
            }
        }
        
        return result
    }
    
    private func isOperatorStart(_ char: Character) -> Bool {
        return char == "!" || char == "<" || char == ">" || char == "=" || char == "|" || char == "&"
    }
    
    private func twoCharacterOperator(_ char: Character, _ nextChar: Character) -> String? {
        let twoChar = String(char) + String(nextChar)
        
        switch twoChar {
        case "!=", "<>", "<=", ">=", "||", "&&", "++", "--", "**", "//", "%%":
            return twoChar
        case "<<", ">>":
            return twoChar
        default:
            return nil
        }
    }
    
    private func peekNext() -> Character {
        let nextIndex = input.index(after: currentIndex)
        return nextIndex < input.endIndex ? input[nextIndex] : "\0"
    }
    
    private func advance() {
        if currentIndex < input.endIndex {
            currentIndex = input.index(after: currentIndex)
            position += 1
        }
    }
}

/// SQL Tokenizer Errors
public enum SQLTokenizerError: Error, CustomStringConvertible {
    case unexpectedCharacter(Character, Int)
    case unterminatedString(Int)
    case unterminatedComment(Int)
    
    public var description: String {
        switch self {
        case .unexpectedCharacter(let char, let position):
            return "Unexpected character '\(char)' at position \(position)"
        case .unterminatedString(let position):
            return "Unterminated string at position \(position)"
        case .unterminatedComment(let position):
            return "Unterminated comment at position \(position)"
        }
    }
}
