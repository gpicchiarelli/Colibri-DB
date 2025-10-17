//
//  SQLParser.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-09-27.
//
// Theme: Complete SQL parser for DDL/DML/DCL statements.

import Foundation

// MARK: - SQL Parser
public struct SQLParser {
    private var tokens: [SQLToken]
    private var position: Int = 0
    
    public init(tokens: [SQLToken]) {
        self.tokens = tokens
    }
    
    // 🔧 FIX: SQL Injection Prevention with input validation and sanitization
    public static func parse(_ sql: String) throws -> SQLStatement {
        // Input validation
        try validateSQLInput(sql)
        
        // Sanitize input
        let sanitizedSQL = try sanitizeSQLInput(sql)
        
        var lexer = SQLLexer(input: sanitizedSQL)
        let tokens = try lexer.tokenize()
        
        // Additional token validation
        try validateTokens(tokens)
        
        var parser = SQLParser(tokens: tokens)
        return try parser.parseStatement()
    }
    
    // MARK: - Security & Validation
    
    /// 🔧 FIX: Comprehensive SQL input validation
    private static func validateSQLInput(_ sql: String) throws {
        // Check for null bytes and control characters
        if sql.contains("\0") {
            throw SQLParseError.invalidInput("SQL contains null bytes")
        }
        
        // Check for excessive length (prevent DoS)
        let maxLength = 1_000_000 // 1MB limit
        if sql.count > maxLength {
            throw SQLParseError.invalidInput("SQL statement too long (max: \(maxLength) characters)")
        }
        
        // Check for suspicious patterns that might indicate injection
        let suspiciousPatterns = [
            // SQL injection patterns
            "\\bunion\\s+select\\b",
            "\\bor\\s+1\\s*=\\s*1\\b",
            "\\band\\s+1\\s*=\\s*1\\b",
            "\\bor\\s+'.*'\\s*=\\s*'.*'\\b",
            // Command injection patterns
            "\\bexec\\s*\\(",
            "\\beval\\s*\\(",
            "\\bsystem\\s*\\(",
            // Path traversal in string literals
            "\\.\\./",
            "\\\\\\.\\.\\\\",
            // Excessive nested queries
            "\\(\\s*select\\s+.*\\(\\s*select\\s+.*\\(\\s*select"
        ]
        
        for pattern in suspiciousPatterns {
            let regex = try NSRegularExpression(pattern: pattern, options: [.caseInsensitive])
            let range = NSRange(location: 0, length: sql.utf16.count)
            if regex.firstMatch(in: sql, options: [], range: range) != nil {
                throw SQLParseError.suspiciousInput("Potentially malicious SQL pattern detected: \(pattern)")
            }
        }
        
        // Check for excessive semicolons (multiple statements)
        let semicolonCount = sql.filter { $0 == ";" }.count
        if semicolonCount > 1 {
            throw SQLParseError.invalidInput("Multiple statements not allowed (found \(semicolonCount) semicolons)")
        }
        
        print("✅ SQL input validation passed")
    }
    
    /// 🔧 FIX: SQL input sanitization
    private static func sanitizeSQLInput(_ sql: String) throws -> String {
        var sanitized = sql
        
        // Remove dangerous control characters but preserve newlines and tabs
        sanitized = sanitized.filter { char in
            char.isASCII && (char.isWhitespace || char.isLetter || char.isNumber || char.isPunctuation || char.isSymbol || char == "\n" || char == "\t")
        }
        
        // Normalize whitespace
        sanitized = sanitized.replacingOccurrences(
            of: "\\s+", 
            with: " ", 
            options: .regularExpression
        ).trimmingCharacters(in: .whitespacesAndNewlines)
        
        // Remove comments that could hide malicious code
        // Note: This is aggressive - in production you might want to preserve legitimate comments
        sanitized = sanitized.replacingOccurrences(
            of: "--.*$", 
            with: "", 
            options: .regularExpression
        )
        
        sanitized = sanitized.replacingOccurrences(
            of: "/\\*.*?\\*/", 
            with: "", 
            options: .regularExpression
        )
        
        print("✅ SQL input sanitized")
        return sanitized
    }
    
    /// 🔧 FIX: Token-level validation
    private static func validateTokens(_ tokens: [SQLToken]) throws {
        // Check for excessive token count (DoS prevention)
        let maxTokens = 10_000
        if tokens.count > maxTokens {
            throw SQLParseError.invalidInput("Too many tokens (max: \(maxTokens))")
        }
        
        // Check for suspicious token patterns
        var consecutiveStrings = 0
        var consecutiveOperators = 0
        
        for token in tokens {
            switch token {
            case .literal(.string(_)):
                consecutiveStrings += 1
                consecutiveOperators = 0
                
                // Prevent excessive string concatenation attacks
                if consecutiveStrings > 50 {
                    throw SQLParseError.suspiciousInput("Excessive string literals detected")
                }
                
            case .operator_(_):
                consecutiveOperators += 1
                consecutiveStrings = 0
                
                // Prevent operator flooding
                if consecutiveOperators > 20 {
                    throw SQLParseError.suspiciousInput("Excessive operators detected")
                }
                
            default:
                consecutiveStrings = 0
                consecutiveOperators = 0
            }
        }
        
        print("✅ Token validation passed (\(tokens.count) tokens)")
    }
    
    // MARK: - Main Parse Methods
    public mutating func parseStatement() throws -> SQLStatement {
        let token = try currentToken()
        
        switch token {
        case .keyword("CREATE"):
            return try parseCreateStatement()
        case .keyword("DROP"):
            return try parseDropStatement()
        case .keyword("INSERT"):
            return try parseInsertStatement()
        case .keyword("UPDATE"):
            return try parseUpdateStatement()
        case .keyword("DELETE"):
            return try parseDeleteStatement()
        case .keyword("SELECT"):
            return try parseSelectStatement()
        case .keyword("EXPLAIN"):
            return try parseExplainStatement()
        default:
            throw SQLParseError.unexpectedToken("Expected statement keyword")
        }
    }
    
    // MARK: - DDL Parsing
    private mutating func parseCreateStatement() throws -> SQLStatement {
        try consume(.keyword("CREATE"))
        
        let token = try currentToken()
        switch token {
        case .keyword("TABLE"):
            return try parseCreateTableStatement()
        case .keyword("INDEX"):
            return try parseCreateIndexStatement()
        default:
            throw SQLParseError.expectedToken("TABLE or INDEX", actual: tokenDescription(token))
        }
    }
    
    private mutating func parseCreateTableStatement() throws -> SQLStatement {
        try consume(.keyword("TABLE"))
        
        let tableName = try parseIdentifier()
        try consume(.punctuation("("))
        
        var columns: [SQLColumnDefinition] = []
        var constraints: [SQLConstraint] = []
        
        while !isCurrentToken(.punctuation(")")) {
            if isCurrentToken(.keyword("PRIMARY")) || isCurrentToken(.keyword("FOREIGN")) || 
               isCurrentToken(.keyword("UNIQUE")) || isCurrentToken(.keyword("CHECK")) {
                let constraint = try parseConstraint()
                constraints.append(constraint)
            } else {
                let column = try parseColumnDefinition()
                columns.append(column)
            }
            
            if isCurrentToken(.punctuation(",")) {
                try consume(.punctuation(","))
            }
        }
        
        try consume(.punctuation(")"))
        
        return .createTable(CreateTableStatement(tableName: tableName, columns: columns, constraints: constraints))
    }

    private mutating func parseCreateIndexStatement() throws -> SQLStatement {
        try consume(.keyword("INDEX"))
        let name = try parseIdentifier()
        try consume(.keyword("ON"))
        let tableName = try parseIdentifier()
        try consume(.punctuation("("))
        var columns: [String] = []
        while !isCurrentToken(.punctuation(")")) {
            columns.append(try parseIdentifier())
            if isCurrentToken(.punctuation(",")) { try consume(.punctuation(",")) }
        }
        try consume(.punctuation(")"))
        var usingKind: String? = nil
        if isCurrentToken(.keyword("USING")) {
            try consume(.keyword("USING"))
            usingKind = try parseIdentifier()
        }
        return .createIndex(CreateIndexStatement(name: name, tableName: tableName, columns: columns, usingKind: usingKind))
    }
    
    private mutating func parseColumnDefinition() throws -> SQLColumnDefinition {
        let name = try parseIdentifier()
        let dataType = try parseDataType()
        
        var nullable = true
        var defaultValue: SQLExpression?
        var primaryKey = false
        var unique = false
        
        while !isCurrentToken(.punctuation(",")) && !isCurrentToken(.punctuation(")")) {
            let token = try currentToken()
            switch token {
            case .keyword("NOT"):
                try consume(.keyword("NOT"))
                try consume(.keyword("NULL"))
                nullable = false
            case .keyword("PRIMARY"):
                try consume(.keyword("PRIMARY"))
                try consume(.keyword("KEY"))
                primaryKey = true
            case .keyword("UNIQUE"):
                try consume(.keyword("UNIQUE"))
                unique = true
            case .keyword("DEFAULT"):
                try consume(.keyword("DEFAULT"))
                defaultValue = try parseExpression()
            default:
                break
            }
        }
        
        return SQLColumnDefinition(name: name, dataType: dataType, nullable: nullable, 
                                 defaultValue: defaultValue, primaryKey: primaryKey, unique: unique)
    }
    
    private mutating func parseDataType() throws -> SQLDataType {
        let token = try currentToken()
        
        switch token {
        case .keyword("INT"):
            try consume(.keyword("INT"))
            return .int
        case .keyword("BIGINT"):
            try consume(.keyword("BIGINT"))
            return .bigint
        case .keyword("TEXT"):
            try consume(.keyword("TEXT"))
            return .text
        case .keyword("VARCHAR"):
            try consume(.keyword("VARCHAR"))
            if isCurrentToken(.punctuation("(")) {
                try consume(.punctuation("("))
                let length = try parseIntegerLiteral()
                try consume(.punctuation(")"))
                return .varchar(Int(length))
            }
            return .varchar(nil)
        case .keyword("BOOLEAN"):
            try consume(.keyword("BOOLEAN"))
            return .boolean
        case .keyword("DOUBLE"):
            try consume(.keyword("DOUBLE"))
            return .double
        case .keyword("DECIMAL"):
            try consume(.keyword("DECIMAL"))
            if isCurrentToken(.punctuation("(")) {
                try consume(.punctuation("("))
                let precision = try parseIntegerLiteral()
                if isCurrentToken(.punctuation(",")) {
                    try consume(.punctuation(","))
                    let scale = try parseIntegerLiteral()
                    try consume(.punctuation(")"))
                    return .decimal(Int(precision), Int(scale))
                } else {
                    try consume(.punctuation(")"))
                    return .decimal(Int(precision), nil)
                }
            }
            return .decimal(nil, nil)
        case .keyword("DATE"):
            try consume(.keyword("DATE"))
            return .date
        case .keyword("TIMESTAMP"):
            try consume(.keyword("TIMESTAMP"))
            return .timestamp
        case .keyword("BLOB"):
            try consume(.keyword("BLOB"))
            return .blob
        default:
            throw SQLParseError.expectedToken("data type", actual: tokenDescription(token))
        }
    }
    
    private mutating func parseConstraint() throws -> SQLConstraint {
        let token = try currentToken()
        
        switch token {
        case .keyword("PRIMARY"):
            try consume(.keyword("PRIMARY"))
            try consume(.keyword("KEY"))
            try consume(.punctuation("("))
            var columns: [String] = []
            while !isCurrentToken(.punctuation(")")) {
                columns.append(try parseIdentifier())
                if isCurrentToken(.punctuation(",")) {
                    try consume(.punctuation(","))
                }
            }
            try consume(.punctuation(")"))
            return .primaryKey(columns)
            
        case .keyword("FOREIGN"):
            try consume(.keyword("FOREIGN"))
            try consume(.keyword("KEY"))
            try consume(.punctuation("("))
            var localColumns: [String] = []
            while !isCurrentToken(.punctuation(")")) {
                localColumns.append(try parseIdentifier())
                if isCurrentToken(.punctuation(",")) {
                    try consume(.punctuation(","))
                }
            }
            try consume(.punctuation(")"))
            try consume(.keyword("REFERENCES"))
            let refTable = try parseIdentifier()
            try consume(.punctuation("("))
            var refColumns: [String] = []
            while !isCurrentToken(.punctuation(")")) {
                refColumns.append(try parseIdentifier())
                if isCurrentToken(.punctuation(",")) {
                    try consume(.punctuation(","))
                }
            }
            try consume(.punctuation(")"))
            return .foreignKey(localColumns, refTable, refColumns)
            
        case .keyword("UNIQUE"):
            try consume(.keyword("UNIQUE"))
            try consume(.punctuation("("))
            var columns: [String] = []
            while !isCurrentToken(.punctuation(")")) {
                columns.append(try parseIdentifier())
                if isCurrentToken(.punctuation(",")) {
                    try consume(.punctuation(","))
                }
            }
            try consume(.punctuation(")"))
            return .unique(columns)
            
        case .keyword("CHECK"):
            try consume(.keyword("CHECK"))
            try consume(.punctuation("("))
            let expression = try parseExpression()
            try consume(.punctuation(")"))
            return .check(expression)
            
        default:
            throw SQLParseError.expectedToken("constraint type", actual: tokenDescription(token))
        }
    }
    
    private mutating func parseDropStatement() throws -> SQLStatement {
        try consume(.keyword("DROP"))
        let token = try currentToken()
        switch token {
        case .keyword("TABLE"):
            try consume(.keyword("TABLE"))
            let ifExists = isCurrentToken(.keyword("IF"))
            if ifExists {
                try consume(.keyword("IF"))
                try consume(.keyword("EXISTS"))
            }
            let tableName = try parseIdentifier()
            return .dropTable(DropTableStatement(tableName: tableName, ifExists: ifExists))
        case .keyword("INDEX"):
            try consume(.keyword("INDEX"))
            let ifExists = isCurrentToken(.keyword("IF"))
            if ifExists {
                try consume(.keyword("IF"))
                try consume(.keyword("EXISTS"))
            }
            let indexName = try parseIdentifier()
            try consume(.keyword("ON"))
            let tableName = try parseIdentifier()
            return .dropIndex(DropIndexStatement(indexName: indexName, tableName: tableName, ifExists: ifExists))
        default:
            throw SQLParseError.expectedToken("TABLE or INDEX", actual: tokenDescription(token))
        }
    }
    
    // MARK: - DML Parsing
    private mutating func parseInsertStatement() throws -> SQLStatement {
        try consume(.keyword("INSERT"))
        try consume(.keyword("INTO"))
        
        let tableName = try parseIdentifier()
        
        var columns: [String]?
        if isCurrentToken(.punctuation("(")) {
            try consume(.punctuation("("))
            columns = []
            while !isCurrentToken(.punctuation(")")) {
                columns!.append(try parseIdentifier())
                if isCurrentToken(.punctuation(",")) {
                    try consume(.punctuation(","))
                }
            }
            try consume(.punctuation(")"))
        }
        
        try consume(.keyword("VALUES"))
        try consume(.punctuation("("))
        
        var values: [SQLExpression] = []
        while !isCurrentToken(.punctuation(")")) {
            values.append(try parseExpression())
            if isCurrentToken(.punctuation(",")) {
                try consume(.punctuation(","))
            }
        }
        try consume(.punctuation(")"))
        
        return .insert(InsertStatement(tableName: tableName, columns: columns, values: values))
    }
    
    private mutating func parseUpdateStatement() throws -> SQLStatement {
        try consume(.keyword("UPDATE"))
        let tableName = try parseIdentifier()
        try consume(.keyword("SET"))
        
        var setClauses: [SetClause] = []
        while !isCurrentToken(.keyword("WHERE")) && !isCurrentToken(.eof) {
            let column = try parseIdentifier()
            try consume(.operator_("="))
            let value = try parseExpression()
            setClauses.append(SetClause(column: column, value: value))
            
            if isCurrentToken(.punctuation(",")) {
                try consume(.punctuation(","))
            }
        }
        
        var whereClause: SQLExpression?
        if isCurrentToken(.keyword("WHERE")) {
            try consume(.keyword("WHERE"))
            whereClause = try parseExpression()
        }
        
        return .update(UpdateStatement(tableName: tableName, setClauses: setClauses, whereClause: whereClause))
    }
    
    private mutating func parseDeleteStatement() throws -> SQLStatement {
        try consume(.keyword("DELETE"))
        try consume(.keyword("FROM"))
        let tableName = try parseIdentifier()
        
        var whereClause: SQLExpression?
        if isCurrentToken(.keyword("WHERE")) {
            try consume(.keyword("WHERE"))
            whereClause = try parseExpression()
        }
        
        return .delete(DeleteStatement(tableName: tableName, whereClause: whereClause))
    }
    
    // MARK: - Query Parsing
    private mutating func parseSelectStatement() throws -> SQLStatement {
        try consume(.keyword("SELECT"))
        
        var columns: [SelectColumn] = []
        if isCurrentToken(.operator_("*")) {
            try consume(.operator_("*"))
            columns.append(SelectColumn(expression: .column("*")))
        } else {
            while !isCurrentToken(.keyword("FROM")) && !isCurrentToken(.eof) {
                let expression = try parseExpression()
                var alias: String?
                if isCurrentToken(.keyword("AS")) {
                    try consume(.keyword("AS"))
                    alias = try parseIdentifier()
                } else if isCurrentToken(.identifier("")) && !isCurrentToken(.keyword("FROM")) {
                    // Check if next token is identifier (alias without AS)
                    let nextToken = try peekToken()
                    if case .identifier = nextToken {
                        alias = try parseIdentifier()
                    }
                }
                columns.append(SelectColumn(expression: expression, alias: alias))
                
                if isCurrentToken(.punctuation(",")) {
                    try consume(.punctuation(","))
                }
            }
        }
        
        var from: TableReference?
        if isCurrentToken(.keyword("FROM")) {
            try consume(.keyword("FROM"))
            from = try parseTableReference()
        }
        
        var whereClause: SQLExpression?
        if isCurrentToken(.keyword("WHERE")) {
            try consume(.keyword("WHERE"))
            whereClause = try parseExpression()
        }
        
        var groupBy: [SQLExpression]?
        if isCurrentToken(.keyword("GROUP")) {
            try consume(.keyword("GROUP"))
            try consume(.keyword("BY"))
            groupBy = []
            while !isCurrentToken(.keyword("HAVING")) && !isCurrentToken(.keyword("ORDER")) && !isCurrentToken(.keyword("LIMIT")) && !isCurrentToken(.eof) {
                groupBy!.append(try parseExpression())
                if isCurrentToken(.punctuation(",")) {
                    try consume(.punctuation(","))
                }
            }
        }
        
        var having: SQLExpression?
        if isCurrentToken(.keyword("HAVING")) {
            try consume(.keyword("HAVING"))
            having = try parseExpression()
        }
        
        var orderBy: [OrderByClause]?
        if isCurrentToken(.keyword("ORDER")) {
            try consume(.keyword("ORDER"))
            try consume(.keyword("BY"))
            orderBy = []
            while !isCurrentToken(.keyword("LIMIT")) && !isCurrentToken(.eof) {
                let expression = try parseExpression()
                var ascending = true
                if isCurrentToken(.keyword("ASC")) {
                    try consume(.keyword("ASC"))
                    ascending = true
                } else if isCurrentToken(.keyword("DESC")) {
                    try consume(.keyword("DESC"))
                    ascending = false
                }
                orderBy!.append(OrderByClause(expression: expression, ascending: ascending))
                
                if isCurrentToken(.punctuation(",")) {
                    try consume(.punctuation(","))
                }
            }
        }
        
        var limit: Int?
        if isCurrentToken(.keyword("LIMIT")) {
            try consume(.keyword("LIMIT"))
            limit = Int(try parseIntegerLiteral())
        }
        
        var offset: Int?
        if isCurrentToken(.keyword("OFFSET")) {
            try consume(.keyword("OFFSET"))
            offset = Int(try parseIntegerLiteral())
        }
        
        return .select(SelectStatement(columns: columns, from: from, whereClause: whereClause, 
                                     groupBy: groupBy, having: having, orderBy: orderBy, 
                                     limit: limit, offset: offset))
    }
    
    private mutating func parseTableReference() throws -> TableReference {
        let tableName = try parseIdentifier()
        var alias: String?
        
        if isCurrentToken(.keyword("AS")) {
            try consume(.keyword("AS"))
            alias = try parseIdentifier()
        } else if isCurrentToken(.identifier("")) {
            // Check if next token is identifier (alias without AS)
            let nextToken = try peekToken()
            if case .identifier = nextToken {
                alias = try parseIdentifier()
            }
        }
        
        var result: TableReference = .table(tableName, alias)
        
        // Parse joins
        while isCurrentToken(.keyword("INNER")) || isCurrentToken(.keyword("LEFT")) || 
              isCurrentToken(.keyword("RIGHT")) || isCurrentToken(.keyword("FULL")) || 
              isCurrentToken(.keyword("JOIN")) {
            
            let joinType: TableReference.JoinType
            if isCurrentToken(.keyword("INNER")) {
                try consume(.keyword("INNER"))
                joinType = .inner
            } else if isCurrentToken(.keyword("LEFT")) {
                try consume(.keyword("LEFT"))
                joinType = .left
            } else if isCurrentToken(.keyword("RIGHT")) {
                try consume(.keyword("RIGHT"))
                joinType = .right
            } else if isCurrentToken(.keyword("FULL")) {
                try consume(.keyword("FULL"))
                joinType = .full
            } else {
                joinType = .inner
            }
            
            try consume(.keyword("JOIN"))
            let rightTable = try parseTableReference()
            
            var condition: SQLExpression?
            if isCurrentToken(.keyword("ON")) {
                try consume(.keyword("ON"))
                condition = try parseExpression()
            }
            
            result = .join(result, joinType, rightTable, condition)
        }
        
        return result
    }
    
    private mutating func parseExplainStatement() throws -> SQLStatement {
        try consume(.keyword("EXPLAIN"))
        let statement = try parseStatement()
        return .explain(ExplainStatement(statement: statement))
    }
    
    // MARK: - Expression Parsing
    private mutating func parseExpression() throws -> SQLExpression {
        return try parseOrExpression()
    }
    
    private mutating func parseOrExpression() throws -> SQLExpression {
        var left = try parseAndExpression()
        
        while isCurrentToken(.keyword("OR")) {
            try consume(.keyword("OR"))
            let right = try parseAndExpression()
            left = .binary(left, .or, right)
        }
        
        return left
    }
    
    private mutating func parseAndExpression() throws -> SQLExpression {
        var left = try parseEqualityExpression()
        
        while isCurrentToken(.keyword("AND")) {
            try consume(.keyword("AND"))
            let right = try parseEqualityExpression()
            left = .binary(left, .and, right)
        }
        
        return left
    }
    
    private mutating func parseEqualityExpression() throws -> SQLExpression {
        var left = try parseRelationalExpression()
        
        while isCurrentToken(.operator_("=")) || isCurrentToken(.operator_("!=")) {
            let op: SQLBinaryOperator = isCurrentToken(.operator_("=")) ? .equals : .notEquals
            try consumeCurrentToken()
            let right = try parseRelationalExpression()
            left = .binary(left, op, right)
        }
        
        return left
    }
    
    private mutating func parseRelationalExpression() throws -> SQLExpression {
        var left = try parseAdditiveExpression()
        
        while isCurrentToken(.operator_("<")) || isCurrentToken(.operator_("<=")) ||
              isCurrentToken(.operator_(">")) || isCurrentToken(.operator_(">=")) {
            let op: SQLBinaryOperator
            if isCurrentToken(.operator_("<")) {
                op = .lessThan
            } else if isCurrentToken(.operator_("<=")) {
                op = .lessThanOrEqual
            } else if isCurrentToken(.operator_(">")) {
                op = .greaterThan
            } else {
                op = .greaterThanOrEqual
            }
            try consumeCurrentToken()
            let right = try parseAdditiveExpression()
            left = .binary(left, op, right)
        }
        
        return left
    }
    
    private mutating func parseAdditiveExpression() throws -> SQLExpression {
        var left = try parseMultiplicativeExpression()
        
        while isCurrentToken(.operator_("+")) || isCurrentToken(.operator_("-")) {
            let op: SQLBinaryOperator = isCurrentToken(.operator_("+")) ? .plus : .minus
            try consumeCurrentToken()
            let right = try parseMultiplicativeExpression()
            left = .binary(left, op, right)
        }
        
        return left
    }
    
    private mutating func parseMultiplicativeExpression() throws -> SQLExpression {
        var left = try parseUnaryExpression()
        
        while isCurrentToken(.operator_("*")) || isCurrentToken(.operator_("/")) || isCurrentToken(.operator_("%")) {
            let op: SQLBinaryOperator
            if isCurrentToken(.operator_("*")) {
                op = .multiply
            } else if isCurrentToken(.operator_("/")) {
                op = .divide
            } else {
                op = .modulo
            }
            try consumeCurrentToken()
            let right = try parseUnaryExpression()
            left = .binary(left, op, right)
        }
        
        return left
    }
    
    private mutating func parseUnaryExpression() throws -> SQLExpression {
        if isCurrentToken(.keyword("NOT")) {
            try consume(.keyword("NOT"))
            let operand = try parsePrimaryExpression()
            return .unary(.not, operand)
        } else if isCurrentToken(.operator_("-")) {
            try consume(.operator_("-"))
            let operand = try parsePrimaryExpression()
            return .unary(.minus, operand)
        } else if isCurrentToken(.operator_("+")) {
            try consume(.operator_("+"))
            let operand = try parsePrimaryExpression()
            return .unary(.plus, operand)
        } else {
            return try parsePrimaryExpression()
        }
    }
    
    private mutating func parsePrimaryExpression() throws -> SQLExpression {
        let token = try currentToken()
        
        switch token {
        case .literal(let literal):
            try consumeCurrentToken()
            return .literal(literal)
            
        case .identifier(let name):
            try consumeCurrentToken()
            
            // Check if it's a function call
            if isCurrentToken(.punctuation("(")) {
                try consume(.punctuation("("))
                var arguments: [SQLExpression] = []
                
                if !isCurrentToken(.punctuation(")")) {
                    while true {
                        arguments.append(try parseExpression())
                        if isCurrentToken(.punctuation(",")) {
                            try consume(.punctuation(","))
                        } else {
                            break
                        }
                    }
                }
                
                try consume(.punctuation(")"))
                return .function(name, arguments)
            } else {
                return .column(name)
            }
            
        case .punctuation("("):
            try consume(.punctuation("("))
            let expression = try parseExpression()
            try consume(.punctuation(")"))
            return expression
            
        case .keyword("CASE"):
            return try parseCaseExpression()
            
        default:
            throw SQLParseError.unexpectedToken("Expected expression")
        }
    }
    
    private mutating func parseCaseExpression() throws -> SQLExpression {
        try consume(.keyword("CASE"))
        
        var whenClauses: [SQLExpression.SQLWhenClause] = []
        
        while isCurrentToken(.keyword("WHEN")) {
            try consume(.keyword("WHEN"))
            let condition = try parseExpression()
            try consume(.keyword("THEN"))
            let result = try parseExpression()
            whenClauses.append(SQLExpression.SQLWhenClause(condition: condition, result: result))
        }
        
        var elseExpression: SQLExpression?
        if isCurrentToken(.keyword("ELSE")) {
            try consume(.keyword("ELSE"))
            elseExpression = try parseExpression()
        }
        
        try consume(.keyword("END"))
        
        return .caseWhen(whenClauses, elseExpression)
    }
    
    // MARK: - Helper Methods
    private func currentToken() throws -> SQLToken {
        guard position < tokens.count else {
            throw SQLParseError.endOfInput
        }
        return tokens[position]
    }
    
    private func peekToken() throws -> SQLToken {
        guard position + 1 < tokens.count else {
            return .eof
        }
        return tokens[position + 1]
    }
    
    private func isCurrentToken(_ token: SQLToken) -> Bool {
        guard position < tokens.count else { return false }
        return tokens[position] == token
    }
    
    private mutating func consume(_ expected: SQLToken) throws {
        let current = try currentToken()
        guard current == expected else {
            throw SQLParseError.expectedToken(tokenDescription(expected), actual: tokenDescription(current))
        }
        position += 1
    }
    
    private mutating func consumeCurrentToken() throws {
        guard position < tokens.count else {
            throw SQLParseError.endOfInput
        }
        position += 1
    }
    
    private mutating func parseIdentifier() throws -> String {
        let token = try currentToken()
        guard case .identifier(let name) = token else {
            throw SQLParseError.expectedToken("identifier", actual: tokenDescription(token))
        }
        try consumeCurrentToken()
        return name
    }
    
    private mutating func parseIntegerLiteral() throws -> Int64 {
        let token = try currentToken()
        guard case .literal(.integer(let value)) = token else {
            throw SQLParseError.expectedToken("integer", actual: tokenDescription(token))
        }
        try consumeCurrentToken()
        return value
    }
    
    private func tokenDescription(_ token: SQLToken) -> String {
        switch token {
        case .keyword(let kw): return kw
        case .identifier(let id): return id
        case .literal(let lit): return "literal(\(lit))"
        case .operator_(let op): return op
        case .punctuation(let punct): return punct
        case .eof: return "EOF"
        }
    }
}
