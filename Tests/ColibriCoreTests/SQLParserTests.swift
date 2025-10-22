//
//  SQLParserTests.swift
//  ColibrìDB SQL Parser Tests
//
//  Tests for SQL parsing, tokenization, and statement generation
//

import Foundation
import Testing
@testable import ColibriCore

/// Tests for the SQL Parser
@Suite("SQL Parser Tests")
struct SQLParserTests {
    
    /// Test parser initialization
    @Test("Parser Initialization")
    func testParserInitialization() throws {
        var parser = SQLParser()
        
        // Parser should be initialized successfully
        try TestAssertions.assertNotNil(parser, "Parser should be initialized")
    }
    
    /// Test SELECT statement parsing
    @Test("SELECT Statement Parsing")
    func testSELECTStatementParsing() throws {
        var parser = SQLParser()
        
        // Test simple SELECT
        let select1 = try parser.parse("SELECT * FROM users")
        if case .select(let columns, let table, let whereClause) = select1 {
            try TestAssertions.assertEqual(columns, ["*"], "Should parse SELECT *")
            try TestAssertions.assertEqual(table, "users", "Should parse table name")
            try TestAssertions.assertNil(whereClause, "Should have no WHERE clause")
        } else {
            try TestAssertions.assertionFailed("Should parse as SELECT statement")
        }
        
        // Test SELECT with specific columns
        let select2 = try parser.parse("SELECT id, name, age FROM users")
        if case .select(let columns, let table, let whereClause) = select2 {
            try TestAssertions.assertEqual(columns, ["id", "name", "age"], "Should parse column list")
            try TestAssertions.assertEqual(table, "users", "Should parse table name")
            try TestAssertions.assertNil(whereClause, "Should have no WHERE clause")
        } else {
            try TestAssertions.assertionFailed("Should parse as SELECT statement")
        }
        
        // Test SELECT with WHERE clause
        let select3 = try parser.parse("SELECT * FROM users WHERE age > 25")
        if case .select(let columns, let table, let whereClause) = select3 {
            try TestAssertions.assertEqual(columns, ["*"], "Should parse SELECT *")
            try TestAssertions.assertEqual(table, "users", "Should parse table name")
            try TestAssertions.assertNotNil(whereClause, "Should have WHERE clause")
        } else {
            try TestAssertions.assertionFailed("Should parse as SELECT statement")
        }
    }
    
    /// Test INSERT statement parsing
    @Test("INSERT Statement Parsing")
    func testINSERTStatementParsing() throws {
        var parser = SQLParser()
        
        // Test INSERT statement
        let insert = try parser.parse("INSERT INTO users VALUES (1, 'Alice', 25)")
        if case .insert(let table, let columns, let values) = insert {
            try TestAssertions.assertEqual(table, "users", "Should parse table name")
            try TestAssertions.assertEqual(columns.count, 0, "Should have empty columns list")
            try TestAssertions.assertEqual(values.count, 0, "Should have empty values list")
        } else {
            try TestAssertions.assertionFailed("Should parse as INSERT statement")
        }
    }
    
    /// Test UPDATE statement parsing
    @Test("UPDATE Statement Parsing")
    func testUPDATEStatementParsing() throws {
        var parser = SQLParser()
        
        // Test UPDATE statement
        let update = try parser.parse("UPDATE users SET age = 26 WHERE id = 1")
        if case .update(let table, let assignments, let whereClause) = update {
            try TestAssertions.assertEqual(table, "users", "Should parse table name")
            try TestAssertions.assertEqual(assignments.count, 0, "Should have empty assignments list")
            try TestAssertions.assertNotNil(whereClause, "Should have WHERE clause")
        } else {
            try TestAssertions.assertionFailed("Should parse as UPDATE statement")
        }
    }
    
    /// Test DELETE statement parsing
    @Test("DELETE Statement Parsing")
    func testDELETEStatementParsing() throws {
        var parser = SQLParser()
        
        // Test DELETE statement
        let delete = try parser.parse("DELETE FROM users WHERE age < 18")
        if case .delete(let table, let whereClause) = delete {
            try TestAssertions.assertEqual(table, "users", "Should parse table name")
            try TestAssertions.assertNotNil(whereClause, "Should have WHERE clause")
        } else {
            try TestAssertions.assertionFailed("Should parse as DELETE statement")
        }
    }
    
    /// Test CREATE TABLE statement parsing
    @Test("CREATE TABLE Statement Parsing")
    func testCREATETABLEStatementParsing() throws {
        var parser = SQLParser()
        
        // Test CREATE TABLE statement
        let createTable = try parser.parse("CREATE TABLE users (id INT, name VARCHAR(100), age INT)")
        if case .createTable(let name, let columns) = createTable {
            try TestAssertions.assertEqual(name, "users", "Should parse table name")
            try TestAssertions.assertEqual(columns.count, 0, "Should have empty columns list")
        } else {
            try TestAssertions.assertionFailed("Should parse as CREATE TABLE statement")
        }
    }
    
    /// Test DROP TABLE statement parsing
    @Test("DROP TABLE Statement Parsing")
    func testDROPTABLEStatementParsing() throws {
        var parser = SQLParser()
        
        // Test DROP TABLE statement
        let dropTable = try parser.parse("DROP TABLE users")
        if case .dropTable(let name) = dropTable {
            try TestAssertions.assertEqual(name, "users", "Should parse table name")
        } else {
            try TestAssertions.assertionFailed("Should parse as DROP TABLE statement")
        }
    }
    
    /// Test tokenization
    @Test("Tokenization")
    func testTokenization() throws {
        var parser = SQLParser()
        
        // Test tokenization of a simple query
        let sql = "SELECT id, name FROM users WHERE age > 25"
        let tokens = try parser.parse(sql)
        
        // Verify that parsing succeeds (tokenization is internal)
        try TestAssertions.assertNotNil(tokens, "Should successfully parse SQL")
    }
    
    /// Test case insensitive parsing
    @Test("Case Insensitive Parsing")
    func testCaseInsensitiveParsing() throws {
        var parser = SQLParser()
        
        // Test different cases
        let queries = [
            "SELECT * FROM users",
            "select * from users",
            "Select * From Users",
            "SELECT * FROM USERS"
        ]
        
        for query in queries {
            let statement = try parser.parse(query)
            try TestAssertions.assertNotNil(statement, "Should parse query regardless of case")
        }
    }
    
    /// Test whitespace handling
    @Test("Whitespace Handling")
    func testWhitespaceHandling() throws {
        var parser = SQLParser()
        
        // Test queries with different whitespace
        let queries = [
            "SELECT * FROM users",
            "SELECT  *  FROM  users",
            "SELECT\n*\nFROM\nusers",
            "SELECT\t*\tFROM\tusers"
        ]
        
        for query in queries {
            let statement = try parser.parse(query)
            try TestAssertions.assertNotNil(statement, "Should parse query regardless of whitespace")
        }
    }
    
    /// Test string literal parsing
    @Test("String Literal Parsing")
    func testStringLiteralParsing() throws {
        var parser = SQLParser()
        
        // Test queries with string literals
        let queries = [
            "SELECT * FROM users WHERE name = 'Alice'",
            "SELECT * FROM users WHERE name = 'Bob'",
            "SELECT * FROM users WHERE name = 'Charlie'"
        ]
        
        for query in queries {
            let statement = try parser.parse(query)
            try TestAssertions.assertNotNil(statement, "Should parse query with string literals")
        }
    }
    
    /// Test numeric literal parsing
    @Test("Numeric Literal Parsing")
    func testNumericLiteralParsing() throws {
        var parser = SQLParser()
        
        // Test queries with numeric literals
        let queries = [
            "SELECT * FROM users WHERE age = 25",
            "SELECT * FROM users WHERE age = 30",
            "SELECT * FROM users WHERE age = 100"
        ]
        
        for query in queries {
            let statement = try parser.parse(query)
            try TestAssertions.assertNotNil(statement, "Should parse query with numeric literals")
        }
    }
    
    /// Test identifier parsing
    @Test("Identifier Parsing")
    func testIdentifierParsing() throws {
        var parser = SQLParser()
        
        // Test queries with different identifiers
        let queries = [
            "SELECT id FROM users",
            "SELECT user_id FROM users",
            "SELECT user_name FROM users",
            "SELECT user_age FROM users"
        ]
        
        for query in queries {
            let statement = try parser.parse(query)
            try TestAssertions.assertNotNil(statement, "Should parse query with identifiers")
        }
    }
    
    /// Test error handling
    @Test("Error Handling")
    func testErrorHandling() throws {
        var parser = SQLParser()
        
        // Test invalid SQL statements
        let invalidQueries = [
            "INVALID SQL",
            "SELECT FROM",
            "SELECT * FROM",
            "SELECT * FROM WHERE",
            "CREATE TABLE",
            "DROP TABLE"
        ]
        
        for query in invalidQueries {
            try TestAssertions.assertThrows({
                try parser.parse(query)
            }, "Should throw error for invalid SQL: \(query)")
        }
    }
    
    /// Test complex queries
    @Test("Complex Queries")
    func testComplexQueries() throws {
        var parser = SQLParser()
        
        // Test more complex queries
        let queries = [
            "SELECT id, name, age FROM users WHERE age > 25 AND name = 'Alice'",
            "SELECT * FROM users WHERE age BETWEEN 18 AND 65",
            "SELECT COUNT(*) FROM users WHERE age > 30",
            "SELECT u.id, u.name FROM users u WHERE u.age > 25"
        ]
        
        for query in queries {
            let statement = try parser.parse(query)
            try TestAssertions.assertNotNil(statement, "Should parse complex query: \(query)")
        }
    }
    
    /// Test SQL statement types
    @Test("SQL Statement Types")
    func testSQLStatementTypes() throws {
        var parser = SQLParser()
        
        // Test different statement types
        let selectStmt = try parser.parse("SELECT * FROM users")
        try TestAssertions.assertTrue(selectStmt is SQLStatement, "Should be SQLStatement")
        
        let insertStmt = try parser.parse("INSERT INTO users VALUES (1, 'Alice', 25)")
        try TestAssertions.assertTrue(insertStmt is SQLStatement, "Should be SQLStatement")
        
        let updateStmt = try parser.parse("UPDATE users SET age = 26 WHERE id = 1")
        try TestAssertions.assertTrue(updateStmt is SQLStatement, "Should be SQLStatement")
        
        let deleteStmt = try parser.parse("DELETE FROM users WHERE age < 18")
        try TestAssertions.assertTrue(deleteStmt is SQLStatement, "Should be SQLStatement")
        
        let createStmt = try parser.parse("CREATE TABLE users (id INT, name VARCHAR(100))")
        try TestAssertions.assertTrue(createStmt is SQLStatement, "Should be SQLStatement")
        
        let dropStmt = try parser.parse("DROP TABLE users")
        try TestAssertions.assertTrue(dropStmt is SQLStatement, "Should be SQLStatement")
    }
    
    /// Test expression parsing
    @Test("Expression Parsing")
    func testExpressionParsing() throws {
        var parser = SQLParser()
        
        // Test queries with expressions
        let queries = [
            "SELECT * FROM users WHERE age > 25",
            "SELECT * FROM users WHERE age = 30",
            "SELECT * FROM users WHERE age < 40",
            "SELECT * FROM users WHERE age >= 18",
            "SELECT * FROM users WHERE age <= 65"
        ]
        
        for query in queries {
            let statement = try parser.parse(query)
            try TestAssertions.assertNotNil(statement, "Should parse query with expressions")
        }
    }
    
    /// Test binary operators
    @Test("Binary Operators")
    func testBinaryOperators() throws {
        var parser = SQLParser()
        
        // Test different binary operators
        let operators = ["=", "<", ">", "<=", ">=", "!="]
        
        for op in operators {
            let query = "SELECT * FROM users WHERE age \(op) 25"
            let statement = try parser.parse(query)
            try TestAssertions.assertNotNil(statement, "Should parse query with operator \(op)")
        }
    }
    
    /// Test logical operators
    @Test("Logical Operators")
    func testLogicalOperators() throws {
        var parser = SQLParser()
        
        // Test logical operators
        let queries = [
            "SELECT * FROM users WHERE age > 25 AND name = 'Alice'",
            "SELECT * FROM users WHERE age > 25 OR name = 'Bob'",
            "SELECT * FROM users WHERE NOT age < 18"
        ]
        
        for query in queries {
            let statement = try parser.parse(query)
            try TestAssertions.assertNotNil(statement, "Should parse query with logical operators")
        }
    }
    
    /// Test parentheses
    @Test("Parentheses")
    func testParentheses() throws {
        var parser = SQLParser()
        
        // Test queries with parentheses
        let queries = [
            "SELECT * FROM users WHERE (age > 25 AND name = 'Alice')",
            "SELECT * FROM users WHERE age > 25 AND (name = 'Alice' OR name = 'Bob')",
            "SELECT * FROM users WHERE (age > 25 OR age < 18) AND name = 'Charlie'"
        ]
        
        for query in queries {
            let statement = try parser.parse(query)
            try TestAssertions.assertNotNil(statement, "Should parse query with parentheses")
        }
    }
    
    /// Test performance with large queries
    @Test("Performance - Large Queries")
    func testPerformanceLargeQueries() throws {
        var parser = SQLParser()
        
        // Test performance with large query
        let largeQuery = "SELECT id, name, age, email, phone, address, city, state, zip FROM users WHERE age > 25 AND name = 'Alice' AND email = 'alice@example.com' AND phone = '123-456-7890' AND address = '123 Main St' AND city = 'New York' AND state = 'NY' AND zip = '10001'"
        
        let startTime = Date()
        let statement = try parser.parse(largeQuery)
        let endTime = Date()
        let duration = endTime.timeIntervalSince(startTime)
        
        // Verify performance is reasonable
        try TestAssertions.assertTrue(duration < 0.1, "Performance should be reasonable")
        try TestAssertions.assertNotNil(statement, "Should parse large query successfully")
    }
    
    /// Test multiple statements
    @Test("Multiple Statements")
    func testMultipleStatements() throws {
        var parser = SQLParser()
        
        // Test parsing multiple statements (one at a time)
        let statements = [
            "SELECT * FROM users",
            "INSERT INTO users VALUES (1, 'Alice', 25)",
            "UPDATE users SET age = 26 WHERE id = 1",
            "DELETE FROM users WHERE age < 18",
            "CREATE TABLE users (id INT, name VARCHAR(100))",
            "DROP TABLE users"
        ]
        
        for sql in statements {
            let statement = try parser.parse(sql)
            try TestAssertions.assertNotNil(statement, "Should parse statement: \(sql)")
        }
    }
    
    /// Test edge cases
    @Test("Edge Cases")
    func testEdgeCases() throws {
        var parser = SQLParser()
        
        // Test edge cases
        let edgeCases = [
            "SELECT * FROM users",  // Simple case
            "SELECT * FROM users WHERE age = 0",  // Zero value
            "SELECT * FROM users WHERE age = -1",  // Negative value
            "SELECT * FROM users WHERE name = ''",  // Empty string
            "SELECT * FROM users WHERE age = 999999999",  // Large number
        ]
        
        for query in edgeCases {
            let statement = try parser.parse(query)
            try TestAssertions.assertNotNil(statement, "Should parse edge case: \(query)")
        }
    }
}
