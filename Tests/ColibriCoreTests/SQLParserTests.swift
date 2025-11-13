//
//  SQLParserTests.swift
//  ColibrìDB SQL Parser Tests
//
//  Tests for SQL parsing, tokenization, and statement generation
//

import Foundation
import XCTest
@testable import ColibriCore

/// Tests for the SQL Parser
final class SQLParserTests {
    
    /// Test parser initialization
    func testParserInitialization() throws {
        var parser = SQLParser()
        
        // Parser should be initialized successfully
        XCTAssertNotNil(parser, "Parser should be initialized")
    }
    
    /// Test SELECT statement parsing
    func testSELECTStatementParsing() throws {
        var parser = SQLParser()
        
        // Test simple SELECT
        var parser1 = SQLParser()
        let select1 = try parser1.parse("SELECT * FROM users")
        XCTAssertEqual(select1.kind, StmtKind.select.rawValue, "Should parse as SELECT statement")
        
        // Test SELECT with specific columns
        var parser2 = SQLParser()
        let select2 = try parser2.parse("SELECT id, name, age FROM users")
        XCTAssertEqual(select2.kind, StmtKind.select.rawValue, "Should parse as SELECT statement")
        
        // Test SELECT with WHERE clause
        var parser3 = SQLParser()
        let select3 = try parser3.parse("SELECT * FROM users WHERE age > 25")
        XCTAssertEqual(select3.kind, StmtKind.select.rawValue, "Should parse as SELECT statement")
    }
    
    /// Test INSERT statement parsing
    func testINSERTStatementParsing() throws {
        var parser = SQLParser()
        
        // Test INSERT statement
        var parser1 = SQLParser()
        let insert = try parser1.parse("INSERT INTO users VALUES (1, 'Alice', 25)")
        XCTAssertEqual(insert.kind, StmtKind.insert.rawValue, "Should parse as INSERT statement")
        XCTAssertEqual(insert.attributes["table"], "users", "Should parse table name")
    }
    
    /// Test UPDATE statement parsing
    func testUPDATEStatementParsing() throws {
        var parser = SQLParser()
        
        // Test UPDATE statement
        var parser1 = SQLParser()
        let update = try parser1.parse("UPDATE users SET age = 26 WHERE id = 1")
        XCTAssertEqual(update.kind, StmtKind.update.rawValue, "Should parse as UPDATE statement")
        XCTAssertEqual(update.attributes["table"], "users", "Should parse table name")
    }
    
    /// Test DELETE statement parsing
    func testDELETEStatementParsing() throws {
        var parser = SQLParser()
        
        // Test DELETE statement
        var parser1 = SQLParser()
        let delete = try parser1.parse("DELETE FROM users WHERE age < 18")
        XCTAssertEqual(delete.kind, StmtKind.delete.rawValue, "Should parse as DELETE statement")
        XCTAssertEqual(delete.attributes["table"], "users", "Should parse table name")
    }
    
    /// Test CREATE TABLE statement parsing
    func testCREATETABLEStatementParsing() throws {
        var parser = SQLParser()
        
        // Test CREATE TABLE statement
        var parser1 = SQLParser()
        let createTable = try parser1.parse("CREATE TABLE users (id INT, name VARCHAR(100), age INT)")
        XCTAssertEqual(createTable.kind, StmtKind.createTable.rawValue, "Should parse as CREATE TABLE statement")
        XCTAssertEqual(createTable.attributes["table"], "users", "Should parse table name")
    }
    
    /// Test DROP TABLE statement parsing
    func testDROPTABLEStatementParsing() throws {
        var parser = SQLParser()
        
        // Test DROP TABLE statement
        var parser1 = SQLParser()
        let dropTable = try parser1.parse("DROP TABLE users")
        XCTAssertEqual(dropTable.kind, StmtKind.dropTable.rawValue, "Should parse as DROP TABLE statement")
        XCTAssertEqual(dropTable.attributes["table"], "users", "Should parse table name")
    }
    
    /// Test tokenization
    func testTokenization() throws {
        var parser = SQLParser()
        
        // Test tokenization of a simple query
        let sql = "SELECT id, name FROM users WHERE age > 25"
        var parser1 = SQLParser()
        let ast = try parser1.parse(sql)
        
        // Verify that parsing succeeds (tokenization is internal)
        XCTAssertEqual(ast.kind, StmtKind.select.rawValue, "Should successfully parse SQL")
    }
    
    /// Test case insensitive parsing
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
            var parser1 = SQLParser()
            let statement = try parser1.parse(query)
            XCTAssertEqual(statement.kind, StmtKind.select.rawValue, "Should parse query regardless of case")
        }
    }
    
    /// Test whitespace handling
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
            var parser1 = SQLParser()
            let statement = try parser1.parse(query)
            XCTAssertEqual(statement.kind, StmtKind.select.rawValue, "Should parse query regardless of whitespace")
        }
    }
    
    /// Test string literal parsing
    func testStringLiteralParsing() throws {
        var parser = SQLParser()
        
        // Test queries with string literals
        let queries = [
            "SELECT * FROM users WHERE name = 'Alice'",
            "SELECT * FROM users WHERE name = 'Bob'",
            "SELECT * FROM users WHERE name = 'Charlie'"
        ]
        
        for query in queries {
            var parser1 = SQLParser()
            let statement = try parser1.parse(query)
            XCTAssertEqual(statement.kind, StmtKind.select.rawValue, "Should parse query with string literals")
        }
    }
    
    /// Test numeric literal parsing
    func testNumericLiteralParsing() throws {
        var parser = SQLParser()
        
        // Test queries with numeric literals
        let queries = [
            "SELECT * FROM users WHERE age = 25",
            "SELECT * FROM users WHERE age = 30",
            "SELECT * FROM users WHERE age = 100"
        ]
        
        for query in queries {
            var parser1 = SQLParser()
            let statement = try parser1.parse(query)
            XCTAssertEqual(statement.kind, StmtKind.select.rawValue, "Should parse query with numeric literals")
        }
    }
    
    /// Test identifier parsing
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
            var parser1 = SQLParser()
            let statement = try parser1.parse(query)
            XCTAssertEqual(statement.kind, StmtKind.select.rawValue, "Should parse query with identifiers")
        }
    }
    
    /// Test error handling
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
            var parser1 = SQLParser()
            do {
                _ = try parser1.parse(query)
                XCTFail("Should throw error for invalid SQL: \(query)")
            } catch {
                // Expected
            }
        }
    }
    
    /// Test complex queries
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
            var parser1 = SQLParser()
            let statement = try parser1.parse(query)
            XCTAssertEqual(statement.kind, StmtKind.select.rawValue, "Should parse complex query: \(query)")
        }
    }
    
    /// Test SQL statement types
    func testSQLStatementTypes() throws {
        var parser = SQLParser()
        
        // Test different statement types
        var parser1 = SQLParser()
        let selectStmt = try parser1.parse("SELECT * FROM users")
        XCTAssertEqual(selectStmt.kind, StmtKind.select.rawValue, "Should be SELECT statement")
        
        var parser2 = SQLParser()
        let insertStmt = try parser2.parse("INSERT INTO users VALUES (1, 'Alice', 25)")
        XCTAssertEqual(insertStmt.kind, StmtKind.insert.rawValue, "Should be INSERT statement")
        
        var parser3 = SQLParser()
        let updateStmt = try parser3.parse("UPDATE users SET age = 26 WHERE id = 1")
        XCTAssertEqual(updateStmt.kind, StmtKind.update.rawValue, "Should be UPDATE statement")
        
        var parser4 = SQLParser()
        let deleteStmt = try parser4.parse("DELETE FROM users WHERE age < 18")
        XCTAssertEqual(deleteStmt.kind, StmtKind.delete.rawValue, "Should be DELETE statement")
        
        var parser5 = SQLParser()
        let createStmt = try parser5.parse("CREATE TABLE users (id INT, name VARCHAR(100))")
        XCTAssertEqual(createStmt.kind, StmtKind.createTable.rawValue, "Should be CREATE TABLE statement")
        
        var parser6 = SQLParser()
        let dropStmt = try parser6.parse("DROP TABLE users")
        XCTAssertEqual(dropStmt.kind, StmtKind.dropTable.rawValue, "Should be DROP TABLE statement")
    }
    
    /// Test expression parsing
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
            var parser1 = SQLParser()
            let statement = try parser1.parse(query)
            XCTAssertEqual(statement.kind, StmtKind.select.rawValue, "Should parse query with expressions")
        }
    }
    
    /// Test binary operators
    func testBinaryOperators() throws {
        var parser = SQLParser()
        
        // Test different binary operators
        let operators = ["=", "<", ">", "<=", ">=", "!="]
        
        for op in operators {
            let query = "SELECT * FROM users WHERE age \(op) 25"
            var parser1 = SQLParser()
            let statement = try parser1.parse(query)
            XCTAssertEqual(statement.kind, StmtKind.select.rawValue, "Should parse query with operator \(op)")
        }
    }
    
    /// Test logical operators
    func testLogicalOperators() throws {
        var parser = SQLParser()
        
        // Test logical operators
        let queries = [
            "SELECT * FROM users WHERE age > 25 AND name = 'Alice'",
            "SELECT * FROM users WHERE age > 25 OR name = 'Bob'",
            "SELECT * FROM users WHERE NOT age < 18"
        ]
        
        for query in queries {
            var parser1 = SQLParser()
            let statement = try parser1.parse(query)
            XCTAssertEqual(statement.kind, StmtKind.select.rawValue, "Should parse query with logical operators")
        }
    }
    
    /// Test parentheses
    func testParentheses() throws {
        var parser = SQLParser()
        
        // Test queries with parentheses
        let queries = [
            "SELECT * FROM users WHERE (age > 25 AND name = 'Alice')",
            "SELECT * FROM users WHERE age > 25 AND (name = 'Alice' OR name = 'Bob')",
            "SELECT * FROM users WHERE (age > 25 OR age < 18) AND name = 'Charlie'"
        ]
        
        for query in queries {
            var parser1 = SQLParser()
            let statement = try parser1.parse(query)
            XCTAssertEqual(statement.kind, StmtKind.select.rawValue, "Should parse query with parentheses")
        }
    }
    
    /// Test performance with large queries
    func testPerformanceLargeQueries() throws {
        var parser = SQLParser()
        
        // Test performance with large query
        let largeQuery = "SELECT id, name, age, email, phone, address, city, state, zip FROM users WHERE age > 25 AND name = 'Alice' AND email = 'alice@example.com' AND phone = '123-456-7890' AND address = '123 Main St' AND city = 'New York' AND state = 'NY' AND zip = '10001'"
        
        var parser1 = SQLParser()
        let startTime = Date()
        let statement = try parser1.parse(largeQuery)
        let endTime = Date()
        let duration = endTime.timeIntervalSince(startTime)
        
        // Verify performance is reasonable
        XCTAssertTrue(duration < 0.1, "Performance should be reasonable")
        XCTAssertEqual(statement.kind, StmtKind.select.rawValue, "Should parse large query successfully")
    }
    
    /// Test multiple statements
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
            var parser1 = SQLParser()
            let statement = try parser1.parse(sql)
            XCTAssertNotNil(statement, "Should parse statement: \(sql)")
        }
    }
    
    /// Test edge cases
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
            var parser1 = SQLParser()
            let statement = try parser1.parse(query)
            XCTAssertEqual(statement.kind, StmtKind.select.rawValue, "Should parse edge case: \(query)")
        }
    }
}

