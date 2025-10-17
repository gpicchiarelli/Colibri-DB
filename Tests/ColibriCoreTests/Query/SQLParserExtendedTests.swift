//
//  SQLParserExtendedTests.swift
//  ColibrDB Tests
//
//  Extended SQL parser tests
//

import Foundation
@_spi(Experimental) import Testing
@testable import ColibriCore

@Suite("SQL Parser Extended Tests")
struct SQLParserExtendedTests {
    
    @Test("Parse simple SELECT")
    func testParseSimpleSelect() throws {
        let parser = SQLParser()
        let stmt = try parser.parse("SELECT * FROM users")
        
        // Basic validation - statement parsed without errors
        #expect(stmt.type == .select)
    }
    
    @Test("Parse SELECT with WHERE")
    func testParseSelectWithWhere() throws {
        let parser = SQLParser()
        let stmt = try parser.parse("SELECT id, name FROM users WHERE age > 18")
        
        #expect(stmt.type == .select)
    }
    
    @Test("Parse INSERT statement")
    func testParseInsert() throws {
        let parser = SQLParser()
        let stmt = try parser.parse("INSERT INTO users (id, name) VALUES (1, 'Alice')")
        
        #expect(stmt.type == .insert)
    }
    
    @Test("Parse UPDATE statement")
    func testParseUpdate() throws {
        let parser = SQLParser()
        let stmt = try parser.parse("UPDATE users SET name = 'Bob' WHERE id = 1")
        
        #expect(stmt.type == .update)
    }
    
    @Test("Parse DELETE statement")
    func testParseDelete() throws {
        let parser = SQLParser()
        let stmt = try parser.parse("DELETE FROM users WHERE id = 1")
        
        #expect(stmt.type == .delete)
    }
    
    @Test("Parse CREATE TABLE")
    func testParseCreateTable() throws {
        let parser = SQLParser()
        let stmt = try parser.parse("CREATE TABLE users (id INT, name TEXT)")
        
        #expect(stmt.type == .createTable)
    }
    
    @Test("Parse DROP TABLE")
    func testParseDropTable() throws {
        let parser = SQLParser()
        let stmt = try parser.parse("DROP TABLE users")
        
        #expect(stmt.type == .dropTable)
    }
    
    @Test("Parse with semicolon")
    func testParseWithSemicolon() throws {
        let parser = SQLParser()
        let stmt = try parser.parse("SELECT * FROM users;")
        
        #expect(stmt.type == .select)
    }
    
    @Test("Parse case insensitive keywords")
    func testParseCaseInsensitive() throws {
        let parser = SQLParser()
        let stmt = try parser.parse("select * from users where id = 1")
        
        #expect(stmt.type == .select)
    }
    
    @Test("Reject empty query")
    func testRejectEmpty() {
        let parser = SQLParser()
        
        #expect(throws: Error.self) {
            _ = try parser.parse("")
        }
    }
    
    @Test("Reject invalid syntax")
    func testRejectInvalid() {
        let parser = SQLParser()
        
        #expect(throws: Error.self) {
            _ = try parser.parse("INVALID SQL QUERY")
        }
    }
}

