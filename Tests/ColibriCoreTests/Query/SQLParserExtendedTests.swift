import Foundation
@_spi(Experimental) import Testing
@testable import ColibriCore

@Suite("SQL Parser Extended Tests")
struct SQLParserExtendedTests {
    
    @Test("Parse simple SELECT")
    func testParseSimpleSelect() throws {
        let stmt = try SQLParser.parse("SELECT * FROM users")
        if case .select = stmt { } else { #expect(Bool(false)) }
    }
    
    @Test("Parse SELECT with WHERE")
    func testParseSelectWithWhere() throws {
        let stmt = try SQLParser.parse("SELECT id, name FROM users WHERE age > 18")
        if case .select = stmt { } else { #expect(Bool(false)) }
    }
    
    @Test("Parse INSERT statement")
    func testParseInsert() throws {
        let stmt = try SQLParser.parse("INSERT INTO users (id, name) VALUES (1, 'Alice')")
        if case .insert = stmt { } else { #expect(Bool(false)) }
    }
    
    @Test("Parse UPDATE statement")
    func testParseUpdate() throws {
        let stmt = try SQLParser.parse("UPDATE users SET name = 'Bob' WHERE id = 1")
        if case .update = stmt { } else { #expect(Bool(false)) }
    }
    
    @Test("Parse DELETE statement")
    func testParseDelete() throws {
        let stmt = try SQLParser.parse("DELETE FROM users WHERE id = 1")
        if case .delete = stmt { } else { #expect(Bool(false)) }
    }
    
    @Test("Parse CREATE TABLE")
    func testParseCreateTable() throws {
        let stmt = try SQLParser.parse("CREATE TABLE users (id INT, name TEXT)")
        if case .createTable = stmt { } else { #expect(Bool(false)) }
    }
    
    @Test("Parse DROP TABLE")
    func testParseDropTable() throws {
        let stmt = try SQLParser.parse("DROP TABLE users")
        if case .dropTable = stmt { } else { #expect(Bool(false)) }
    }
    
    @Test("Parse with semicolon")
    func testParseWithSemicolon() throws {
        let stmt = try SQLParser.parse("SELECT * FROM users;")
        if case .select = stmt { } else { #expect(Bool(false)) }
    }
    
    @Test("Parse case insensitive keywords")
    func testParseCaseInsensitive() throws {
        let stmt = try SQLParser.parse("select * from users where id = 1")
        if case .select = stmt { } else { #expect(Bool(false)) }
    }
    
    @Test("Reject empty query")
    func testRejectEmpty() {
        #expect(throws: Error.self) {
            _ = try SQLParser.parse("")
        }
    }
    
    @Test("Reject invalid syntax")
    func testRejectInvalid() {
        #expect(throws: Error.self) {
            _ = try SQLParser.parse("INVALID SQL QUERY")
        }
    }
}
