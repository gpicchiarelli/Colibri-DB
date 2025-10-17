//
//  PreparedStatementIntegrationTests.swift
//  ColibrDB Tests
//
//  End-to-end tests for prepared statement integration
//

import Foundation
@_spi(Experimental) import Testing
@testable import ColibriCore

@Suite("Prepared Statement Integration Tests", .serialized)
struct PreparedStatementIntegrationTests {
    
    func createTestDatabase() throws -> Database {
        let tempDir = FileManager.default.temporaryDirectory
            .appendingPathComponent(UUID().uuidString)
        var config = DBConfig()
        config.dataDir = tempDir.path
        config.walEnabled = false
        
        let db = try Database(config: config)
        try db.createTable("users")
        
        // Setup test data
        let tid = try db.begin()
        for i in 1...10 {
            let row: Row = [
                "id": .int(Int64(i)),
                "name": .string("User\(i)"),
                "age": .int(Int64(20 + i)),
                "email": .string("user\(i)@test.com")
            ]
            _ = try db.insert(into: "users", row: row, tid: tid)
        }
        try db.commit(tid)
        
        return db
    }
    
    @Test("E2E: Prepare and execute SELECT with positional parameter")
    func testE2ESelectPositional() throws {
        let db = try createTestDatabase()
        defer { try? db.close() }
        
        // This tests the full stack: Lexer → Parser → Prepared Statement → Execution
        var stmt = try db.prepare("SELECT * FROM users WHERE id = $1")
        try stmt.bind(parameters: ["$1": .int(5)])
        let results = try stmt.execute()
        
        #expect(results.count == 1)
        #expect(results[0]["name"] == .string("User5"))
    }
    
    @Test("E2E: Multiple parameters in WHERE clause")
    func testE2EMultipleParameters() throws {
        let db = try createTestDatabase()
        defer { try? db.close() }
        
        var stmt = try db.prepare("SELECT * FROM users WHERE id = $1 AND name = $2")
        try stmt.bind(parameters: [
            "$1": .int(3),
            "$2": .string("User3")
        ])
        let results = try stmt.execute()
        
        #expect(results.count == 1)
        #expect(results[0]["id"] == .int(3))
    }
    
    @Test("E2E: Statement reuse with different parameters")
    func testE2EStatementReuse() throws {
        let db = try createTestDatabase()
        defer { try? db.close() }
        
        var stmt = try db.prepare("SELECT * FROM users WHERE id = $1")
        
        // Execute with id=1
        try stmt.bind(parameters: ["$1": .int(1)])
        let results1 = try stmt.execute()
        #expect(results1.count == 1)
        #expect(results1[0]["name"] == .string("User1"))
        
        // Reset and execute with id=2
        stmt.reset()
        try stmt.bind(parameters: ["$1": .int(2)])
        let results2 = try stmt.execute()
        #expect(results2.count == 1)
        #expect(results2[0]["name"] == .string("User2"))
    }
    
    @Test("E2E: Prevent SQL injection with malicious input")
    func testE2EInjectionPrevention() throws {
        let db = try createTestDatabase()
        defer { try? db.close() }
        
        // Classic SQL injection attempt
        let malicious = "' OR '1'='1"
        
        var stmt = try db.prepare("SELECT * FROM users WHERE name = $1")
        try stmt.bind(parameters: ["$1": .string(malicious)])
        let results = try stmt.execute()
        
        // Should find NO results (malicious string treated as literal)
        #expect(results.isEmpty)
        
        // Verify database integrity
        let allUsers = try db.scan( "users")
        #expect(allUsers.count == 10)  // All data intact
    }
    
    @Test("E2E: Convenience execute() method")
    func testE2EConvenienceMethod() throws {
        let db = try createTestDatabase()
        defer { try? db.close() }
        
        // One-line execution
        let results = try db.execute(
            "SELECT * FROM users WHERE age = $1",
            parameters: ["$1": .int(25)]
        )
        
        #expect(results.count == 1)
        #expect(results[0]["name"] == .string("User5"))
    }
    
    @Test("E2E: Special characters in parameters handled safely")
    func testE2ESpecialCharacters() throws {
        let db = try createTestDatabase()
        defer { try? db.close() }
        
        // Insert user with special characters
        let tid = try db.begin()
        _ = try db.insert(
            table: "users",
            row: [
                "id": .int(99),
                "name": .string("O'Brien"),
                "age": .int(45),
                "email": .string("o'brien@test.com")
            ],
            tid: tid
        )
        try db.commit(tid)
        
        // Search with apostrophe in parameter
        let results = try db.execute(
            "SELECT * FROM users WHERE name = $1",
            parameters: ["$1": .string("O'Brien")]
        )
        
        #expect(results.count == 1)
        #expect(results[0]["email"] == .string("o'brien@test.com"))
    }
    
    @Test("E2E: NULL parameter handling")
    func testE2ENullParameter() throws {
        let db = try createTestDatabase()
        defer { try? db.close() }
        
        var stmt = try db.prepare("SELECT * FROM users WHERE name = $1")
        try stmt.bind(parameters: ["$1": .null])
        let results = try stmt.execute()
        
        // NULL doesn't match any name
        #expect(results.isEmpty)
    }
    
    @Test("E2E: Numeric parameter types")
    func testE2ENumericParameters() throws {
        let db = try createTestDatabase()
        defer { try? db.close() }
        
        // Integer parameter
        let intResults = try db.execute(
            "SELECT * FROM users WHERE id = $1",
            parameters: ["$1": .int(7)]
        )
        #expect(intResults.count == 1)
        
        // Double parameter (for age comparison)
        let doubleResults = try db.execute(
            "SELECT * FROM users WHERE age = $1",
            parameters: ["$1": .double(25.0)]
        )
        #expect(doubleResults.count >= 1)
    }
    
    @Test("E2E: Date parameter handling")
    func testE2EDateParameter() throws {
        let db = try createTestDatabase()
        defer { try? db.close() }
        
        let now = Date()
        
        let tid = try db.begin()
        _ = try db.insert(
            table: "users",
            row: [
                "id": .int(100),
                "name": .string("DateTest"),
                "age": .int(30),
                "created_at": .date(now)
            ],
            tid: tid
        )
        try db.commit(tid)
        
        // Query with date parameter
        let results = try db.execute(
            "SELECT * FROM users WHERE created_at = $1",
            parameters: ["$1": .date(now)]
        )
        
        #expect(results.count == 1)
    }
    
    @Test("E2E: Large dataset with prepared statements")
    func testE2ELargeDataset() throws {
        let db = try createTestDatabase()
        defer { try? db.close() }
        
        var stmt = try db.prepare("SELECT * FROM users WHERE id = $1")
        
        // Query all 10 users via prepared statement
        for i in 1...10 {
            try stmt.bind(parameters: ["$1": .int(Int64(i))])
            let results = try stmt.execute()
            
            #expect(results.count == 1)
            #expect(results[0]["id"] == .int(Int64(i)))
            
            stmt.reset()
        }
    }
}

