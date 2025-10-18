//
//  ErrorHandlingTests.swift
//  ColibrDB Tests
//
//  Tests for proper error handling and propagation
//

import Foundation
@_spi(Experimental) import Testing
@testable import ColibriCore

@Suite("Error Handling Tests")
struct ErrorHandlingTests {
    
    @Test("DBError types")
    func testErrorTypes() {
        let ioError = DBError.io("disk failure")
        #expect(ioError.description.contains("IO"))
        
        let configError = DBError.config("invalid setting")
        #expect(configError.description.contains("Config"))
        
        let argError = DBError.invalidArgument("bad value")
        #expect(argError.description.contains("InvalidArgument"))
        
        let notFoundError = DBError.notFound("missing item")
        #expect(notFoundError.description.contains("NotFound"))
        
        let conflictError = DBError.conflict("duplicate key")
        #expect(conflictError.description.contains("Conflict"))
        
        let deadlockError = DBError.deadlock("cycle detected")
        #expect(deadlockError.description.contains("Deadlock"))
        
        let timeoutError = DBError.lockTimeout("timeout exceeded")
        #expect(timeoutError.description.contains("LockTimeout"))
    }
    
    @Test("Error descriptions are informative")
    func testErrorDescriptions() {
        let error = DBError.io("Failed to write page 123")
        let desc = error.description
        
        #expect(desc.contains("IO"))
        #expect(desc.contains("Failed to write page 123"))
    }
    
    @Test("Database throws on invalid table name")
    func testInvalidTableError() throws {
        let tempDir = FileManager.default.temporaryDirectory
            .appendingPathComponent(UUID().uuidString)
        var config = DBConfig()
        config.dataDir = tempDir.path
        
        let db = try Database(config: config)
        defer { try? db.close() }
        
        #expect(throws: DBError.self) {
            _ = try db.scan( "nonexistent_table")
        }
    }
    
    @Test("Database throws on invalid RID")
    func testInvalidRIDError() throws {
        let tempDir = FileManager.default.temporaryDirectory
            .appendingPathComponent(UUID().uuidString)
        var config = DBConfig()
        config.dataDir = tempDir.path
        
        let db = try Database(config: config)
        defer { try? db.close() }
        
        try db.createTable("test")
        
        let invalidRID = RID(pageId: 9999, slotId: 9999)
        
        #expect(throws: Error.self) {
            _ = try db.readRow(table: "test", rid: invalidRID)
        }
    }
    
    @Test("Transaction rollback cleans up state")
    func testRollbackCleanup() throws {
        let tempDir = FileManager.default.temporaryDirectory
            .appendingPathComponent(UUID().uuidString)
        var config = DBConfig()
        config.dataDir = tempDir.path
        
        let db = try Database(config: config)
        defer { try? db.close() }
        
        try db.createTable("test")
        
        let tid = try db.begin()
        _ = try db.insert(into: "test", row: ["id": .int(1)], tid: tid)
        
        // Rollback
        try db.rollback(tid)
        
        // Verify nothing was inserted
        let results = try db.scan( "test")
        #expect(results.isEmpty)
    }
    
    @Test("Multiple error scenarios")
    func testMultipleErrors() throws {
        let tempDir = FileManager.default.temporaryDirectory
            .appendingPathComponent(UUID().uuidString)
        var config = DBConfig()
        config.dataDir = tempDir.path
        
        let db = try Database(config: config)
        defer { try? db.close() }
        
        // Error 1: Table doesn't exist
        #expect(throws: Error.self) {
            _ = try db.scan( "missing")
        }
        
        // Create table
        try db.createTable("test")
        
        // Error 2: Duplicate table
        #expect(throws: Error.self) {
            try db.createTable("test")
        }
        
        // Error 3: Invalid transaction
        #expect(throws: Error.self) {
            try db.commit(999999)
        }
    }
    
    @Test("Error recovery - database remains usable")
    func testErrorRecovery() throws {
        let tempDir = FileManager.default.temporaryDirectory
            .appendingPathComponent(UUID().uuidString)
        var config = DBConfig()
        config.dataDir = tempDir.path
        
        let db = try Database(config: config)
        defer { try? db.close() }
        
        try db.createTable("test")
        
        // Cause an error
        _ = try? db.scan( "nonexistent")
        
        // Database should still work
        let tid = try db.begin()
        _ = try db.insert(into: "test", row: ["id": .int(1)], tid: tid)
        try db.commit(tid)
        
        let results = try db.scan( "test")
        #expect(results.count == 1)
    }
}

