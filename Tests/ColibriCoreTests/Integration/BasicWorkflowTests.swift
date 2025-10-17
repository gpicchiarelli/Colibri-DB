//
//  BasicWorkflowTests.swift
//  ColibrDB Tests
//
//  Integration tests for complete workflows
//

import Foundation
@_spi(Experimental) import Testing
@testable import ColibriCore

@Suite("Basic Workflow Integration Tests", .serialized)
struct BasicWorkflowTests {
    
    func createTestDatabase() throws -> Database {
        let tempDir = FileManager.default.temporaryDirectory.appendingPathComponent(UUID().uuidString)
        var config = DBConfig()
        config.dataDir = tempDir.path
        
        return try Database(config: config)
    }
    
    @Test("Complete CRUD workflow")
    func testCompleteCRUD() throws {
        let db = try createTestDatabase()
        defer { try? db.close() }
        
        // Create
        try db.createTable("users")
        
        // Insert
        let tid1 = try db.begin()
        let rid1 = try db.insert(into: "users", row: ["id": .int(1), "name": .string("Alice")], tid: tid1)
        let rid2 = try db.insert(into: "users", row: ["id": .int(2), "name": .string("Bob")], tid: tid1)
        try db.commit(tid1)
        
        // Read
        let row1 = try db.read(table: "users", rid: rid1)
        #expect(row1["name"] == .string("Alice"))
        
        // Update
        let tid2 = try db.begin()
        try db.update(table: "users", rid: rid1, newRow: ["id": .int(1), "name": .string("Alice Updated")], tid: tid2)
        try db.commit(tid2)
        
        let updated = try db.read(table: "users", rid: rid1)
        #expect(updated["name"] == .string("Alice Updated"))
        
        // Delete
        let tid3 = try db.begin()
        try db.delete(table: "users", rid: rid2, tid: tid3)
        try db.commit(tid3)
        
        let remaining = try db.scan( "users")
        #expect(remaining.count == 1)
    }
    
    @Test("Transaction rollback workflow")
    func testTransactionRollback() throws {
        let db = try createTestDatabase()
        defer { try? db.close() }
        
        try db.createTable("test")
        
        // Insert and commit
        let tid1 = try db.begin()
        _ = try db.insert(into: "test", row: ["id": .int(1)], tid: tid1)
        try db.commit(tid1)
        
        // Insert and rollback
        let tid2 = try db.begin()
        _ = try db.insert(into: "test", row: ["id": .int(2)], tid: tid2)
        try db.rollback(tid2)
        
        // Only first insert should be visible
        let results = try db.scan( "test")
        #expect(results.count == 1)
        #expect(results[0].row["id"] == .int(1))
    }
    
    @Test("Multiple tables workflow")
    func testMultipleTables() throws {
        let db = try createTestDatabase()
        defer { try? db.close() }
        
        try db.createTable("users")
        try db.createTable("orders")
        
        let tid = try db.begin()
        
        _ = try db.insert(into: "users", row: ["id": .int(1), "name": .string("User1")], tid: tid)
        _ = try db.insert(into: "orders", row: ["id": .int(1), "user_id": .int(1), "amount": .double(99.99)], tid: tid)
        
        try db.commit(tid)
        
        let users = try db.scan( "users")
        let orders = try db.scan( "orders")
        
        #expect(users.count == 1)
        #expect(orders.count == 1)
    }
    
    @Test("Large batch insert workflow")
    func testLargeBatchInsert() throws {
        let db = try createTestDatabase()
        defer { try? db.close() }
        
        try db.createTable("batch")
        
        let tid = try db.begin()
        
        for i in 0..<1000 {
            let row: Row = [
                "id": .int(Int64(i)),
                "value": .string("data_\(i)"),
                "score": .double(Double(i) * 1.5)
            ]
            _ = try db.insert(into: "batch", row: row, tid: tid)
        }
        
        try db.commit(tid)
        
        let results = try db.scan( "batch")
        #expect(results.count == 1000)
    }
}

