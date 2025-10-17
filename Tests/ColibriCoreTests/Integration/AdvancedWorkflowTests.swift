//
//  AdvancedWorkflowTests.swift
//  ColibrDB Tests
//

import Foundation
@_spi(Experimental) import Testing
@testable import ColibriCore

@Suite("Advanced Workflow Integration Tests", .serialized)
struct AdvancedWorkflowTests {
    
    func createTestDatabase() throws -> Database {
        let tempDir = FileManager.default.temporaryDirectory
            .appendingPathComponent(UUID().uuidString)
        var config = DBConfig()
        config.dataDir = tempDir.path
        
        return try Database(config: config)
    }
    
    @Test("Multi-table transaction workflow")
    func testMultiTableTransaction() throws {
        let db = try createTestDatabase()
        defer { try? db.close() }
        
        try db.createTable("users")
        try db.createTable("orders")
        
        let tid = try db.begin()
        
        // Insert into both tables
        let userRID = try db.insert(
            table: "users",
            row: ["id": .int(1), "name": .string("Alice")],
            tid: tid
        )
        
        let orderRID = try db.insert(
            table: "orders",
            row: ["id": .int(1), "user_id": .int(1), "amount": .double(99.99)],
            tid: tid
        )
        
        // Commit both
        try db.commit(tid)
        
        // Verify both
        let user = try db.read(table: "users", rid: userRID)
        let order = try db.read(table: "orders", rid: orderRID)
        
        #expect(user["name"] == .string("Alice"))
        #expect(order["amount"] == .double(99.99))
    }
    
    @Test("Index and table consistency")
    func testIndexTableConsistency() throws {
        let db = try createTestDatabase()
        defer { try? db.close() }
        
        try db.createTable("products")
        try db.createIndex(table: "products", name: "idx_id", columns: ["id"], indexType: "BTree")
        
        let tid = try db.begin()
        
        // Insert data
        for i in 1...10 {
            let row: Row = ["id": .int(Int64(i)), "name": .string("Product\(i)")]
            _ = try db.insert(table: "products", row: row, tid: tid)
        }
        
        try db.commit(tid)
        
        // Verify via table scan
        let scanResults = try db.scan(table: "products")
        #expect(scanResults.count == 10)
        
        // Verify via index
        let indexResults = try db.indexSearch(table: "products", index: "idx_id", key: "5")
        #expect(indexResults.count == 1)
    }
    
    @Test("Cascade delete workflow")
    func testCascadeDelete() throws {
        let db = try createTestDatabase()
        defer { try? db.close() }
        
        try db.createTable("parent")
        try db.createTable("child")
        
        let tid = try db.begin()
        
        let parentRID = try db.insert(
            table: "parent",
            row: ["id": .int(1), "name": .string("Parent")],
            tid: tid
        )
        
        let childRID1 = try db.insert(
            table: "child",
            row: ["id": .int(1), "parent_id": .int(1)],
            tid: tid
        )
        
        let childRID2 = try db.insert(
            table: "child",
            row: ["id": .int(2), "parent_id": .int(1)],
            tid: tid
        )
        
        try db.commit(tid)
        
        // Delete parent
        let deleteTid = try db.begin()
        try db.delete(table: "parent", rid: parentRID, tid: deleteTid)
        
        // Manually delete children (cascade logic)
        try db.delete(table: "child", rid: childRID1, tid: deleteTid)
        try db.delete(table: "child", rid: childRID2, tid: deleteTid)
        
        try db.commit(deleteTid)
        
        // Verify all deleted
        let parents = try db.scan(table: "parent")
        let children = try db.scan(table: "child")
        
        #expect(parents.isEmpty)
        #expect(children.isEmpty)
    }
    
    @Test("Bulk load workflow")
    func testBulkLoad() throws {
        let db = try createTestDatabase()
        defer { try? db.close() }
        
        try db.createTable("bulk")
        
        let tid = try db.begin()
        
        // Insert 500 rows in one transaction
        for i in 0..<500 {
            let row: Row = [
                "id": .int(Int64(i)),
                "data": .string("bulk_\(i)"),
                "value": .double(Double(i) * 1.5)
            ]
            _ = try db.insert(table: "bulk", row: row, tid: tid)
        }
        
        try db.commit(tid)
        
        let results = try db.scan(table: "bulk")
        #expect(results.count == 500)
    }
    
    @Test("Savepoint workflow")
    func testSavepointWorkflow() throws {
        let db = try createTestDatabase()
        defer { try? db.close() }
        
        try db.createTable("test")
        
        let tid = try db.begin()
        
        // Insert first batch
        _ = try db.insert(table: "test", row: ["id": .int(1)], tid: tid)
        _ = try db.insert(table: "test", row: ["id": .int(2)], tid: tid)
        
        // Savepoint
        try db.setSavepoint(tid: tid, name: "sp1")
        
        // Insert more
        _ = try db.insert(table: "test", row: ["id": .int(3)], tid: tid)
        _ = try db.insert(table: "test", row: ["id": .int(4)], tid: tid)
        
        // Rollback to savepoint
        try db.rollbackToSavepoint(tid: tid, name: "sp1")
        
        // Commit
        try db.commit(tid)
        
        // Should only have first 2 rows
        let results = try db.scan(table: "test")
        #expect(results.count == 2)
    }
    
    @Test("Transaction timeout scenario")
    func testTransactionTimeout() throws {
        var config = DBConfig()
        config.dataDir = FileManager.default.temporaryDirectory
            .appendingPathComponent(UUID().uuidString).path
        config.lockTimeoutSeconds = 0.1  // Very short timeout
        
        let db = try Database(config: config)
        defer { try? db.close() }
        
        try db.createTable("test")
        
        // T1: Lock a row
        let tid1 = try db.begin()
        let rid = try db.insert(table: "test", row: ["id": .int(1)], tid: tid1)
        
        // T2: Try to update same row - should timeout
        let tid2 = try db.begin()
        
        #expect(throws: DBError.self) {
            try db.update(table: "test", rid: rid, newRow: ["id": .int(1), "updated": .bool(true)], tid: tid2)
        }
        
        try db.rollback(tid2)
        try db.commit(tid1)
    }
    
    @Test("Long-running transaction")
    func testLongRunningTransaction() throws {
        let db = try createTestDatabase()
        defer { try? db.close() }
        
        try db.createTable("test")
        
        let tid = try db.begin()
        
        // Insert over time
        for i in 0..<50 {
            let row: Row = ["id": .int(Int64(i))]
            _ = try db.insert(table: "test", row: row, tid: tid)
            
            if i % 10 == 0 {
                Thread.sleep(forTimeInterval: 0.01) // Simulate work
            }
        }
        
        try db.commit(tid)
        
        let results = try db.scan(table: "test")
        #expect(results.count == 50)
    }
    
    @Test("Nested transaction simulation")
    func testNestedTransactions() throws {
        let db = try createTestDatabase()
        defer { try? db.close() }
        
        try db.createTable("test")
        
        // Outer transaction
        let outerTid = try db.begin()
        _ = try db.insert(table: "test", row: ["id": .int(1), "level": .string("outer")], tid: outerTid)
        
        // Savepoint simulates inner transaction
        try db.setSavepoint(tid: outerTid, name: "inner")
        _ = try db.insert(table: "test", row: ["id": .int(2), "level": .string("inner")], tid: outerTid)
        
        // Rollback inner
        try db.rollbackToSavepoint(tid: outerTid, name: "inner")
        
        // Commit outer
        try db.commit(outerTid)
        
        let results = try db.scan(table: "test")
        #expect(results.count == 1)
        #expect(results[0].row["level"] == .string("outer"))
    }
}

