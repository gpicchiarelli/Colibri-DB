//
//  TransactionManagerTests.swift
//  ColibrDB Tests
//

import Foundation
@_spi(Experimental) import Testing
@testable import ColibriCore

@Suite("Transaction Manager Tests", .serialized)
struct TransactionManagerTests {
    
    func createTestDatabase() throws -> Database {
        let tempDir = FileManager.default.temporaryDirectory
            .appendingPathComponent(UUID().uuidString)
        var config = DBConfig()
        config.dataDir = tempDir.path
        
        return try Database(config: config)
    }
    
    @Test("Begin transaction returns TID")
    func testBeginTransaction() throws {
        let db = try createTestDatabase()
        defer { try? db.close() }
        
        let tid = try db.begin()
        
        #expect(tid > 0)
    }
    
    @Test("Commit transaction succeeds")
    func testCommitTransaction() throws {
        let db = try createTestDatabase()
        defer { try? db.close() }
        
        let tid = try db.begin()
        
        // Should not throw
        try db.commit(tid)
    }
    
    @Test("Rollback transaction succeeds")
    func testRollbackTransaction() throws {
        let db = try createTestDatabase()
        defer { try? db.close() }
        
        let tid = try db.begin()
        
        // Should not throw
        try db.rollback(tid)
    }
    
    @Test("Multiple transactions get unique TIDs")
    func testUniqueTIDs() throws {
        let db = try createTestDatabase()
        defer { try? db.close() }
        
        let tid1 = try db.begin()
        let tid2 = try db.begin()
        let tid3 = try db.begin()
        
        #expect(tid1 != tid2)
        #expect(tid2 != tid3)
        #expect(tid1 != tid3)
        
        try db.rollback(tid1)
        try db.rollback(tid2)
        try db.rollback(tid3)
    }
    
    @Test("Transaction isolation - read committed")
    func testReadCommitted() throws {
        let db = try createTestDatabase()
        defer { try? db.close() }
        
        try db.createTable("test")
        
        // T1: Insert but don't commit
        let tid1 = try db.begin()
        _ = try db.insert(into: "test", row: ["id": .int(1)], tid: tid1)
        
        // T2: Should not see uncommitted data
        let tid2 = try db.begin()
        let results = try db.scan( "test", tid: tid2)
        #expect(results.isEmpty)
        
        // Commit T1
        try db.commit(tid1)
        
        // T2 in new snapshot should see committed data
        try db.rollback(tid2)
        let tid3 = try db.begin()
        let results2 = try db.scan( "test", tid: tid3)
        #expect(results2.count == 1)
        
        try db.commit(tid3)
    }
    
    @Test("Transaction isolation - repeatable read")
    func testRepeatableRead() throws {
        var config = DBConfig()
        config.dataDir = FileManager.default.temporaryDirectory
            .appendingPathComponent(UUID().uuidString).path
        config.defaultIsolationLevel = .repeatableRead
        
        let db = try Database(config: config)
        defer { try? db.close() }
        
        try db.createTable("test")
        
        // Insert initial data
        let setupTid = try db.begin()
        _ = try db.insert(into: "test", row: ["id": .int(1)], tid: setupTid)
        try db.commit(setupTid)
        
        // T1: Read
        let tid1 = try db.begin(isolation: .repeatableRead)
        let read1 = try db.scan( "test", tid: tid1)
        #expect(read1.count == 1)
        
        // T2: Insert more data and commit
        let tid2 = try db.begin()
        _ = try db.insert(into: "test", row: ["id": .int(2)], tid: tid2)
        try db.commit(tid2)
        
        // T1: Read again - should still see same data (repeatable read)
        let read2 = try db.scan( "test", tid: tid1)
        #expect(read2.count == 1) // Phantom protection
        
        try db.commit(tid1)
    }
    
    @Test("Abort transaction undoes changes")
    func testAbortUndoes() throws {
        let db = try createTestDatabase()
        defer { try? db.close() }
        
        try db.createTable("test")
        
        let tid = try db.begin()
        _ = try db.insert(into: "test", row: ["id": .int(1)], tid: tid)
        _ = try db.insert(into: "test", row: ["id": .int(2)], tid: tid)
        _ = try db.insert(into: "test", row: ["id": .int(3)], tid: tid)
        
        // Rollback
        try db.rollback(tid)
        
        // Nothing should be committed
        let results = try db.scan( "test")
        #expect(results.isEmpty)
    }
    
    @Test("Concurrent non-conflicting transactions")
    func testConcurrentNonConflicting() throws {
        let db = try createTestDatabase()
        defer { try? db.close() }
        
        try db.createTable("test")
        
        var errors: [Error] = []
        let errorLock = NSLock()
        
        DispatchQueue.concurrentPerform(iterations: 20) { i in
            do {
                let tid = try db.begin()
                let row: Row = ["id": .int(Int64(i)), "data": .string("tx_\(i)")]
                _ = try db.insert(into: "test", row: row, tid: tid)
                try db.commit(tid)
            } catch {
                errorLock.lock()
                errors.append(error)
                errorLock.unlock()
            }
        }
        
        #expect(errors.isEmpty)
        
        let results = try db.scan( "test")
        #expect(results.count == 20)
    }
    
    @Test("Transaction commit is durable")
    func testTransactionDurability() throws {
        let tempDir = FileManager.default.temporaryDirectory
            .appendingPathComponent(UUID().uuidString)
        var config = DBConfig()
        config.dataDir = tempDir.path
        config.walEnabled = true
        
        // Write and commit
        do {
            let db = try Database(config: config)
            try db.createTable("test")
            
            let tid = try db.begin()
            _ = try db.insert(into: "test", row: ["id": .int(42)], tid: tid)
            try db.commit(tid)
            
            // Force a checkpoint to ensure data is written
            try db.checkpoint()
            
            try db.close()
        }
        
        // Reopen and verify
        do {
            let db = try Database(config: config)
            let results = try db.scan( "test")
            
            #expect(results.count == 1)
            if !results.isEmpty {
                #expect(results[0].1["id"] == .int(42))
            }
            
            try db.close()
        }
    }
}

