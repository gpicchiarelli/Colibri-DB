//
//  ConcurrencyStressTests.swift
//  ColibrDB Tests
//
//  Stress tests for concurrent operations
//

import Foundation
@_spi(Experimental) import Testing
@testable import ColibriCore

@Suite("Concurrency Stress Tests", .serialized)
struct ConcurrencyStressTests {
    
    func createTestDatabase() throws -> Database {
        let tempDir = FileManager.default.temporaryDirectory.appendingPathComponent(UUID().uuidString)
        var config = DBConfig()
        config.dataDir = tempDir.path
        config.walEnabled = false
        
        let db = try Database(config: config)
        try db.createTable("stress_test")
        return db
    }
    
    @Test("100 concurrent inserts")
    func testConcurrentInserts() throws {
        let db = try createTestDatabase()
        defer { try? db.close() }
        
        let iterations = 100
        var errors: [Error] = []
        let errorLock = NSLock()
        
        DispatchQueue.concurrentPerform(iterations: iterations) { i in
            do {
                let tid = try db.begin()
                let row: Row = ["id": .int(Int64(i)), "data": .string("concurrent_\(i)")]
                _ = try db.insert(into: "stress_test", row: row, tid: tid)
                try db.commit(tid)
            } catch {
                errorLock.lock()
                errors.append(error)
                errorLock.unlock()
            }
        }
        
        #expect(errors.isEmpty, "Found \(errors.count) errors")
        
        let results = try db.scan( "stress_test")
        #expect(results.count == iterations)
    }
    
    @Test("Concurrent reads and writes")
    func testConcurrentReadsWrites() throws {
        let db = try createTestDatabase()
        defer { try? db.close() }
        
        // Setup initial data
        let setupTid = try db.begin()
        for i in 0..<10 {
            let row: Row = ["id": .int(Int64(i)), "value": .int(Int64(i * 100))]
            _ = try db.insert(into: "stress_test", row: row, tid: setupTid)
        }
        try db.commit(setupTid)
        
        var errors: [Error] = []
        let errorLock = NSLock()
        let iterations = 50
        
        DispatchQueue.concurrentPerform(iterations: iterations) { i in
            do {
                if i % 2 == 0 {
                    // Read
                    _ = try db.scan( "stress_test")
                } else {
                    // Write
                    let tid = try db.begin()
                    let row: Row = ["id": .int(Int64(100 + i)), "value": .int(Int64(i))]
                    _ = try db.insert(into: "stress_test", row: row, tid: tid)
                    try db.commit(tid)
                }
            } catch {
                errorLock.lock()
                errors.append(error)
                errorLock.unlock()
            }
        }
        
        #expect(errors.isEmpty)
    }
    
    @Test("Transaction abort stress")
    func testTransactionAborts() throws {
        let db = try createTestDatabase()
        defer { try? db.close() }
        
        let iterations = 50
        var successCount = 0
        let lock = NSLock()
        
        DispatchQueue.concurrentPerform(iterations: iterations) { i in
            do {
                let tid = try db.begin()
                let row: Row = ["id": .int(Int64(i))]
                _ = try db.insert(into: "stress_test", row: row, tid: tid)
                
                if i % 3 == 0 {
                    try db.rollback(tid)
                } else {
                    try db.commit(tid)
                    lock.lock()
                    successCount += 1
                    lock.unlock()
                }
            } catch {
                // Expected some failures due to contention
            }
        }
        
        let finalRows = try db.scan( "stress_test")
        #expect(finalRows.count == successCount)
    }
}

