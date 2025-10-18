//
//  StoragePropertyTests.swift
//  ColibrDB Tests
//
//  Property-based tests for storage invariants
//

import Foundation
@_spi(Experimental) import Testing
@testable import ColibriCore

@Suite("Storage Property Tests")
struct StoragePropertyTests {
    
    func createTestDB() throws -> Database {
        let tempDir = FileManager.default.temporaryDirectory
            .appendingPathComponent(UUID().uuidString)
        var config = DBConfig()
        config.dataDir = tempDir.path
        return Database(config: config)
    }
    
    // Property: Insert then Read always returns same data
    @Test("Property: Insert→Read identity", arguments: 1...20)
    func testInsertReadIdentity(seed: Int) throws {
        let db = try createTestDB()
        defer { try? db.close() }
        
        try db.createTable("test")
        
        let row: Row = [
            "id": .int(Int64(seed)),
            "name": .string("User\(seed)"),
            "value": .double(Double(seed) * 1.5)
        ]
        
        let rid = try db.insert(into: "test", row: row)
        let retrieved = try db.readRow(table: "test", rid: rid)
        
        #expect(retrieved == row)
    }
    
    // Property: Update changes data
    @Test("Property: Update→Read reflects change", arguments: 1...15)
    func testUpdateChangesData(seed: Int) throws {
        let db = try createTestDB()
        defer { try? db.close() }
        
        try db.createTable("test")
        
        let original: Row = ["value": .int(Int64(seed))]
        let rid = try db.insert(into: "test", row: original)
        
        let updated: Row = ["value": .int(Int64(seed * 2))]
        _ = try db.deleteBatch(table: "test", rids: [rid])
        let newRid = try db.insert(into: "test", row: updated)
        
        let retrieved = try db.readRow(table: "test", rid: newRid)
        #expect(retrieved == updated)
        #expect(retrieved != original)
    }
    
    // Property: Delete makes row unreadable
    @Test("Property: Delete→Read fails", arguments: 1...15)
    func testDeleteMakesUnreadable(seed: Int) throws {
        let db = try createTestDB()
        defer { try? db.close() }
        
        try db.createTable("test")
        
        let row: Row = ["id": .int(Int64(seed))]
        let rid = try db.insert(into: "test", row: row)
        
        _ = try db.deleteBatch(table: "test", rids: [rid])
        
        #expect(throws: Error.self) {
            _ = try db.readRow(table: "test", rid: rid)
        }
    }
    
    // Property: Scan returns all non-deleted rows
    @Test("Property: Scan completeness", arguments: 5...25)
    func testScanCompleteness(rowCount: Int) throws {
        let db = try createTestDB()
        defer { try? db.close() }
        
        try db.createTable("test")
        
        var insertedRIDs: Set<RID> = []
        
        for i in 0..<rowCount {
            let row: Row = ["id": .int(Int64(i))]
            let rid = try db.insert(into: "test", row: row)
            insertedRIDs.insert(rid)
        }
        
        let scannedRIDs = Set(try db.scan("test").map { $0.0 })
        
        #expect(scannedRIDs == insertedRIDs)
    }
    
    // Property: Multiple inserts don't interfere
    @Test("Property: Insert independence", arguments: 1...10)
    func testInsertIndependence(batchSize: Int) throws {
        let db = try createTestDB()
        defer { try? db.close() }
        
        try db.createTable("test")
        
        var insertedData: [(RID, Row)] = []
        
        for i in 0..<batchSize {
            let row: Row = [
                "id": .int(Int64(i)),
                "unique": .string(UUID().uuidString)
            ]
            let rid = try db.insert(into: "test", row: row)
            insertedData.append((rid, row))
        }
        
        // Verify each insert independently
        for (rid, expectedRow) in insertedData {
            let retrieved = try db.readRow(table: "test", rid: rid)
            #expect(retrieved == expectedRow)
        }
    }
    
    // Property: RID uniqueness
    @Test("Property: RID uniqueness", arguments: 10...30)
    func testRIDUniqueness(insertCount: Int) throws {
        let db = try createTestDB()
        defer { try? db.close() }
        
        try db.createTable("test")
        
        var rids: [RID] = []
        
        for i in 0..<insertCount {
            let row: Row = ["id": .int(Int64(i))]
            let rid = try db.insert(into: "test", row: row)
            rids.append(rid)
        }
        
        // All RIDs should be unique
        let uniqueRIDs = Set(rids)
        #expect(uniqueRIDs.count == rids.count)
    }
}

