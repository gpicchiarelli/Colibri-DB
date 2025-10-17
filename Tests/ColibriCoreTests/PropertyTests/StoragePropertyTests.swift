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
    
    // Property: Insert then Read always returns same data
    @Test("Property: Insert→Read identity", arguments: 1...20)
    func testInsertReadIdentity(seed: Int) throws {
        let tempPath = FileManager.default.temporaryDirectory
            .appendingPathComponent(UUID().uuidString)
            .appendingPathComponent("test.dat").path
        
        var table = try FileHeapTable(path: tempPath, pageSize: 8192)
        defer { try? table.close() }
        
        let row: Row = [
            "id": .int(Int64(seed)),
            "name": .string("User\(seed)"),
            "value": .double(Double(seed) * 1.5)
        ]
        
        let rid = try table.insert(row)
        let retrieved = try table.read(rid)
        
        #expect(retrieved == row)
    }
    
    // Property: Update changes data
    @Test("Property: Update→Read reflects change", arguments: 1...15)
    func testUpdateChangesData(seed: Int) throws {
        let tempPath = FileManager.default.temporaryDirectory
            .appendingPathComponent(UUID().uuidString)
            .appendingPathComponent("test.dat").path
        
        var table = try FileHeapTable(path: tempPath, pageSize: 8192)
        defer { try? table.close() }
        
        let original: Row = ["value": .int(Int64(seed))]
        let rid = try table.insert(original)
        
        let updated: Row = ["value": .int(Int64(seed * 2))]
        try table.update(rid, updated)
        
        let retrieved = try table.read(rid)
        #expect(retrieved == updated)
        #expect(retrieved != original)
    }
    
    // Property: Delete makes row unreadable
    @Test("Property: Delete→Read fails", arguments: 1...15)
    func testDeleteMakesUnreadable(seed: Int) throws {
        let tempPath = FileManager.default.temporaryDirectory
            .appendingPathComponent(UUID().uuidString)
            .appendingPathComponent("test.dat").path
        
        var table = try FileHeapTable(path: tempPath, pageSize: 8192)
        defer { try? table.close() }
        
        let row: Row = ["id": .int(Int64(seed))]
        let rid = try table.insert(row)
        
        try table.remove(rid)
        
        #expect(throws: Error.self) {
            _ = try table.read(rid)
        }
    }
    
    // Property: Scan returns all non-deleted rows
    @Test("Property: Scan completeness", arguments: 5...25)
    func testScanCompleteness(rowCount: Int) throws {
        let tempPath = FileManager.default.temporaryDirectory
            .appendingPathComponent(UUID().uuidString)
            .appendingPathComponent("test.dat").path
        
        var table = try FileHeapTable(path: tempPath, pageSize: 8192)
        defer { try? table.close() }
        
        var insertedRIDs: Set<RID> = []
        
        for i in 0..<rowCount {
            let row: Row = ["id": .int(Int64(i))]
            let rid = try table.insert(row)
            insertedRIDs.insert(rid)
        }
        
        let scannedRIDs = Set(try table.scan().map { $0.0 })
        
        #expect(scannedRIDs == insertedRIDs)
    }
    
    // Property: Multiple inserts don't interfere
    @Test("Property: Insert independence", arguments: 1...10)
    func testInsertIndependence(batchSize: Int) throws {
        let tempPath = FileManager.default.temporaryDirectory
            .appendingPathComponent(UUID().uuidString)
            .appendingPathComponent("test.dat").path
        
        var table = try FileHeapTable(path: tempPath, pageSize: 8192)
        defer { try? table.close() }
        
        var insertedData: [(RID, Row)] = []
        
        for i in 0..<batchSize {
            let row: Row = [
                "id": .int(Int64(i)),
                "unique": .string(UUID().uuidString)
            ]
            let rid = try table.insert(row)
            insertedData.append((rid, row))
        }
        
        // Verify each insert independently
        for (rid, expectedRow) in insertedData {
            let retrieved = try table.read(rid)
            #expect(retrieved == expectedRow)
        }
    }
    
    // Property: RID uniqueness
    @Test("Property: RID uniqueness", arguments: 10...30)
    func testRIDUniqueness(insertCount: Int) throws {
        let tempPath = FileManager.default.temporaryDirectory
            .appendingPathComponent(UUID().uuidString)
            .appendingPathComponent("test.dat").path
        
        var table = try FileHeapTable(path: tempPath, pageSize: 8192)
        defer { try? table.close() }
        
        var rids: [RID] = []
        
        for i in 0..<insertCount {
            let row: Row = ["id": .int(Int64(i))]
            let rid = try table.insert(row)
            rids.append(rid)
        }
        
        // All RIDs should be unique
        let uniqueRIDs = Set(rids)
        #expect(uniqueRIDs.count == rids.count)
    }
}

