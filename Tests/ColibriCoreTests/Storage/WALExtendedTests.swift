//
//  WALExtendedTests.swift
//  ColibrDB Tests
//

import Foundation
@_spi(Experimental) import Testing
@testable import ColibriCore

@Suite("WAL Extended Tests", .serialized)
struct WALExtendedTests {
    
    func createTestWAL() throws -> FileWAL {
        let tempDir = FileManager.default.temporaryDirectory
            .appendingPathComponent(UUID().uuidString)
        try FileManager.default.createDirectory(at: tempDir, withIntermediateDirectories: true)
        let walPath = tempDir.appendingPathComponent("test.wal").path
        return try FileWAL(path: walPath)
    }
    
    @Test("Append record returns LSN")
    func testAppendReturnsLSN() throws {
        var wal = try createTestWAL()
        
        let data = Data("test record".utf8)
        let lsn = try wal.append(record: data)
        
        #expect(lsn > 0)
    }
    
    @Test("Sequential LSNs increase")
    func testSequentialLSNs() throws {
        var wal = try createTestWAL()
        
        let lsn1 = try wal.append(record: Data("record1".utf8))
        let lsn2 = try wal.append(record: Data("record2".utf8))
        let lsn3 = try wal.append(record: Data("record3".utf8))
        
        #expect(lsn2 > lsn1)
        #expect(lsn3 > lsn2)
    }
    
    @Test("Flush to specific LSN")
    func testFlushToLSN() throws {
        var wal = try createTestWAL()
        
        let lsn1 = try wal.append(record: Data("record1".utf8))
        let lsn2 = try wal.append(record: Data("record2".utf8))
        
        try wal.flush(upTo: lsn2)
        
        // If no exception, flush succeeded
        #expect(true)
    }
    
    @Test("Read all records")
    func testReadAllRecords() throws {
        var wal = try createTestWAL()
        
        _ = try wal.append(record: Data("record1".utf8))
        _ = try wal.append(record: Data("record2".utf8))
        _ = try wal.append(record: Data("record3".utf8))
        
        try wal.flush(upTo: 3)
        
        let records = try wal.readAll()
        #expect(records.count == 3)
    }
    
    @Test("Empty WAL has no records")
    func testEmptyWAL() throws {
        let wal = try createTestWAL()
        
        let records = try wal.readAll()
        #expect(records.isEmpty)
    }
    
    @Test("Append multiple records batch")
    func testBatchAppend() throws {
        var wal = try createTestWAL()
        
        for i in 0..<100 {
            let data = Data("record_\(i)".utf8)
            _ = try wal.append(record: data)
        }
        
        try wal.flush(upTo: 100)
        
        let records = try wal.readAll()
        #expect(records.count == 100)
    }
    
    @Test("Large record append")
    func testLargeRecord() throws {
        var wal = try createTestWAL()
        
        let largeData = Data(repeating: 0xAB, count: 10_000)
        let lsn = try wal.append(record: largeData)
        
        #expect(lsn > 0)
    }
    
    @Test("WAL persists after close and reopen")
    func testPersistence() throws {
        let tempDir = FileManager.default.temporaryDirectory
            .appendingPathComponent(UUID().uuidString)
        try FileManager.default.createDirectory(at: tempDir, withIntermediateDirectories: true)
        let walPath = tempDir.appendingPathComponent("persist.wal").path
        
        // Write some records
        do {
            var wal = try FileWAL(path: walPath)
            _ = try wal.append(record: Data("persistent1".utf8))
            _ = try wal.append(record: Data("persistent2".utf8))
            try wal.flush(upTo: 2)
        }
        
        // Reopen and verify
        do {
            let wal = try FileWAL(path: walPath)
            let records = try wal.readAll()
            #expect(records.count == 2)
        }
    }
}

