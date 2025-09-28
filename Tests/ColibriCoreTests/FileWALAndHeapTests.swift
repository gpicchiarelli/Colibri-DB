//
//  FileWALAndHeapTests.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//

// Theme: WAL and heap sagas checking durability and recovery arcs.

import Foundation
@_spi(Experimental) import Testing
@testable import ColibriCore

@Suite(.serialized)
struct FileWALTests {
    @Test func readAllStopsWhenEncounteringCorruptedRecord() throws {
        let tempDir = FileManager.default.temporaryDirectory.appendingPathComponent(UUID().uuidString, isDirectory: true)
        try FileManager.default.createDirectory(at: tempDir, withIntermediateDirectories: true)
        defer { try? FileManager.default.removeItem(at: tempDir) }

        let walPath = tempDir.appendingPathComponent("wal.log").path
        var wal: FileWAL? = try FileWAL(path: walPath)
        defer { wal = nil }

        _ = try wal?.appendInsert(table: "items", row: ["id": .int(1)])
        _ = try wal?.appendDelete(table: "items", rid: RID(pageId: 1, slotId: 1))
        try wal?.flushPending()
        wal = nil

        var bytes = try Data(contentsOf: URL(fileURLWithPath: walPath))
        if !bytes.isEmpty {
            bytes[bytes.count - 1] ^= 0xFF
            try bytes.write(to: URL(fileURLWithPath: walPath))
        }

        let walRecovered = try FileWAL(path: walPath)
        let records = try walRecovered.readAll()
        #expect(records.count == 1)
        #expect(records.first?.type == .insertRow)
    }

    @Test func recoveryUndoesIncompleteTransactions() throws {
        let tempDir = FileManager.default.temporaryDirectory.appendingPathComponent(UUID().uuidString, isDirectory: true)
        try FileManager.default.createDirectory(at: tempDir, withIntermediateDirectories: true)
        defer { try? FileManager.default.removeItem(at: tempDir) }

        var config = DBConfig(dataDir: tempDir.path)
        config.autoCompactionEnabled = false
        config.lockTimeoutSeconds = 0.5
        config.dataBufferPoolPages = 8
        config.indexBufferPoolPages = 4

        do {
            let db = Database(config: config)
            try db.createTable("events")
            let tid = try db.begin(isolation: .readCommitted)
            _ = try db.insert(into: "events", row: ["id": .int(1)], tid: tid)
            db.flushAll()
            try db.globalWAL?.groupCommitSync()
            // Simulate crash by dropping the instance without committing.
        }

        let recovered = Database(config: config)
        try recovered.createTable("events")
        try recovered.replayGlobalWAL()

        let rows = try recovered.scan("events")
        #expect(rows.isEmpty)

        let walRecords = try recovered.globalWAL?.iterate(from: 1).reduce(into: [WALRecord]()) { records, record in
            records.append(record)
        } ?? []
        #expect(!walRecords.isEmpty, "Expected WAL records to remain readable after recovery")
    }
}

@Suite(.serialized)
struct FileHeapTableTests {
    @Test func rebuildsFSMWhenSidecarIsCorrupted() throws {
        let tempDir = FileManager.default.temporaryDirectory.appendingPathComponent(UUID().uuidString, isDirectory: true)
        try FileManager.default.createDirectory(at: tempDir, withIntermediateDirectories: true)
        defer { try? FileManager.default.removeItem(at: tempDir) }

        let tablePath = tempDir.appendingPathComponent("heap.dat").path
        var table: FileHeapTable? = try FileHeapTable(path: tablePath, pageSize: 512, capacityPages: 4)
        let ridA = try table?.insert(["id": .int(1)])
        let ridB = try table?.insert(["id": .int(2)])
        #expect(ridA != nil && ridB != nil)
        try table?.flush()
        table = nil

        let fsmURL = URL(fileURLWithPath: tablePath + ".fsm")
        try "corrupted".data(using: .utf8)?.write(to: fsmURL)

        table = try FileHeapTable(path: tablePath, pageSize: 512, capacityPages: 4)
        let rows = try table?.scan().map { $0.1 } ?? []
        #expect(rows.count == 2)

        let ridC = try table?.insert(["id": .int(3)])
        #expect(ridC != nil)
    }
}

