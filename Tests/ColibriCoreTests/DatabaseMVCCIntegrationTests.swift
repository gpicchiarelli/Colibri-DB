//
//  DatabaseMVCCIntegrationTests.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//

// Theme: MVCC trials exercising visibility and vacuum stories.

import Foundation
@_spi(Experimental) import Testing
@testable import ColibriCore

@Suite(.serialized)
struct DatabaseMVCCIntegrationTests {
    @Test func mvccIsolationAndVacuumFlow() throws {
        let tempDir = FileManager.default.temporaryDirectory.appendingPathComponent(UUID().uuidString, isDirectory: true)
        try FileManager.default.createDirectory(at: tempDir, withIntermediateDirectories: true)
        defer { try? FileManager.default.removeItem(at: tempDir) }

        var config = DBConfig(dataDir: tempDir.path)
        config.autoCompactionEnabled = false
        config.lockTimeoutSeconds = 1.0
        config.defaultIsolationLevel = .readCommitted

        let db = Database(config: config)
        try db.createTable("items")

        let rid1 = try db.insert(into: "items", row: ["id": .int(1)])

        let txRepeatable = try db.begin(isolation: .repeatableRead)
        let repeatableContext = db.txContexts[txRepeatable]
        let repeatableSnapshot = db.mvcc.snapshot(for: txRepeatable, isolationCutoff: repeatableContext?.snapshotCutoff)
        let initialVisible = db.mvcc.visibleRows(table: "items", snapshot: repeatableSnapshot, readerTID: txRepeatable)
        #expect(initialVisible.count == 1)
        #expect(initialVisible.values.first?["id"] == .int(1))

        let txReadCommitted = try db.begin(isolation: .readCommitted)
        let rid2 = try db.insert(into: "items", row: ["id": .int(2)], tid: txReadCommitted)

        let duringInsertVisible = db.mvcc.visibleRows(table: "items", snapshot: repeatableSnapshot, readerTID: txRepeatable)
        #expect(duringInsertVisible.count == 1)
        #expect(duringInsertVisible.values.first?["id"] == .int(1))

        try db.commit(txReadCommitted)

        let afterCommitSnapshot = try db.scan("items", tid: txRepeatable)
        #expect(afterCommitSnapshot.count == 1)
        #expect(afterCommitSnapshot.first?.1["id"] == .int(1))
        db.lockManager.unlockAll(for: txRepeatable)

        let txObserver = try db.begin(isolation: .readCommitted)
        let observerRows = try db.scan("items", tid: txObserver)
        let observerIds = observerRows.compactMap { rowPair -> Int in
            if case let .int(val) = rowPair.1["id"] { return Int(val) }
            return -1
        }.sorted()
        #expect(observerIds == [1, 2])
        try db.commit(txObserver)

        try db.commit(txRepeatable)

        let txDelete = try db.begin(isolation: .readCommitted)
        let deleted = try db.deleteEquals(table: "items", column: "id", value: .int(1), tid: txDelete)
        #expect(deleted == 1)
        try db.commit(txDelete)

        db.vacuumTick()

        let postVacuumRows = try db.scan("items")
        #expect(postVacuumRows.count == 1)
        #expect(postVacuumRows.first?.1["id"] == .int(2))

        let versions = db.mvcc.allVersions(for: "items")
        #expect(versions[rid1] == nil)
        #expect(versions[rid2] != nil)
        if let chain = versions[rid2] {
            #expect(!chain.isEmpty)
        }
    }
}

