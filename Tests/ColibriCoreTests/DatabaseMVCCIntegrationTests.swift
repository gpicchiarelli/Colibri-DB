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

    @Test func deletesRemainInvisibleUntilVacuumRuns() throws {
        var config = DBConfig(storageEngine: "InMemory")
        config.autoCompactionEnabled = false
        let db = Database(config: config)
        try db.createTable("docs")
        try db.createIndex(name: "idx_docs_title", on: "docs", columns: ["title"], using: "hash")

        let rid = try db.insert(into: "docs", row: ["title": .string("Design"), "body": .string("Draft")])
        let scanBefore = try db.scan("docs").map { $0.1 }
        #expect(scanBefore.count == 1)

        _ = try db.deleteEquals(table: "docs", column: "title", value: .string("Design"))
        let scanAfter = try db.scan("docs").map { $0.1 }
        #expect(scanAfter.isEmpty)

        let indexHits = try db.indexSearchEqualsTyped(table: "docs", index: "idx_docs_title", value: .string("Design"))
        #expect(indexHits.isEmpty)

        // Vacuum should be able to reclaim tombstone and keep table empty
        _ = try db.compactTable(table: "docs", pageId: nil)
        let scanVacuumed = try db.scan("docs").map { $0.1 }
        #expect(scanVacuumed.isEmpty)
        let indexHitsVacuumed = try db.indexSearchEqualsTyped(table: "docs", index: "idx_docs_title", value: .string("Design"))
        #expect(indexHitsVacuumed.isEmpty)

        // Reinserting should work and be visible again
        let rid2 = try db.insert(into: "docs", row: ["title": .string("Design"), "body": .string("Final")])
        #expect(rid2 != rid)
        let hitsReinsert = try db.indexSearchEqualsTyped(table: "docs", index: "idx_docs_title", value: .string("Design"))
        #expect(hitsReinsert == [rid2])
    }
}

