//
//  DatabaseTwoPhaseCommitTests.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//

// Theme: Two-phase tales validating distributed commit drama.

import Foundation
@_spi(Experimental) import Testing
@testable import ColibriCore

@Suite(.serialized)
struct DatabaseTwoPhaseCommitTests {
    @Test func twoPhaseCommitCoordinatorCommitsAcrossParticipants() throws {
        let root = FileManager.default.temporaryDirectory.appendingPathComponent(UUID().uuidString, isDirectory: true)
        let dirA = root.appendingPathComponent("nodeA", isDirectory: true)
        let dirB = root.appendingPathComponent("nodeB", isDirectory: true)
        try FileManager.default.createDirectory(at: dirA, withIntermediateDirectories: true)
        try FileManager.default.createDirectory(at: dirB, withIntermediateDirectories: true)
        defer { try? FileManager.default.removeItem(at: root) }

        var configA = DBConfig(dataDir: dirA.path)
        configA.autoCompactionEnabled = false
        var configB = DBConfig(dataDir: dirB.path)
        configB.autoCompactionEnabled = false

        let dbA = Database(config: configA)
        let dbB = Database(config: configB)
        try dbA.createTable("events")
        try dbB.createTable("events")

        let txA = try dbA.begin(isolation: .readCommitted)
        let txB = try dbB.begin(isolation: .readCommitted)

        _ = try dbA.insert(into: "events", row: ["node": .string("A"), "seq": .int(1)], tid: txA)
        _ = try dbB.insert(into: "events", row: ["node": .string("B"), "seq": .int(1)], tid: txB)

        let coordinator = TwoPhaseCommitCoordinator()
        let participants = [dbA.make2PCParticipant(tid: txA), dbB.make2PCParticipant(tid: txB)]
        try coordinator.execute(globalTransactionID: "g-commit", participants: participants)

        let rowsA = try dbA.scan("events")
        let rowsB = try dbB.scan("events")
        #expect(rowsA.count == 1)
        #expect(rowsB.count == 1)
        #expect(rowsA.first?.1["node"] == .string("A"))
        #expect(rowsB.first?.1["node"] == .string("B"))
        #expect(dbA.preparedTransactions.isEmpty)
        #expect(dbB.preparedTransactions.isEmpty)
        #expect(dbA.activeTIDs.isEmpty)
        #expect(dbB.activeTIDs.isEmpty)
    }

    @Test func twoPhaseCommitCoordinatorAbortsOnPrepareFailure() throws {
        let root = FileManager.default.temporaryDirectory.appendingPathComponent(UUID().uuidString, isDirectory: true)
        let dir = root.appendingPathComponent("node", isDirectory: true)
        try FileManager.default.createDirectory(at: dir, withIntermediateDirectories: true)
        defer { try? FileManager.default.removeItem(at: root) }

        var config = DBConfig(dataDir: dir.path)
        config.autoCompactionEnabled = false

        let db = Database(config: config)
        try db.createTable("ledger")

        let tx = try db.begin(isolation: .readCommitted)
        _ = try db.insert(into: "ledger", row: ["entry": .string("pending"), "amount": .int(10)], tid: tx)

        let coordinator = TwoPhaseCommitCoordinator()
        let dbParticipant = db.make2PCParticipant(tid: tx)
        let failingParticipant = TwoPhaseCommitParticipant(
            id: "validator",
            prepare: { throw TwoPhaseCommitError.prepareFailed(participant: "validator") },
            commit: {},
            abort: {}
        )

        do {
            try coordinator.execute(globalTransactionID: "g-abort", participants: [dbParticipant, failingParticipant])
            Issue.record("Expected coordinator to throw prepare failure")
        } catch let error as TwoPhaseCommitError {
            #expect(error == .prepareFailed(participant: "validator"))
        }

        let rows = try db.scan("ledger")
        #expect(rows.isEmpty)
        #expect(db.preparedTransactions.isEmpty)
        #expect(db.activeTIDs.isEmpty)
    }
}

