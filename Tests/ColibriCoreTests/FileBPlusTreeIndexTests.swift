//
//  FileBPlusTreeIndexTests.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//

// Theme: B+Tree chronicles covering inserts, splits, and deletes.

import Foundation
@_spi(Experimental) import Testing
@testable import ColibriCore

@Suite(.serialized)
struct FileBPlusTreeIndexTests {
    @Test func insertAndSearchEquality() throws {
        let tempDir = FileManager.default.temporaryDirectory.appendingPathComponent(UUID().uuidString, isDirectory: true)
        try FileManager.default.createDirectory(at: tempDir, withIntermediateDirectories: true)
        defer { try? FileManager.default.removeItem(at: tempDir) }
        let indexPath = tempDir.appendingPathComponent("test_index.bt").path

        let index = try FileBPlusTreeIndex(path: indexPath, pageSize: 4096, capacityPages: 32)
        let rid = RID(pageId: 1, slotId: 1)
        try index.insert(key: Value.int(42), rid: rid)

        let matches = index.searchEquals(Value.int(42))
        #expect(matches == [rid])
        #expect(index.searchEquals(Value.int(7)).isEmpty)
    }

    @Test func systemCatalogRegistersTable() throws {
        let tempDir = FileManager.default.temporaryDirectory.appendingPathComponent(UUID().uuidString, isDirectory: true)
        try FileManager.default.createDirectory(at: tempDir, withIntermediateDirectories: true)
        defer { try? FileManager.default.removeItem(at: tempDir) }
        let catalogPath = tempDir.appendingPathComponent("system_catalog.json").path

        let catalog = try SystemCatalog(path: catalogPath)
        let logical = catalog.registerTable(name: "users", schema: "public", storage: "FileHeap", physicalPath: nil, pageSize: 8192, inMemory: false)
        #expect(logical.name == "users")
        #expect(catalog.logicalObjects(kind: SystemCatalog.LogicalKind.table).count == 1)
        #expect(catalog.physicalObjects(kind: nil as SystemCatalog.PhysicalKind?).isEmpty)
    }

    @Test func rolesConfigurationsAndStatistics() throws {
        let tempDir = FileManager.default.temporaryDirectory.appendingPathComponent(UUID().uuidString, isDirectory: true)
        try FileManager.default.createDirectory(at: tempDir, withIntermediateDirectories: true)
        defer { try? FileManager.default.removeItem(at: tempDir) }
        let catalogPath = tempDir.appendingPathComponent("system_catalog.json").path

        let catalog = try SystemCatalog(path: catalogPath)
        let role = catalog.registerRole(name: "analyst", kind: .user, members: ["alice"], privileges: ["SELECT"], metadata: ["scope": "reporting"])
        catalog.addRoleMembership(name: "analyst", kind: .user, member: "bob")
        catalog.setRolePrivileges(name: "analyst", kind: .user, privileges: ["SELECT", "ANALYZE"])
        let roles = catalog.roles(kind: .user)
        #expect(roles.first?.members.contains("bob") == true)
        #expect(roles.first?.privileges.contains("ANALYZE") == true)

        let stat = catalog.registerStatistic(table: "orders", column: "customer_id", stats: ["distinctCount": 42], metadata: ["sampledRows": "100"])
        #expect(stat.table == "orders")
        #expect(catalog.statistics(table: "orders", column: "customer_id").first?.stats["distinctCount"] == 42)

        catalog.registerConfiguration(scope: "global", key: "storageEngine", value: "FileHeap")
        #expect(catalog.configurations(scope: "global", key: "storageEngine").first?.value == "FileHeap")

        catalog.registerStructurePreference(table: "orders", columns: ["customer_id"], structure: "lsm")
        #expect(catalog.structurePreferences(table: "orders").first?.structure == "lsm")
        #expect(role.metadata["scope"] == "reporting")
    }

    @Test func bPlusTreeSplitAndRangeValidated() throws {
        let (index, tempDir) = try makeIndexFixture(pageSize: 192)
        defer { index.close(); try? FileManager.default.removeItem(at: tempDir) }

        var ridByKey: [Int: RID] = [:]
        var keyByRid: [RID: Int] = [:]
        for key in 0..<64 {
            let rid = RID(pageId: UInt64(key + 1), slotId: 1)
            ridByKey[key] = rid
            keyByRid[rid] = key
            try index.insert(key: .int(Int64(key)), rid: rid)
        }

        let report = index.validateDeep()
        #expect(report.ok)
        #expect(report.leaves > 1)
        #expect(report.internalNodes >= 1)

        let rids = index.range(nil, nil)
        #expect(Set(rids) == Set(keyByRid.keys))
        let keys = rids.compactMap { keyByRid[$0] }
        #expect(keys.count == 64)
        #expect(Set(keys) == Set(0..<64))
    }

    @Test func bPlusTreeDeleteBorrowProbe() throws {
        let (index, tempDir) = try makeIndexFixture(pageSize: 256)
        defer { index.close(); try? FileManager.default.removeItem(at: tempDir) }

        var ridByKey: [Int: RID] = [:]
        for key in 0..<48 {
            let rid = RID(pageId: UInt64(key + 1), slotId: 1)
            ridByKey[key] = rid
            try index.insert(key: .int(Int64(key)), rid: rid)
        }

        let baseline = index.validateDeep()
        #expect(baseline.ok)

        var lastKeyChecked: Int = -1
        var problematicReport: FileBPlusTreeIndex.DeepReport?
        for key in 0..<48 {
            guard let rid = ridByKey[key] else { continue }
            try index.remove(key: .int(Int64(key)), rid: rid)
            lastKeyChecked = key
            let report = index.validateDeep()
            if !report.ok {
                problematicReport = report
                break
            }
        }

        #expect(problematicReport == nil, "validateDeep failed after deleting key \(lastKeyChecked): \(String(describing: problematicReport?.messages))")
    }

    @Test func bPlusTreeDeleteLeftMergeCollapse() throws {
        let (index, tempDir) = try makeIndexFixture(pageSize: 192)
        defer { index.close(); try? FileManager.default.removeItem(at: tempDir) }

        var ridByKey: [Int: RID] = [:]
        var keyByRid: [RID: Int] = [:]
        for key in 0..<60 {
            let rid = RID(pageId: UInt64(key + 1), slotId: 1)
            ridByKey[key] = rid
            keyByRid[rid] = key
            try index.insert(key: .int(Int64(key)), rid: rid)
        }

        let baseline = index.validateDeep()
        #expect(baseline.ok)
        #expect(baseline.internalNodes > 0)

        for key in stride(from: 59, through: 2, by: -1) {
            guard let rid = ridByKey.removeValue(forKey: key) else { continue }
            keyByRid.removeValue(forKey: rid)
            try index.remove(key: .int(Int64(key)), rid: rid)
            let report = index.validateDeep()
            #expect(report.ok, "validateDeep failed after deleting key \(key): \(report.messages)")
        }

        let finalReport = index.validateDeep()
        #expect(finalReport.ok)

        let remaining = index.range(nil, nil)
        #expect(remaining.count == 2)
        let remainingKeys = remaining.compactMap { keyByRid[$0] }
        #expect(Set(remainingKeys) == Set([0, 1]))
    }
}

private func makeIndexFixture(pageSize: Int) throws -> (FileBPlusTreeIndex, URL) {
    let tempDir = FileManager.default.temporaryDirectory.appendingPathComponent(UUID().uuidString, isDirectory: true)
    try FileManager.default.createDirectory(at: tempDir, withIntermediateDirectories: true)
    let indexPath = tempDir.appendingPathComponent("fixture.bt").path
    let index = try FileBPlusTreeIndex(path: indexPath, pageSize: pageSize, capacityPages: 32)
    return (index, tempDir)
}

