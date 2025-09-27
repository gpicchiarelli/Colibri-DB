//
//  PlannerExecutorTests.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// Theme: Planner regression suite validating Volcano operators, optimizer choices, and caching.

import Foundation
@_spi(Experimental) import Testing
@testable import ColibriCore

struct PlannerExecutorTests {
    @Test func executesFilteredScanWithOrderBy() throws {
        let tempDir = FileManager.default.temporaryDirectory.appendingPathComponent(UUID().uuidString, isDirectory: true)
        try FileManager.default.createDirectory(at: tempDir, withIntermediateDirectories: true)
        defer { try? FileManager.default.removeItem(at: tempDir) }

        var config = DBConfig(dataDir: tempDir.path)
        config.autoCompactionEnabled = false

        let db = Database(config: config)
        try db.createTable("users")
        try db.insert(into: "users", row: ["id": .int(1), "name": .string("Ada"), "region": .string("EU")])
        try db.insert(into: "users", row: ["id": .int(2), "name": .string("Bob"), "region": .string("US")])
        try db.insert(into: "users", row: ["id": .int(3), "name": .string("Cleo"), "region": .string("EU")])
        try db.createIndex(name: "idx_users_region", on: "users", columns: ["region"], using: "BTree")

        let predicate = QueryPredicate(column: "region", op: .equals, value: .string("EU"), selectivityHint: 0.2)
        let table = QueryTableRef(name: "users", predicates: [predicate], projection: ["id", "name", "region"])
        let order = SortKey(column: "users.id", ascending: true)
        let request = QueryRequest(root: table, orderBy: [order])

        let rows = try db.executeQuery(request)
        #expect(rows.count == 2)
        let ids = rows.compactMap { row -> Int? in
            if case let .int(value) = row["users.id"] { return Int(value) }
            return nil
        }
        #expect(ids == [1, 3])
    }

    @Test func executesHashJoinWithMaterializedCache() throws {
        let tempDir = FileManager.default.temporaryDirectory.appendingPathComponent(UUID().uuidString, isDirectory: true)
        try FileManager.default.createDirectory(at: tempDir, withIntermediateDirectories: true)
        defer { try? FileManager.default.removeItem(at: tempDir) }

        var config = DBConfig(dataDir: tempDir.path)
        config.autoCompactionEnabled = false

        let db = Database(config: config)
        try db.createTable("users")
        try db.createTable("orders")

        try db.insert(into: "users", row: ["id": .int(1), "name": .string("Ada"), "region": .string("EU")])
        try db.insert(into: "users", row: ["id": .int(2), "name": .string("Bob"), "region": .string("US")])

        try db.insert(into: "orders", row: ["id": .int(10), "user_id": .int(1), "total": .double(99.5)])
        try db.insert(into: "orders", row: ["id": .int(11), "user_id": .int(1), "total": .double(42.0)])
        try db.insert(into: "orders", row: ["id": .int(12), "user_id": .int(2), "total": .double(15.0)])

        try db.createIndex(name: "idx_orders_user", on: "orders", columns: ["user_id"], using: "BTree")

        let userTable = QueryTableRef(name: "users", predicates: [QueryPredicate(column: "region", op: .equals, value: .string("EU"))])
        let ordersTable = QueryTableRef(name: "orders", alias: "o", projection: ["id", "user_id", "total"])
        let join = QueryJoinSpec(table: ordersTable, leftColumns: ["users.id"], rightColumns: ["o.user_id"])
        let order = SortKey(column: "o.total", ascending: false)
        var request = QueryRequest(root: userTable,
                                   joins: [join],
                                   orderBy: [order],
                                   parallelism: 2,
                                   cacheKey: "eu-orders",
                                   useMaterializedCache: true)

        let first = try db.executeQuery(request)
        #expect(first.count == 2)
        let totals = first.compactMap { row -> Double? in
            if case let .double(v) = row["o.total"] { return v }
            return nil
        }
        #expect(totals == [99.5, 42.0])

        // Second call should hit cache and return identical data.
        let second = try db.executeQuery(request)
        #expect(second == first)
        #expect(db.materializedViewCache["eu-orders"]?.count == first.count)

        db.invalidateMaterializedView(key: "eu-orders")
        #expect(db.materializedViewCache["eu-orders"] == nil)
    }
}
