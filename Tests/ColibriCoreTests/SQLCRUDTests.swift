//
//  SQLCRUDTests.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-09-27.
//
// Theme: End-to-end CRUD via SQLQueryInterface to simulate a small RDBMS workflow.

import Foundation
@_spi(Experimental) import Testing
@testable import ColibriCore

struct SQLCRUDTests {
    @Test func crudCycleOnUsersAndOrders() throws {
        let tempDir = FileManager.default.temporaryDirectory.appendingPathComponent(UUID().uuidString, isDirectory: true)
        try FileManager.default.createDirectory(at: tempDir, withIntermediateDirectories: true)
        defer { try? FileManager.default.removeItem(at: tempDir) }

        var config = DBConfig(dataDir: tempDir.path)
        config.autoCompactionEnabled = false

        let db = Database(config: config)
        let sql = SQLQueryInterface(database: db)

        // CREATE
        _ = try sql.execute("CREATE TABLE users (id INT PRIMARY KEY, name TEXT, region TEXT)")
        _ = try sql.execute("CREATE TABLE orders (id INT PRIMARY KEY, user_id INT, total DOUBLE)")
        _ = try sql.execute("CREATE INDEX idx_orders_user ON orders (user_id) USING BTree")
        // also create in-memory variants to ensure multi-backend mapping works
        _ = try sql.execute("CREATE INDEX idx_orders_user_hash ON orders (user_id) USING Hash")
        _ = try sql.execute("CREATE INDEX idx_orders_user_art ON orders (user_id) USING ART")

        // INSERT
        _ = try sql.execute("INSERT INTO users (id, name, region) VALUES (1, 'Ada', 'EU')")
        _ = try sql.execute("INSERT INTO users (id, name, region) VALUES (2, 'Bob', 'US')")
        _ = try sql.execute("INSERT INTO orders (id, user_id, total) VALUES (10, 1, 99.5)")
        _ = try sql.execute("INSERT INTO orders (id, user_id, total) VALUES (11, 1, 42.0)")

        // READ
        let r1 = try sql.execute("SELECT * FROM users WHERE region = 'EU'")
        #expect(r1.rows.count == 1)

        // UPDATE (append-only semantics)
        _ = try sql.execute("UPDATE users SET region = 'EMEA' WHERE id = 1")
        let r2 = try sql.execute("SELECT * FROM users WHERE region = 'EMEA'")
        #expect(r2.rows.count >= 1)

        // DELETE
        let d1 = try sql.execute("DELETE FROM orders WHERE id = 11")
        #expect(d1.affectedRows == 1)
        let r3 = try sql.execute("SELECT * FROM orders")
        #expect(r3.rows.count == 1)
        // drop indexes (one existing, one IF EXISTS on non-existing)
        _ = try sql.execute("DROP INDEX idx_orders_user ON orders")
        _ = try sql.execute("DROP INDEX IF EXISTS idx_missing ON orders")

        // Negative: operations on non-registered table should fail
        do {
            _ = try sql.execute("INSERT INTO ghost (id) VALUES (1)")
            Issue.record("Expected failure when inserting into non-registered table")
        } catch {
            // ok
        }
    }
}


