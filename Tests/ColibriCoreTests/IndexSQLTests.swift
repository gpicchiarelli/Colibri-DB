//
//  IndexSQLTests.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-09-27.
//
//  Theme: Verify SQL DDL for indexes across all backends and basic search semantics.
//

import Foundation
@_spi(Experimental) import Testing
@testable import ColibriCore

struct IndexSQLTests {
    // MARK: - Helpers
    private func newDB() throws -> (Database, SQLQueryInterface, URL) {
        let tempDir = FileManager.default.temporaryDirectory.appendingPathComponent(UUID().uuidString, isDirectory: true)
        try FileManager.default.createDirectory(at: tempDir, withIntermediateDirectories: true)
        var cfg = DBConfig(dataDir: tempDir.path)
        cfg.autoCompactionEnabled = false
        let db = Database(config: cfg)
        let sql = SQLQueryInterface(database: db)
        return (db, sql, tempDir)
    }

    private func bootstrapTable(_ sql: SQLQueryInterface) throws {
        _ = try sql.execute("CREATE TABLE t (id INT PRIMARY KEY, k TEXT, v INT)")
    }

    private func seedRows(_ sql: SQLQueryInterface) throws {
        _ = try sql.execute("INSERT INTO t (id, k, v) VALUES (1, 'a', 10)")
        _ = try sql.execute("INSERT INTO t (id, k, v) VALUES (2, 'b', 20)")
        _ = try sql.execute("INSERT INTO t (id, k, v) VALUES (3, 'b', 30)")
        _ = try sql.execute("INSERT INTO t (id, k, v) VALUES (4, 'c', 40)")
    }

    // MARK: - In-memory indexes
    @Test func hashIndexEqualityAndRangeEdge() throws {
        let (db, sql, dir) = try newDB(); defer { try? FileManager.default.removeItem(at: dir) }
        try bootstrapTable(sql)
        _ = try sql.execute("CREATE INDEX idx_t_k_hash ON t (k) USING Hash")
        try seedRows(sql)

        let eq = try db.indexSearchEqualsTyped(table: "t", index: "idx_t_k_hash", value: .string("b"))
        #expect(eq.count == 2)

        let rngEmpty = try db.indexRangeTyped(table: "t", index: "idx_t_k_hash", lo: .string("a"), hi: .string("c"))
        #expect(rngEmpty.isEmpty) // Hash index does not support range

        let rngEq = try db.indexRangeTyped(table: "t", index: "idx_t_k_hash", lo: .string("b"), hi: .string("b"))
        #expect(rngEq.count == 2)
        _ = try sql.execute("DELETE FROM t WHERE k = 'b'")
        let remaining = try sql.execute("SELECT * FROM t")
        #expect(remaining.rows.count == 2)
    }

    @Test func artIndexEqualityAndRange() throws {
        let (db, sql, dir) = try newDB(); defer { try? FileManager.default.removeItem(at: dir) }
        try bootstrapTable(sql)
        _ = try sql.execute("CREATE INDEX idx_t_k_art ON t (k) USING ART")
        try seedRows(sql)

        let eq = try db.indexSearchEqualsTyped(table: "t", index: "idx_t_k_art", value: .string("b"))
        #expect(eq.count == 2)
        let rng = try db.indexRangeTyped(table: "t", index: "idx_t_k_art", lo: .string("b"), hi: .string("c"))
        #expect(rng.count >= 3) // 'b' x2 and 'c'
    }

    @Test func skipListIndexEqualityAndRange() throws {
        let (db, sql, dir) = try newDB(); defer { try? FileManager.default.removeItem(at: dir) }
        try bootstrapTable(sql)
        _ = try sql.execute("CREATE INDEX idx_t_k_skip ON t (k) USING SkipList")
        try seedRows(sql)

        let eq = try db.indexSearchEqualsTyped(table: "t", index: "idx_t_k_skip", value: .string("a"))
        #expect(eq.count == 1)
        let rng = try db.indexRangeTyped(table: "t", index: "idx_t_k_skip", lo: .string("a"), hi: .string("b"))
        #expect(rng.count >= 3)
    }

    @Test func fractalIndexEqualityAndRange() throws {
        let (db, sql, dir) = try newDB(); defer { try? FileManager.default.removeItem(at: dir) }
        try bootstrapTable(sql)
        _ = try sql.execute("CREATE INDEX idx_t_k_fractal ON t (k) USING Fractal")
        try seedRows(sql)

        let eq = try db.indexSearchEqualsTyped(table: "t", index: "idx_t_k_fractal", value: .string("c"))
        #expect(eq.count == 1)
        let rng = try db.indexRangeTyped(table: "t", index: "idx_t_k_fractal", lo: .string("b"), hi: .string("c"))
        #expect(rng.count >= 3)
    }

    @Test func lsmIndexEqualityAndRange() throws {
        let (db, sql, dir) = try newDB(); defer { try? FileManager.default.removeItem(at: dir) }
        try bootstrapTable(sql)
        _ = try sql.execute("CREATE INDEX idx_t_k_lsm ON t (k) USING LSM")
        try seedRows(sql)

        let eq = try db.indexSearchEqualsTyped(table: "t", index: "idx_t_k_lsm", value: .string("b"))
        #expect(eq.count == 2)
        let rng = try db.indexRangeTyped(table: "t", index: "idx_t_k_lsm", lo: .string("a"), hi: .string("c"))
        #expect(rng.count >= 4)
    }

    // MARK: - Persistent B+Tree
    @Test func persistentBTreeEqualityAndRange() throws {
        let (db, sql, dir) = try newDB()
        defer { 
            try? db.close()
            try? FileManager.default.removeItem(at: dir) 
        }
        try bootstrapTable(sql)
        _ = try sql.execute("CREATE INDEX idx_t_k_btree ON t (k) USING BTree")
        try seedRows(sql)

        let eq = try db.indexSearchEqualsTyped(table: "t", index: "idx_t_k_btree", value: .string("b"))
        #expect(eq.count == 2)
        let rng = try db.indexRangeTyped(table: "t", index: "idx_t_k_btree", lo: .string("b"), hi: .string("c"))
        #expect(rng.count >= 3)

        // Drop and verify removal
        _ = try sql.execute("DROP INDEX idx_t_k_btree ON t")
        do {
            _ = try db.indexSearchEqualsTyped(table: "t", index: "idx_t_k_btree", value: .string("b"))
            Issue.record("Expected notFound for dropped index")
        } catch {
            // ok
        }
    }
}


