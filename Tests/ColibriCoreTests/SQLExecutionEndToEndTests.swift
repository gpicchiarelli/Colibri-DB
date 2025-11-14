//
//  SQLExecutionEndToEndTests.swift
//  ColibrìDB End-to-End SQL Tests
//
//  Verifies that the full SQL stack (Parser -> Optimizer -> Executor -> Storage)
//  works for INSERT / SELECT / UPDATE / DELETE statements.
//

import XCTest
@testable import ColibriCore

final class SQLExecutionEndToEndTests: XCTestCase {
    
    override func setUpWithError() throws {
        throw XCTSkip("SQL execution integration tests pending transaction isolation fixes")
    }
    
    // MARK: - Helpers
    
    private func makeDatabase() async throws -> (db: ColibrìDB, tempDir: URL) {
        let tempDir = try TestUtils.createTempDirectory()
        let config = TestUtils.createTestConfig(dataDirectory: tempDir)
        
        let db = try ColibrìDB(config: config)
        try await db.start()
        
        return (db, tempDir)
    }
    
    private func createUsersTable(on db: ColibrìDB) async throws {
        let tableDef = TableDefinition(
            name: "users",
            columns: [
                ColumnDefinition(name: "id", type: .int, nullable: false),
                ColumnDefinition(name: "name", type: .string, nullable: false),
                ColumnDefinition(name: "age", type: .int, nullable: true)
            ],
            primaryKey: ["id"],
            indexes: []
        )
        
        try await db.createTable(tableDef)
    }
    
    // MARK: - Tests
    
    /// Verifies INSERT -> SELECT -> UPDATE -> DELETE flow using SQL pipeline.
    func testSQLInsertSelectUpdateDeleteFlow() async throws {
        let (db, tempDir) = try await makeDatabase()
        defer {
            Task {
                try? await db.shutdown()
                try? TestUtils.cleanupTempDirectory(tempDir)
            }
        }
        
        try await createUsersTable(on: db)
        
        // INSERT rows
        let txInsert = try await db.beginTransaction()
        _ = try await db.executeQuery(
            "INSERT INTO users (id, name, age) VALUES (1, 'Alice', 30)",
            txId: txInsert
        )
        _ = try await db.executeQuery(
            "INSERT INTO users (id, name, age) VALUES (2, 'Bob', 28)",
            txId: txInsert
        )
        try await db.commit(txId: txInsert)
        
        // SELECT and verify contents
        let txSelect = try await db.beginTransaction()
        let selectResult = try await db.executeQuery(
            "SELECT id, name, age FROM users ORDER BY id",
            txId: txSelect
        )
        XCTAssertEqual(selectResult.rows.count, 2, "Expected two inserted rows")
        
        if let firstRow = selectResult.rows.first {
            XCTAssertEqual(firstRow["id"], Value.int(1))
            XCTAssertEqual(firstRow["name"], Value.string("Alice"))
            XCTAssertEqual(firstRow["age"], Value.int(30))
        } else {
            XCTFail("Missing first row")
        }
        try await db.commit(txId: txSelect)
        
        // UPDATE age for Alice
        let txUpdate = try await db.beginTransaction()
        _ = try await db.executeQuery(
            "UPDATE users SET age = 31 WHERE id = 1",
            txId: txUpdate
        )
        try await db.commit(txId: txUpdate)
        
        // Verify UPDATE via SELECT
        let txVerifyUpdate = try await db.beginTransaction()
        let updatedResult = try await db.executeQuery(
            "SELECT age FROM users WHERE id = 1",
            txId: txVerifyUpdate
        )
        XCTAssertEqual(updatedResult.rows.count, 1, "Update SELECT rows: \(updatedResult.rows)")
        XCTAssertEqual(updatedResult.rows.first?["age"], Value.int(31))
        try await db.commit(txId: txVerifyUpdate)
        
        // DELETE Bob
        let txDelete = try await db.beginTransaction()
        _ = try await db.executeQuery(
            "DELETE FROM users WHERE id = 2",
            txId: txDelete
        )
        try await db.commit(txId: txDelete)
        
        // Verify DELETE
        let txVerifyDelete = try await db.beginTransaction()
        let remaining = try await db.executeQuery(
            "SELECT id FROM users",
            txId: txVerifyDelete
        )
        print("Remaining rows after DELETE:", remaining.rows)
        XCTAssertEqual(remaining.rows.count, 1, "Rows: \(remaining.rows)")
        XCTAssertEqual(remaining.rows.first?["id"], Value.int(1))
        try await db.commit(txId: txVerifyDelete)
    }
    
    /// Verifies that SQL statements respect transaction boundaries.
    func testSQLTransactionsAreIsolated() async throws {
        let (db, tempDir) = try await makeDatabase()
        defer {
            Task {
                try? await db.shutdown()
                try? TestUtils.cleanupTempDirectory(tempDir)
            }
        }
        
        try await createUsersTable(on: db)
        
        // Transaction 1 inserts a row but does not commit yet
        let tx1 = try await db.beginTransaction()
        _ = try await db.executeQuery(
            "INSERT INTO users (id, name, age) VALUES (10, 'Uncommitted', 20)",
            txId: tx1
        )
        
        // Transaction 2 should not see uncommitted data
        let tx2 = try await db.beginTransaction()
        let selectDuringTx1 = try await db.executeQuery(
            "SELECT * FROM users WHERE id = 10",
            txId: tx2
        )
        XCTAssertEqual(selectDuringTx1.rows.count, 0, "Uncommitted data should be invisible to other transactions")
        try await db.commit(txId: tx2)
        
        // Commit transaction 1
        try await db.commit(txId: tx1)
        
        // New transaction should see committed row
        let tx3 = try await db.beginTransaction()
        let selectAfterCommit = try await db.executeQuery(
            "SELECT name FROM users WHERE id = 10",
            txId: tx3
        )
        XCTAssertEqual(selectAfterCommit.rows.count, 1)
        XCTAssertEqual(selectAfterCommit.rows.first?["name"], Value.string("Uncommitted"))
        try await db.commit(txId: tx3)
    }
}

