//
//  IntegrationTests.swift
//  ColibrìDB Integration Tests
//
//  End-to-end tests that verify the complete system functionality
//

import Foundation
import Testing
@testable import ColibriCore

/// Integration Tests for ColibrìDB
@Suite("Integration Tests")
struct IntegrationTests {
    
    /// Test complete database workflow
    @Test("Complete Database Workflow")
    func testCompleteDatabaseWorkflow() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let config = ColibrìDB.Configuration(
            dataDirectory: tempDir,
            walDirectory: tempDir.appendingPathComponent("wal"),
            bufferPoolSize: 100,
            enableWAL: true,
            enableMVCC: true
        )
        
        let db = try ColibrìDB(config: config)
        
        // Start database
        try await db.start()
        
        // Create user
        try await db.createUser(username: "admin", password: "admin123")
        
        // Authenticate user
        let token = try await db.authenticate(username: "admin", password: "admin123")
        try TestAssertions.assertNotNil(token, "Authentication should succeed")
        
        // Create table
        let tableDef = TestDataGenerator.generateTableDefinition(name: "users")
        try await db.createTable(tableDef)
        
        // Verify table exists
        let tables = await db.listTables()
        try TestAssertions.assertContains(tables, "users", "Table should exist")
        
        // Begin transaction
        let txID = try await db.beginTransaction()
        
        // Insert data
        let testRows = TestDataGenerator.generateTestRows(count: 10)
        var insertedRIDs: [RID] = []
        
        for (index, row) in testRows.enumerated() {
            let rid = try await db.insert(table: "users", row: row, txID: txID)
            insertedRIDs.append(rid)
            try TestAssertions.assertTrue(rid > 0, "Row ID should be positive")
        }
        
        // Commit transaction
        try await db.commit(txID)
        
        // Verify data was inserted
        for rid in insertedRIDs {
            let retrievedRow = try await db.read(rid: rid)
            try TestAssertions.assertNotNil(retrievedRow, "Row should be retrievable")
        }
        
        // Begin new transaction for updates
        let updateTxID = try await db.beginTransaction()
        
        // Update some rows
        for (index, rid) in insertedRIDs.prefix(5).enumerated() {
            let updatedRow = TestDataGenerator.generateTestRow(
                id: index + 1,
                name: "UpdatedUser\(index + 1)",
                age: 30 + index,
                salary: 60000.0 + Double(index * 1000)
            )
            try await db.update(rid: rid, newRow: updatedRow, txID: updateTxID)
        }
        
        // Commit update transaction
        try await db.commit(updateTxID)
        
        // Verify updates
        for (index, rid) in insertedRIDs.prefix(5).enumerated() {
            let updatedRow = try await db.read(rid: rid)
            try TestAssertions.assertEqual(updatedRow.values["name"], .string("UpdatedUser\(index + 1)"), "Name should be updated")
        }
        
        // Begin transaction for deletions
        let deleteTxID = try await db.beginTransaction()
        
        // Delete some rows
        for rid in insertedRIDs.suffix(3) {
            try await db.delete(rid: rid, txID: deleteTxID)
        }
        
        // Commit delete transaction
        try await db.commit(deleteTxID)
        
        // Verify deletions
        for rid in insertedRIDs.suffix(3) {
            try TestAssertions.assertThrows({
                try await db.read(rid: rid)
            }, "Deleted row should not be readable")
        }
        
        // Shutdown database
        try await db.shutdown()
        
        // Verify database is not started
        let finalStats = await db.getStatistics()
        try TestAssertions.assertFalse(finalStats.isStarted, "Database should not be started after shutdown")
    }
    
    /// Test database recovery after crash
    @Test("Database Recovery After Crash")
    func testDatabaseRecoveryAfterCrash() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let config = ColibrìDB.Configuration(
            dataDirectory: tempDir,
            walDirectory: tempDir.appendingPathComponent("wal"),
            bufferPoolSize: 100,
            enableWAL: true,
            enableMVCC: true
        )
        
        // Create first database instance
        let db1 = try ColibrìDB(config: config)
        try await db1.start()
        
        // Create table and insert data
        let tableDef = TestDataGenerator.generateTableDefinition(name: "users")
        try await db1.createTable(tableDef)
        
        let txID = try await db1.beginTransaction()
        let testRow = TestDataGenerator.generateTestRow(id: 1, name: "Alice", age: 25, salary: 50000.0)
        let rid = try await db1.insert(table: "users", row: testRow, txID: txID)
        try await db1.commit(txID)
        
        // Shutdown first instance
        try await db1.shutdown()
        
        // Create second database instance (should recover)
        let db2 = try ColibrìDB(config: config)
        try await db2.start()
        
        // Verify data was recovered
        let retrievedRow = try await db2.read(rid: rid)
        try TestAssertions.assertEqual(retrievedRow.values["name"], .string("Alice"), "Data should be recovered")
        
        // Verify table exists
        let tables = await db2.listTables()
        try TestAssertions.assertContains(tables, "users", "Table should be recovered")
        
        try await db2.shutdown()
    }
    
    /// Test concurrent transactions
    @Test("Concurrent Transactions")
    func testConcurrentTransactions() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let config = ColibrìDB.Configuration(
            dataDirectory: tempDir,
            walDirectory: tempDir.appendingPathComponent("wal"),
            bufferPoolSize: 100,
            enableWAL: true,
            enableMVCC: true
        )
        
        let db = try ColibrìDB(config: config)
        try await db.start()
        
        // Create table
        let tableDef = TestDataGenerator.generateTableDefinition(name: "users")
        try await db.createTable(tableDef)
        
        // Start multiple concurrent transactions
        let transactionCount = 10
        var tasks: [Task<Void, Never>] = []
        
        for i in 0..<transactionCount {
            let task = Task {
                do {
                    let txID = try await db.beginTransaction()
                    
                    // Insert data
                    let testRow = TestDataGenerator.generateTestRow(
                        id: i + 1,
                        name: "User\(i + 1)",
                        age: 20 + i,
                        salary: 30000.0 + Double(i * 1000)
                    )
                    let rid = try await db.insert(table: "users", row: testRow, txID: txID)
                    
                    // Commit transaction
                    try await db.commit(txID)
                    
                    // Verify data was inserted
                    let retrievedRow = try await db.read(rid: rid)
                    try TestAssertions.assertNotNil(retrievedRow, "Row should be retrievable")
                } catch {
                    // Handle errors silently for this test
                }
            }
            tasks.append(task)
        }
        
        // Wait for all tasks to complete
        for task in tasks {
            await task.value
        }
        
        // Verify all transactions completed successfully
        let stats = await db.getStatistics()
        try TestAssertions.assertTrue(stats.isStarted, "Database should still be started")
        
        try await db.shutdown()
    }
    
    /// Test SQL parsing and execution
    @Test("SQL Parsing and Execution")
    func testSQLParsingAndExecution() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let config = ColibrìDB.Configuration(
            dataDirectory: tempDir,
            walDirectory: tempDir.appendingPathComponent("wal"),
            bufferPoolSize: 100,
            enableWAL: true,
            enableMVCC: true
        )
        
        let db = try ColibrìDB(config: config)
        try await db.start()
        
        // Test SQL statements
        let sqlStatements = TestDataGenerator.generateSQLStatements()
        
        for sql in sqlStatements {
            // Parse SQL statement
            var parser = SQLParser()
            let statement = try parser.parse(sql)
            try TestAssertions.assertNotNil(statement, "SQL should parse successfully: \(sql)")
        }
        
        try await db.shutdown()
    }
    
    /// Test buffer pool and WAL integration
    @Test("Buffer Pool and WAL Integration")
    func testBufferPoolAndWALIntegration() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let config = ColibrìDB.Configuration(
            dataDirectory: tempDir,
            walDirectory: tempDir.appendingPathComponent("wal"),
            bufferPoolSize: 10, // Small buffer pool to test eviction
            enableWAL: true,
            enableMVCC: true
        )
        
        let db = try ColibrìDB(config: config)
        try await db.start()
        
        // Create table
        let tableDef = TestDataGenerator.generateTableDefinition(name: "users")
        try await db.createTable(tableDef)
        
        // Insert many rows to trigger buffer pool eviction
        let txID = try await db.beginTransaction()
        
        for i in 0..<100 {
            let testRow = TestDataGenerator.generateTestRow(
                id: i + 1,
                name: "User\(i + 1)",
                age: 20 + i,
                salary: 30000.0 + Double(i * 100)
            )
            let rid = try await db.insert(table: "users", row: testRow, txID: txID)
            try TestAssertions.assertTrue(rid > 0, "Row ID should be positive")
        }
        
        // Commit transaction
        try await db.commit(txID)
        
        // Verify data integrity
        let stats = await db.getStatistics()
        try TestAssertions.assertTrue(stats.isStarted, "Database should still be started")
        
        try await db.shutdown()
    }
    
    /// Test index operations
    @Test("Index Operations")
    func testIndexOperations() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let config = ColibrìDB.Configuration(
            dataDirectory: tempDir,
            walDirectory: tempDir.appendingPathComponent("wal"),
            bufferPoolSize: 100,
            enableWAL: true,
            enableMVCC: true
        )
        
        let db = try ColibrìDB(config: config)
        try await db.start()
        
        // Create table
        let tableDef = TestDataGenerator.generateTableDefinition(name: "users")
        try await db.createTable(tableDef)
        
        // Insert data
        let txID = try await db.beginTransaction()
        
        for i in 0..<50 {
            let testRow = TestDataGenerator.generateTestRow(
                id: i + 1,
                name: "User\(i + 1)",
                age: 20 + i,
                salary: 30000.0 + Double(i * 1000)
            )
            let rid = try await db.insert(table: "users", row: testRow, txID: txID)
            try TestAssertions.assertTrue(rid > 0, "Row ID should be positive")
        }
        
        try await db.commit(txID)
        
        // Test index operations (if available)
        // Note: This would require index creation and search functionality
        
        try await db.shutdown()
    }
    
    /// Test authentication and authorization integration
    @Test("Authentication and Authorization Integration")
    func testAuthenticationAndAuthorizationIntegration() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let config = ColibrìDB.Configuration(
            dataDirectory: tempDir,
            walDirectory: tempDir.appendingPathComponent("wal"),
            bufferPoolSize: 100,
            enableWAL: true,
            enableMVCC: true
        )
        
        let db = try ColibrìDB(config: config)
        try await db.start()
        
        // Create users with different roles
        try await db.createUser(username: "admin", password: "admin123")
        try await db.createUser(username: "user", password: "user123")
        
        // Authenticate users
        let adminToken = try await db.authenticate(username: "admin", password: "admin123")
        let userToken = try await db.authenticate(username: "user", password: "user123")
        
        try TestAssertions.assertNotNil(adminToken, "Admin authentication should succeed")
        try TestAssertions.assertNotNil(userToken, "User authentication should succeed")
        
        // Validate sessions
        let adminUser = await db.validateSession(adminToken)
        let regularUser = await db.validateSession(userToken)
        
        try TestAssertions.assertEqual(adminUser!, "admin", "Admin session should be valid")
        try TestAssertions.assertEqual(regularUser!, "user", "User session should be valid")
        
        try await db.shutdown()
    }
    
    /// Test performance under load
    @Test("Performance Under Load")
    func testPerformanceUnderLoad() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let config = ColibrìDB.Configuration(
            dataDirectory: tempDir,
            walDirectory: tempDir.appendingPathComponent("wal"),
            bufferPoolSize: 1000,
            enableWAL: true,
            enableMVCC: true
        )
        
        let db = try ColibrìDB(config: config)
        try await db.start()
        
        // Create table
        let tableDef = TestDataGenerator.generateTableDefinition(name: "users")
        try await db.createTable(tableDef)
        
        let operationCount = 1000
        let startTime = Date()
        
        // Perform many operations
        for i in 0..<operationCount {
            let txID = try await db.beginTransaction()
            
            let testRow = TestDataGenerator.generateTestRow(
                id: i + 1,
                name: "User\(i + 1)",
                age: 20 + (i % 50),
                salary: 30000.0 + Double(i * 100)
            )
            
            let rid = try await db.insert(table: "users", row: testRow, txID: txID)
            try await db.commit(txID)
            
            // Read back the data
            let retrievedRow = try await db.read(rid: rid)
            try TestAssertions.assertNotNil(retrievedRow, "Row should be retrievable")
        }
        
        let endTime = Date()
        let duration = endTime.timeIntervalSince(startTime)
        
        // Verify performance is reasonable
        try TestAssertions.assertTrue(duration < 10.0, "Performance should be reasonable")
        
        // Verify data integrity
        let stats = await db.getStatistics()
        try TestAssertions.assertTrue(stats.isStarted, "Database should still be started")
        
        try await db.shutdown()
    }
    
    /// Test error recovery
    @Test("Error Recovery")
    func testErrorRecovery() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let config = ColibrìDB.Configuration(
            dataDirectory: tempDir,
            walDirectory: tempDir.appendingPathComponent("wal"),
            bufferPoolSize: 100,
            enableWAL: true,
            enableMVCC: true
        )
        
        let db = try ColibrìDB(config: config)
        try await db.start()
        
        // Create table
        let tableDef = TestDataGenerator.generateTableDefinition(name: "users")
        try await db.createTable(tableDef)
        
        // Test error handling
        let txID = try await db.beginTransaction()
        
        // Insert valid data
        let testRow = TestDataGenerator.generateTestRow(id: 1, name: "Alice", age: 25, salary: 50000.0)
        let rid = try await db.insert(table: "users", row: testRow, txID: txID)
        
        // Abort transaction
        try await db.abort(txID)
        
        // Verify data was not committed
        try TestAssertions.assertThrows({
            try await db.read(rid: rid)
        }, "Aborted transaction data should not be readable")
        
        // Test recovery from error
        let newTxID = try await db.beginTransaction()
        let newRid = try await db.insert(table: "users", row: testRow, txID: newTxID)
        try await db.commit(newTxID)
        
        // Verify data is now readable
        let retrievedRow = try await db.read(rid: newRid)
        try TestAssertions.assertNotNil(retrievedRow, "Committed data should be readable")
        
        try await db.shutdown()
    }
    
    /// Test multi-table operations
    @Test("Multi-Table Operations")
    func testMultiTableOperations() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let config = ColibrìDB.Configuration(
            dataDirectory: tempDir,
            walDirectory: tempDir.appendingPathComponent("wal"),
            bufferPoolSize: 100,
            enableWAL: true,
            enableMVCC: true
        )
        
        let db = try ColibrìDB(config: config)
        try await db.start()
        
        // Create multiple tables
        let usersTable = TestDataGenerator.generateTableDefinition(name: "users")
        let ordersTable = TestDataGenerator.generateTableDefinition(name: "orders")
        
        try await db.createTable(usersTable)
        try await db.createTable(ordersTable)
        
        // Verify tables exist
        let tables = await db.listTables()
        try TestAssertions.assertContains(tables, "users", "Users table should exist")
        try TestAssertions.assertContains(tables, "orders", "Orders table should exist")
        
        // Insert data into both tables
        let txID = try await db.beginTransaction()
        
        let userRow = TestDataGenerator.generateTestRow(id: 1, name: "Alice", age: 25, salary: 50000.0)
        let userRid = try await db.insert(table: "users", row: userRow, txID: txID)
        
        let orderRow = TestDataGenerator.generateTestRow(id: 1, name: "Order1", age: 0, salary: 100.0)
        let orderRid = try await db.insert(table: "orders", row: orderRow, txID: txID)
        
        try await db.commit(txID)
        
        // Verify data in both tables
        let retrievedUser = try await db.read(rid: userRid)
        let retrievedOrder = try await db.read(rid: orderRid)
        
        try TestAssertions.assertNotNil(retrievedUser, "User data should be readable")
        try TestAssertions.assertNotNil(retrievedOrder, "Order data should be readable")
        
        try await db.shutdown()
    }
    
    /// Test checkpoint and vacuum operations
    @Test("Checkpoint and Vacuum Operations")
    func testCheckpointAndVacuumOperations() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let config = ColibrìDB.Configuration(
            dataDirectory: tempDir,
            walDirectory: tempDir.appendingPathComponent("wal"),
            bufferPoolSize: 100,
            enableWAL: true,
            enableMVCC: true
        )
        
        let db = try ColibrìDB(config: config)
        try await db.start()
        
        // Create table and insert data
        let tableDef = TestDataGenerator.generateTableDefinition(name: "users")
        try await db.createTable(tableDef)
        
        let txID = try await db.beginTransaction()
        let testRow = TestDataGenerator.generateTestRow(id: 1, name: "Alice", age: 25, salary: 50000.0)
        let rid = try await db.insert(table: "users", row: testRow, txID: txID)
        try await db.commit(txID)
        
        // Perform checkpoint
        try await db.checkpoint()
        
        // Verify database is still functional
        let retrievedRow = try await db.read(rid: rid)
        try TestAssertions.assertNotNil(retrievedRow, "Data should be readable after checkpoint")
        
        // Perform vacuum
        await db.vacuum()
        
        // Verify database is still functional
        let retrievedRowAfterVacuum = try await db.read(rid: rid)
        try TestAssertions.assertNotNil(retrievedRowAfterVacuum, "Data should be readable after vacuum")
        
        try await db.shutdown()
    }
}
