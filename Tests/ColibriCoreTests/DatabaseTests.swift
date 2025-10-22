//
//  DatabaseTests.swift
//  ColibrìDB Database Core Tests
//
//  Tests for the main database engine and core functionality
//

import Foundation
import Testing
@testable import ColibriCore

/// Tests for the main ColibrìDB database engine
@Suite("Database Core Tests")
struct DatabaseTests {
    
    /// Test database initialization
    @Test("Database Initialization")
    func testDatabaseInitialization() async throws {
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
        
        // Verify database is not started initially
        let stats = await db.getStatistics()
        try TestAssertions.assertFalse(stats.isStarted, "Database should not be started initially")
    }
    
    /// Test database startup
    @Test("Database Startup")
    func testDatabaseStartup() async throws {
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
        
        // Start the database
        try await db.start()
        
        // Verify database is started
        let stats = await db.getStatistics()
        try TestAssertions.assertTrue(stats.isStarted, "Database should be started")
    }
    
    /// Test database shutdown
    @Test("Database Shutdown")
    func testDatabaseShutdown() async throws {
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
        
        // Start and then shutdown
        try await db.start()
        try await db.shutdown()
        
        // Verify database is not started after shutdown
        let stats = await db.getStatistics()
        try TestAssertions.assertFalse(stats.isStarted, "Database should not be started after shutdown")
    }
    
    /// Test table creation
    @Test("Table Creation")
    func testTableCreation() async throws {
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
        
        // Create a test table
        let tableDef = TestDataGenerator.generateTableDefinition(name: "test_users")
        try await db.createTable(tableDef)
        
        // Verify table exists
        let retrievedTable = await db.getTable("test_users")
        try TestAssertions.assertNotNil(retrievedTable, "Table should exist after creation")
        try TestAssertions.assertEqual(retrievedTable!.name, "test_users", "Table name should match")
        
        // Verify table is in list
        let tables = await db.listTables()
        try TestAssertions.assertContains(tables, "test_users", "Table should be in list")
    }
    
    /// Test table dropping
    @Test("Table Dropping")
    func testTableDropping() async throws {
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
        
        // Create a test table
        let tableDef = TestDataGenerator.generateTableDefinition(name: "test_users")
        try await db.createTable(tableDef)
        
        // Verify table exists
        let tablesBefore = await db.listTables()
        try TestAssertions.assertContains(tablesBefore, "test_users", "Table should exist before drop")
        
        // Drop the table
        try await db.dropTable("test_users")
        
        // Verify table no longer exists
        let tablesAfter = await db.listTables()
        try TestAssertions.assertNotContains(tablesAfter, "test_users", "Table should not exist after drop")
        
        let retrievedTable = await db.getTable("test_users")
        try TestAssertions.assertNil(retrievedTable, "Table should be nil after drop")
    }
    
    /// Test transaction management
    @Test("Transaction Management")
    func testTransactionManagement() async throws {
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
        
        // Begin a transaction
        let txID = try await db.beginTransaction(isolationLevel: .repeatableRead)
        try TestAssertions.assertTrue(txID > 0, "Transaction ID should be positive")
        
        // Commit the transaction
        try await db.commit(txID)
        
        // Begin another transaction
        let txID2 = try await db.beginTransaction(isolationLevel: .readCommitted)
        try TestAssertions.assertNotEqual(txID2, txID, "Transaction IDs should be different")
        
        // Abort the transaction
        try await db.abort(txID2)
    }
    
    /// Test data operations
    @Test("Data Operations")
    func testDataOperations() async throws {
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
        
        // Create a test table
        let tableDef = TestDataGenerator.generateTableDefinition(name: "test_users")
        try await db.createTable(tableDef)
        
        // Begin transaction
        let txID = try await db.beginTransaction()
        
        // Insert a row
        let testRow = TestDataGenerator.generateTestRow(id: 1, name: "Alice", age: 25, salary: 50000.0)
        let rid = try await db.insert(table: "test_users", row: testRow, txID: txID)
        try TestAssertions.assertTrue(rid > 0, "Row ID should be positive")
        
        // Read the row back
        let retrievedRow = try await db.read(rid: rid)
        try TestAssertions.assertEqual(retrievedRow.values["id"], .int(1), "ID should match")
        try TestAssertions.assertEqual(retrievedRow.values["name"], .string("Alice"), "Name should match")
        try TestAssertions.assertEqual(retrievedRow.values["age"], .int(25), "Age should match")
        try TestAssertions.assertEqual(retrievedRow.values["salary"], .double(50000.0), "Salary should match")
        
        // Update the row
        let updatedRow = TestDataGenerator.generateTestRow(id: 1, name: "Alice Updated", age: 26, salary: 55000.0)
        try await db.update(rid: rid, newRow: updatedRow, txID: txID)
        
        // Read the updated row
        let retrievedUpdatedRow = try await db.read(rid: rid)
        try TestAssertions.assertEqual(retrievedUpdatedRow.values["name"], .string("Alice Updated"), "Updated name should match")
        try TestAssertions.assertEqual(retrievedUpdatedRow.values["age"], .int(26), "Updated age should match")
        
        // Delete the row
        try await db.delete(rid: rid, txID: txID)
        
        // Commit transaction
        try await db.commit(txID)
    }
    
    /// Test authentication
    @Test("Authentication")
    func testAuthentication() async throws {
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
        
        // Create a user
        try await db.createUser(username: "testuser", password: "testpass")
        
        // Authenticate the user
        let token = try await db.authenticate(username: "testuser", password: "testpass")
        try TestAssertions.assertNotNil(token, "Authentication token should not be nil")
        
        // Validate the session
        let validatedUser = await db.validateSession(token)
        try TestAssertions.assertNotNil(validatedUser, "Session should be valid")
        try TestAssertions.assertEqual(validatedUser!, "testuser", "Validated user should match")
        
        // Test invalid authentication
        try TestAssertions.assertAsyncThrows({
            try await db.authenticate(username: "testuser", password: "wrongpass")
        }, "Invalid password should throw")
    }
    
    /// Test database statistics
    @Test("Database Statistics")
    func testDatabaseStatistics() async throws {
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
        
        // Get statistics before start
        let statsBefore = await db.getStatistics()
        try TestAssertions.assertFalse(statsBefore.isStarted, "Database should not be started")
        
        // Start database
        try await db.start()
        
        // Get statistics after start
        let statsAfter = await db.getStatistics()
        try TestAssertions.assertTrue(statsAfter.isStarted, "Database should be started")
        try TestAssertions.assertEqual(statsAfter.bufferPoolSize, 100, "Buffer pool size should match config")
        try TestAssertions.assertTrue(statsAfter.currentLSN >= 0, "Current LSN should be non-negative")
    }
    
    /// Test checkpoint operation
    @Test("Checkpoint Operation")
    func testCheckpointOperation() async throws {
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
        
        // Perform checkpoint
        try await db.checkpoint()
        
        // Verify checkpoint completed without error
        let stats = await db.getStatistics()
        try TestAssertions.assertTrue(stats.isStarted, "Database should still be started after checkpoint")
    }
    
    /// Test vacuum operation
    @Test("Vacuum Operation")
    func testVacuumOperation() async throws {
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
        
        // Perform vacuum
        await db.vacuum()
        
        // Verify vacuum completed without error
        let stats = await db.getStatistics()
        try TestAssertions.assertTrue(stats.isStarted, "Database should still be started after vacuum")
    }
    
    /// Test multiple concurrent transactions
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
        
        // Create a test table
        let tableDef = TestDataGenerator.generateTableDefinition(name: "test_users")
        try await db.createTable(tableDef)
        
        // Start multiple concurrent transactions
        let transactionCount = 10
        var transactionIDs: [TxID] = []
        
        for i in 0..<transactionCount {
            let txID = try await db.beginTransaction()
            transactionIDs.append(txID)
            
            // Insert a row in each transaction
            let testRow = TestDataGenerator.generateTestRow(id: i + 1, name: "User\(i + 1)", age: 20 + i, salary: 30000.0 + Double(i * 1000))
            let rid = try await db.insert(table: "test_users", row: testRow, txID: txID)
            try TestAssertions.assertTrue(rid > 0, "Row ID should be positive")
        }
        
        // Commit all transactions
        for txID in transactionIDs {
            try await db.commit(txID)
        }
        
        // Verify all transactions completed successfully
        let stats = await db.getStatistics()
        try TestAssertions.assertTrue(stats.isStarted, "Database should still be started")
    }
    
    /// Test error handling
    @Test("Error Handling")
    func testErrorHandling() async throws {
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
        
        // Test operations before database start
        try TestAssertions.assertAsyncThrows({
            try await db.beginTransaction()
        }, "Should throw error when database not started")
        
        try TestAssertions.assertAsyncThrows({
            try await db.createTable(TestDataGenerator.generateTableDefinition())
        }, "Should throw error when database not started")
        
        // Start database
        try await db.start()
        
        // Test invalid table operations
        try TestAssertions.assertAsyncThrows({
            try await db.dropTable("nonexistent_table")
        }, "Should throw error for non-existent table")
        
        // Test invalid transaction operations
        let txID = try await db.beginTransaction()
        try await db.commit(txID)
        
        try TestAssertions.assertAsyncThrows({
            try await db.commit(txID)
        }, "Should throw error for already committed transaction")
    }
    
    /// Test database recovery
    @Test("Database Recovery")
    func testDatabaseRecovery() async throws {
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
        
        // Create a table and insert data
        let tableDef = TestDataGenerator.generateTableDefinition(name: "test_users")
        try await db1.createTable(tableDef)
        
        let txID = try await db1.beginTransaction()
        let testRow = TestDataGenerator.generateTestRow(id: 1, name: "Alice", age: 25, salary: 50000.0)
        let rid = try await db1.insert(table: "test_users", row: testRow, txID: txID)
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
        try TestAssertions.assertContains(tables, "test_users", "Table should be recovered")
        
        try await db2.shutdown()
    }
}
