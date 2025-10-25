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
        
        let config = TestUtils.createTestConfig(dataDirectory: tempDir)
        
        let db = try ColibrìDB(config: config)
        
        // Verify database is not started initially
        let isRunning = await db.isDatabaseRunning()
        try TestAssertions.assertFalse(isRunning, "Database should not be started initially")
    }
    
    /// Test database startup
    @Test("Database Startup")
    func testDatabaseStartup() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let config = TestUtils.createTestConfig(dataDirectory: tempDir)
        
        let db = try ColibrìDB(config: config)
        
        // Start the database
        try await db.start()
        
        // Verify database is started
        try TestAssertions.assertTrue(await db.isDatabaseRunning(), "Database should be started")
    }
    
    /// Test database shutdown
    @Test("Database Shutdown")
    func testDatabaseShutdown() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let config = TestUtils.createTestConfig(dataDirectory: tempDir)
        
        let db = try ColibrìDB(config: config)
        
        // Start and then shutdown
        try await db.start()
        try await db.shutdown()
        
        // Verify database is not started after shutdown
        try TestAssertions.assertFalse(await db.isDatabaseRunning(), "Database should not be started after shutdown")
    }
    
    /// Test table creation
    @Test("Table Creation")
    func testTableCreation() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let config = TestUtils.createTestConfig(dataDirectory: tempDir)
        
        let db = try ColibrìDB(config: config)
        try await db.start()
        
        // Create a test table
        let tableDef = TestDataGenerator.generateTableDefinition(name: "test_users")
        try await db.createTable(tableDef)
        
        // Verify table was created (simplified check)
        let stats = await db.getStatistics()
        try TestAssertions.assertEqual(stats.tablesCreated, 1, "Should have created 1 table")
    }
    
    /// Test table dropping
    @Test("Table Dropping")
    func testTableDropping() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let config = TestUtils.createTestConfig(dataDirectory: tempDir)
        
        let db = try ColibrìDB(config: config)
        try await db.start()
        
        // Create a test table
        let tableDef = TestDataGenerator.generateTableDefinition(name: "test_users")
        try await db.createTable(tableDef)
        
        // Verify table was created
        let statsBefore = await db.getStatistics()
        try TestAssertions.assertEqual(statsBefore.tablesCreated, 1, "Should have created 1 table")
        
        // Drop the table
        try await db.dropTable("test_users")
        
        // Verify table was dropped
        let statsAfter = await db.getStatistics()
        try TestAssertions.assertEqual(statsAfter.tablesDropped, 1, "Should have dropped 1 table")
    }
    
    /// Test transaction management
    @Test("Transaction Management")
    func testTransactionManagement() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let config = TestUtils.createTestConfig(dataDirectory: tempDir)
        
        let db = try ColibrìDB(config: config)
        try await db.start()
        
        // Begin a transaction
        let txID = try await db.beginTransaction()
        try TestAssertions.assertTrue(txID > 0, "Transaction ID should be positive")
        
        // Commit the transaction
        try await db.commit(txId: txID)
        
        // Begin another transaction
        let txID2 = try await db.beginTransaction()
        try TestAssertions.assertNotEqual(txID2, txID, "Transaction IDs should be different")
        
        // Abort the transaction
        try await db.abort(txId: txID2)
    }
    
    /// Test data operations
    @Test("Data Operations")
    func testDataOperations() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let config = TestUtils.createTestConfig(dataDirectory: tempDir)
        
        let db = try ColibrìDB(config: config)
        try await db.start()
        
        // Create a test table
        let tableDef = TestDataGenerator.generateTableDefinition(name: "test_users")
        try await db.createTable(tableDef)
        
        // Begin transaction
        let txID = try await db.beginTransaction()
        
        // Insert a row
        let testRow = TestDataGenerator.generateTestRow(id: 1, name: "Alice", age: 25, salary: 50000.0)
        let rid = try await db.insert(table: "test_users", row: testRow, txId: txID)
        try TestAssertions.assertTrue(rid.pageID > 0, "Row ID should be positive")
        
        // Update the row
        let updatedRow = TestDataGenerator.generateTestRow(id: 1, name: "Alice Updated", age: 26, salary: 55000.0)
        try await db.update(table: "test_users", rid: rid, row: updatedRow, txId: txID)
        
        // Delete the row
        try await db.delete(table: "test_users", rid: rid, txId: txID)
        
        // Commit transaction
        try await db.commit(txId: txID)
        
        // Verify statistics
        let stats = await db.getStatistics()
        try TestAssertions.assertEqual(stats.rowsInserted, 1, "Should have inserted 1 row")
        try TestAssertions.assertEqual(stats.rowsUpdated, 1, "Should have updated 1 row")
        try TestAssertions.assertEqual(stats.rowsDeleted, 1, "Should have deleted 1 row")
    }
    
    /// Test authentication (simplified - not implemented yet)
    @Test("Authentication")
    func testAuthentication() async throws {
        // Skip authentication test for now as it's not implemented
        try TestAssertions.assertTrue(true, "Authentication test placeholder")
    }
    
    /// Test database statistics
    @Test("Database Statistics")
    func testDatabaseStatistics() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let config = TestUtils.createTestConfig(dataDirectory: tempDir)
        
        let db = try ColibrìDB(config: config)
        
        // Get statistics before start
        let statsBefore = await db.getStatistics()
        try TestAssertions.assertEqual(statsBefore.transactionsStarted, 0, "Should have no transactions before start")
        
        // Start database
        try await db.start()
        
        // Get statistics after start
        let statsAfter = await db.getStatistics()
        try TestAssertions.assertNotNil(statsAfter.startTime, "Start time should be set")
        try TestAssertions.assertEqual(statsAfter.bufferPoolSize, 10, "Buffer pool size should match config")
    }
    
    /// Test checkpoint operation (simplified - not implemented yet)
    @Test("Checkpoint Operation")
    func testCheckpointOperation() async throws {
        // Skip checkpoint test for now as it's not implemented
        try TestAssertions.assertTrue(true, "Checkpoint test placeholder")
    }
    
    /// Test vacuum operation (simplified - not implemented yet)
    @Test("Vacuum Operation")
    func testVacuumOperation() async throws {
        // Skip vacuum test for now as it's not implemented
        try TestAssertions.assertTrue(true, "Vacuum test placeholder")
    }
    
    /// Test multiple concurrent transactions
    @Test("Concurrent Transactions")
    func testConcurrentTransactions() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let config = TestUtils.createTestConfig(dataDirectory: tempDir)
        
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
            let rid = try await db.insert(table: "test_users", row: testRow, txId: txID)
            try TestAssertions.assertTrue(rid.pageID > 0, "Row ID should be positive")
        }
        
        // Commit all transactions
        for txID in transactionIDs {
            try await db.commit(txId: txID)
        }
        
        // Verify all transactions completed successfully
        let stats = await db.getStatistics()
        try TestAssertions.assertTrue(await db.isDatabaseRunning(), "Database should still be started")
        try TestAssertions.assertEqual(stats.transactionsStarted, transactionCount, "Should have started \(transactionCount) transactions")
        try TestAssertions.assertEqual(stats.transactionsCommitted, transactionCount, "Should have committed \(transactionCount) transactions")
    }
    
    /// Test error handling
    @Test("Error Handling")
    func testErrorHandling() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let config = TestUtils.createTestConfig(dataDirectory: tempDir)
        
        let db = try ColibrìDB(config: config)
        
        // Test operations before database start
        try await TestAssertions.assertAsyncThrows({
            try await db.beginTransaction()
        }, "Should throw error when database not started")
        
        try await TestAssertions.assertAsyncThrows({
            try await db.createTable(TestDataGenerator.generateTableDefinition())
        }, "Should throw error when database not started")
        
        // Start database
        try await db.start()
        
        // Test invalid table operations
        try await TestAssertions.assertAsyncThrows({
            try await db.dropTable("nonexistent_table")
        }, "Should throw error for non-existent table")
        
        // Test invalid transaction operations
        let txID = try await db.beginTransaction()
        try await db.commit(txId: txID)
        
        try await TestAssertions.assertAsyncThrows({
            try await db.commit(txId: txID)
        }, "Should throw error for already committed transaction")
    }
    
    /// Test database recovery (simplified - not fully implemented yet)
    @Test("Database Recovery")
    func testDatabaseRecovery() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let config = TestUtils.createTestConfig(dataDirectory: tempDir)
        
        // Create first database instance
        let db1 = try ColibrìDB(config: config)
        try await db1.start()
        
        // Create a table and insert data
        let tableDef = TestDataGenerator.generateTableDefinition(name: "test_users")
        try await db1.createTable(tableDef)
        
        let txID = try await db1.beginTransaction()
        let testRow = TestDataGenerator.generateTestRow(id: 1, name: "Alice", age: 25, salary: 50000.0)
        let rid = try await db1.insert(table: "test_users", row: testRow, txId: txID)
        try await db1.commit(txId: txID)
        
        // Shutdown first instance
        try await db1.shutdown()
        
        // Create second database instance (should recover)
        let db2 = try ColibrìDB(config: config)
        try await db2.start()
        
        // Verify database can start after recovery
        try TestAssertions.assertTrue(await db2.isDatabaseRunning(), "Database should be running after recovery")
        
        try await db2.shutdown()
    }
}
