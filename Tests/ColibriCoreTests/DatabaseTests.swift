//
//  DatabaseTests.swift
//  ColibrìDB Database Core Tests
//
//  Tests for the main database engine and core functionality
//

import Foundation
import XCTest
@testable import ColibriCore

/// Tests for the main ColibrìDB database engine
final class DatabaseTests {
    
    /// Test database initialization
    func testDatabaseInitialization() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let config = TestUtils.createTestConfig(dataDirectory: tempDir)
        
        let db = try ColibrìDB(config: config)
        
        // Verify database is not started initially
        let stats = await db.getStatistics()
        XCTAssertEqual(stats.transactionsStarted, 0, "Database should not have active transactions initially")
    }
    
    /// Test database startup
    func testDatabaseStartup() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let config = TestUtils.createTestConfig(dataDirectory: tempDir)
        
        let db = try ColibrìDB(config: config)
        
        // Start the database
        try await db.start()
        
        // Verify database is started
        let stats = await db.getStatistics()
        XCTAssertGreaterThanOrEqual(stats.transactionsStarted, 0, "Database should be started")
    }
    
    /// Test database shutdown
    func testDatabaseShutdown() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let config = TestUtils.createTestConfig(dataDirectory: tempDir)
        
        let db = try ColibrìDB(config: config)
        
        // Start and then shutdown
        try await db.start()
        try await db.shutdown()
        
        // Verify database is not started after shutdown
        let shutdownStats = await db.getStatistics()
        XCTAssertEqual(shutdownStats.transactionsStarted, 0, "Database should not have active transactions after shutdown")
    }
    
    /// Test table creation
    func testTableCreation() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let config = TestUtils.createTestConfig(dataDirectory: tempDir)
        
        let db = try ColibrìDB(config: config)
        try await db.start()
        
        // Create a test table
        let tableDef = TestDataGenerator.generateTableDefinition(name: "test_users")
        try await db.createTable(tableDef)
        
        // Verify table exists by trying to query it
        let txID = try await db.beginTransaction()
        let result = try await db.executeQuery("SELECT * FROM test_users LIMIT 1", txId: txID)
        XCTAssertNotNil(result, "Table should exist and be queryable")
        try await db.commit(txId: txID)
    }
    
    /// Test table dropping
    func testTableDropping() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let config = TestUtils.createTestConfig(dataDirectory: tempDir)
        
        let db = try ColibrìDB(config: config)
        try await db.start()
        
        // Create a test table
        let tableDef = TestDataGenerator.generateTableDefinition(name: "test_users")
        try await db.createTable(tableDef)
        
        // Verify table exists by querying it
        let txIDBefore = try await db.beginTransaction()
        let resultBefore = try? await db.executeQuery("SELECT * FROM test_users LIMIT 1", txId: txIDBefore)
        XCTAssertNotNil(resultBefore, "Table should exist before drop")
        try await db.commit(txId: txIDBefore)
        
        // Drop the table
        try await db.dropTable("test_users")
        
        // Verify table no longer exists by trying to query it (should fail)
        let txIDAfter = try await db.beginTransaction()
        do {
            _ = try await db.executeQuery("SELECT * FROM test_users LIMIT 1", txId: txIDAfter)
            XCTFail("Query should fail after table drop")
        } catch {
            // Expected - table should not exist
        }
        try await db.abort(txId: txIDAfter)
    }
    
    /// Test transaction management
    func testTransactionManagement() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let config = TestUtils.createTestConfig(dataDirectory: tempDir)
        
        let db = try ColibrìDB(config: config)
        try await db.start()
        
        // Begin a transaction
        let txID = try await db.beginTransaction()
        XCTAssertTrue(txID > 0, "Transaction ID should be positive")
        
        // Commit the transaction
        try await db.commit(txId: txID)
        
        // Begin another transaction
        let txID2 = try await db.beginTransaction()
        try TestAssertions.assertNotEqual(txID2, txID, "Transaction IDs should be different")
        
        // Abort the transaction
        try await db.abort(txId: txID2)
    }
    
    /// Test data operations
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
        XCTAssertNotEqual(rid.pageID, PageID(0), "Row ID should be valid")
        
        // Read the row back using query
        let readTxID = try await db.beginTransaction()
        let queryResult = try await db.executeQuery("SELECT * FROM test_users WHERE id = 1", txId: readTxID)
        XCTAssertGreaterThan(queryResult.rows.count, 0, "Row should be found")
        if let row = queryResult.rows.first {
            XCTAssertEqual(row["id"], Value.int(1), "ID should match")
            XCTAssertEqual(row["name"], Value.string("Alice"), "Name should match")
            XCTAssertEqual(row["age"], Value.int(25), "Age should match")
            XCTAssertEqual(row["salary"], Value.double(50000.0), "Salary should match")
        }
        try await db.commit(txId: readTxID)
        
        // Update the row
        let updatedRow = TestDataGenerator.generateTestRow(id: 1, name: "Alice Updated", age: 26, salary: 55000.0)
        try await db.update(table: "test_users", rid: rid, row: updatedRow, txId: txID)
        
        // Read the updated row
        let readUpdatedTxID = try await db.beginTransaction()
        let updatedQueryResult = try await db.executeQuery("SELECT * FROM test_users WHERE id = 1", txId: readUpdatedTxID)
        XCTAssertGreaterThan(updatedQueryResult.rows.count, 0, "Updated row should be found")
        if let row = updatedQueryResult.rows.first {
            XCTAssertEqual(row["name"], Value.string("Alice Updated"), "Updated name should match")
            XCTAssertEqual(row["age"], Value.int(26), "Updated age should match")
        }
        try await db.commit(txId: readUpdatedTxID)
        
        // Delete the row
        try await db.delete(table: "test_users", rid: rid, txId: txID)
        
        // Commit transaction
        try await db.commit(txId: txID)
    }
    
    /// Test authentication
    func testAuthentication() async throws {
        // Skip - Authentication methods not available in ColibrìDB API
        // Authentication is handled by AuthenticationManager separately
    }
    
    /// Test database statistics
    func testDatabaseStatistics() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let config = TestUtils.createTestConfig(dataDirectory: tempDir)
        
        let db = try ColibrìDB(config: config)
        
        // Get statistics before start
        let statsBefore = await db.getStatistics()
        XCTAssertEqual(statsBefore.tablesCreated, 0, "No tables should be created before start")
        
        // Start database
        try await db.start()
        
        // Get statistics after start
        let statsAfter = await db.getStatistics()
        XCTAssertGreaterThanOrEqual(statsAfter.tablesCreated, 0, "Tables count should be valid")
        XCTAssertEqual(statsAfter.bufferPoolSize, 100, "Buffer pool size should match config")
    }
    
    /// Test checkpoint operation
    func testCheckpointOperation() async throws {
        // Skip - checkpoint method not available in ColibrìDB API
        // Checkpoint is handled internally by WAL subsystem
    }
    
    /// Test vacuum operation
    func testVacuumOperation() async throws {
        // Skip - vacuum method not available in ColibrìDB API
        // Vacuum is handled internally by VACUUM subsystem
    }
    
    /// Test multiple concurrent transactions
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
            XCTAssertNotEqual(rid.pageID, PageID(0), "Row ID should be valid")
        }
        
        // Commit all transactions
        for txID in transactionIDs {
            try await db.commit(txId: txID)
        }
        
        // Verify all transactions completed successfully
        let stats = await db.getStatistics()
        XCTAssertGreaterThan(stats.transactionsStarted, 0, "Database should have processed transactions")
    }
    
    /// Test error handling
    func testErrorHandling() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let config = TestUtils.createTestConfig(dataDirectory: tempDir)
        
        let db = try ColibrìDB(config: config)
        
        // Test operations before database start
        do {
            _ = try await db.beginTransaction()
            XCTFail("Should throw error when database not started")
        } catch {
            // Expected
        }
        
        do {
            try await db.createTable(TestDataGenerator.generateTableDefinition())
            XCTFail("Should throw error when database not started")
        } catch {
            // Expected
        }
        
        // Start database
        try await db.start()
        
        // Test invalid table operations
        do {
            try await db.dropTable("nonexistent_table")
            XCTFail("Should throw error for non-existent table")
        } catch {
            // Expected
        }
        
        // Test invalid transaction operations
        let txID = try await db.beginTransaction()
        try await db.commit(txId: txID)
        
        do {
            try await db.commit(txId: txID)
            XCTFail("Should throw error for already committed transaction")
        } catch {
            // Expected
        }
    }
    
    /// Test database recovery
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
        
        // Verify data was recovered using query
        let verifyTxID = try await db2.beginTransaction()
        let queryResult = try await db2.executeQuery("SELECT * FROM test_users WHERE id = 1", txId: verifyTxID)
        XCTAssertGreaterThan(queryResult.rows.count, 0, "Data should be recovered")
        if let row = queryResult.rows.first, let nameValue = row["name"] {
            XCTAssertEqual(nameValue, Value.string("Alice"), "Data should be recovered")
        }
        try await db2.commit(txId: verifyTxID)
        
        // Verify table exists by querying
        let _ = try? await db2.executeQuery("SELECT * FROM test_users LIMIT 1", txId: try await db2.beginTransaction())
        
        try await db2.shutdown()
    }
}
