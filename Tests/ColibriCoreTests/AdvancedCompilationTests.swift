//
//  AdvancedCompilationTests.swift
//  ColibrìDB Tests
//
//  Author: ColibrìDB Team
//  Date: 2025-01-27
//

import XCTest
@testable import ColibriCore

/// Advanced compilation tests to verify core functionality works
final class AdvancedCompilationTests: XCTestCase {
    
    /// Test that database can be created and started
    func testDatabaseCreationAndStartup() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let config = TestUtils.createTestConfig(dataDirectory: tempDir)
        let db = try ColibrìDB(config: config)
        
        // Verify database is not running initially
        try TestAssertions.assertFalse(await db.isDatabaseRunning(), "Database should not be running initially")
        
        // Start the database
        try await db.start()
        
        // Verify database is running
        try TestAssertions.assertTrue(await db.isDatabaseRunning(), "Database should be running after start")
        
        // Note: No stop method available in current API
    }
    
    /// Test that logging functions work correctly
    func testLoggingFunctions() throws {
        // These should not crash
        logInfo("Test info message", category: .general)
        logDebug("Test debug message", category: .general)
        logWarning("Test warning message", category: .general)
        logError("Test error message", category: .general)
        
        // Test with metadata
        let metadata = ["key1": "value1", "key2": "value2"]
        logInfo("Test with metadata", category: .general, metadata: metadata)
    }
    
    /// Test that basic types work correctly
    func testBasicTypes() throws {
        // Test Value types
        let intValue = Value.int(42)
        let stringValue = Value.string("hello")
        let doubleValue = Value.double(3.14)
        let boolValue = Value.bool(true)
        let nullValue = Value.null
        
        try TestAssertions.assertEqual(intValue, .int(42))
        try TestAssertions.assertEqual(stringValue, .string("hello"))
        try TestAssertions.assertEqual(doubleValue, .double(3.14))
        try TestAssertions.assertEqual(boolValue, .bool(true))
        try TestAssertions.assertEqual(nullValue, .null)
    }
    
    /// Test that database statistics work
    func testDatabaseStatistics() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let config = TestUtils.createTestConfig(dataDirectory: tempDir)
        let db = try ColibrìDB(config: config)
        
        // Get statistics before starting
        let statsBefore = await db.getStatistics()
        try TestAssertions.assertEqual(statsBefore.transactionsStarted, 0, "Should have no transactions before start")
        try TestAssertions.assertEqual(statsBefore.transactionsCommitted, 0, "Should have no committed transactions before start")
        
        // Start database
        try await db.start()
        
        // Get statistics after starting
        let statsAfter = await db.getStatistics()
        try TestAssertions.assertNotNil(statsAfter.startTime, "Start time should be set")
        
        // Shutdown database
        try await db.shutdown()
    }
    
    /// Test that configuration works correctly
    func testConfiguration() throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let config = ColibrìDBConfiguration(
            dataDirectory: tempDir,
            bufferPoolSize: 50,
            maxConnections: 10,
            walBufferSize: 2048,
            checkpointInterval: 2.0,
            logLevel: .debug,
            enableStatistics: true,
            enableAutoAnalyze: false
        )
        
        try TestAssertions.assertEqual(config.bufferPoolSize, 50)
        try TestAssertions.assertEqual(config.maxConnections, 10)
        try TestAssertions.assertEqual(config.walBufferSize, 2048)
        try TestAssertions.assertEqual(config.checkpointInterval, 2.0)
        try TestAssertions.assertEqual(config.logLevel, .debug)
        try TestAssertions.assertTrue(config.enableStatistics)
        try TestAssertions.assertFalse(config.enableAutoAnalyze)
    }
}
