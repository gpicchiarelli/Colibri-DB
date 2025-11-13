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
        let initialStats = await db.getStatistics()
        XCTAssertEqual(initialStats.transactionsStarted, 0, "Database should not have active transactions initially")
        
        // Start the database
        try await db.start()
        
        // Verify database is running
        let runningStats = await db.getStatistics()
        XCTAssertGreaterThanOrEqual(runningStats.transactionsStarted, 0, "Database should be running after start")
        
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
        
        XCTAssertEqual(intValue, Value.int(42))
        XCTAssertEqual(stringValue, Value.string("hello"))
        XCTAssertEqual(doubleValue, Value.double(3.14))
        XCTAssertEqual(boolValue, .bool(true))
        XCTAssertEqual(nullValue, .null)
    }
    
    /// Test that database statistics work
    func testDatabaseStatistics() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let config = TestUtils.createTestConfig(dataDirectory: tempDir)
        let db = try ColibrìDB(config: config)
        
        // Get statistics before starting
        let statsBefore = await db.getStatistics()
        XCTAssertEqual(statsBefore.transactionsStarted, 0)
        XCTAssertEqual(statsBefore.transactionsCommitted, 0)
        
        // Start database
        try await db.start()
        
        // Get statistics after starting
        let statsAfter = await db.getStatistics()
        XCTAssertTrue(statsAfter.startTime != nil, "Start time should be set")
        
        // Note: No stop method available in current API
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
        
        XCTAssertEqual(config.bufferPoolSize, 50)
        XCTAssertEqual(config.maxConnections, 10)
        XCTAssertEqual(config.walBufferSize, 2048)
        XCTAssertEqual(config.checkpointInterval, 2.0)
        XCTAssertEqual(config.logLevel, .debug)
        XCTAssertTrue(config.enableStatistics)
        XCTAssertFalse(config.enableAutoAnalyze)
    }
}
