//
//  TestUtils.swift
//  ColibrìDB Tests
//
//  Author: ColibrìDB Team
//  Date: 2025-01-27
//

import Foundation
import Testing
@testable import ColibriCore

/// Utility functions for testing
public struct TestUtils {
    
    /// Create a temporary directory for testing
    public static func createTempDirectory() throws -> URL {
        let tempDir = FileManager.default.temporaryDirectory
        let testDir = tempDir.appendingPathComponent("colibridb_test_\(UUID().uuidString)")
        
        try FileManager.default.createDirectory(at: testDir, withIntermediateDirectories: true)
        return testDir
    }
    
    /// Clean up temporary directory
    public static func cleanupTempDirectory(_ url: URL) throws {
        try FileManager.default.removeItem(at: url)
    }
    
    /// Create a test database configuration
    public static func createTestConfig(dataDirectory: URL) -> ColibrìDBConfiguration {
        return ColibrìDBConfiguration(
            dataDirectory: dataDirectory,
            bufferPoolSize: 10,
            maxConnections: 5,
            walBufferSize: 1024,
            checkpointInterval: 1.0,
            logLevel: .debug,
            enableStatistics: false,
            enableAutoAnalyze: false
        )
    }
    
    /// Create test data
    public static func createTestData() -> [[String: Any]] {
        return [
            ["id": 1, "name": "Alice", "age": 30],
            ["id": 2, "name": "Bob", "age": 25],
            ["id": 3, "name": "Charlie", "age": 35]
        ]
    }
    
    /// Wait for a condition to be true
    public static func waitForCondition(
        timeout: TimeInterval = 5.0,
        condition: @escaping () -> Bool
    ) async throws {
        let startTime = Date()
        
        while Date().timeIntervalSince(startTime) < timeout {
            if condition() {
                return
            }
            try await Task.sleep(nanoseconds: 10_000_000) // 10ms
        }
        
        throw TestError.timeout("Condition not met within \(timeout) seconds")
    }
}

/// Test errors
public enum TestError: Error {
    case timeout(String)
    case assertionFailed(String)
    case setupFailed(String)
}

/// Test assertions
public struct TestAssertions {
    
    /// Assert that a condition is true
    public static func assertTrue(
        _ condition: Bool,
        _ message: String = "Assertion failed",
        file: StaticString = #file,
        line: UInt = #line
    ) throws {
        if !condition {
            throw TestError.assertionFailed("\(message) at \(file):\(line)")
        }
    }
    
    /// Assert that a condition is false
    public static func assertFalse(
        _ condition: Bool,
        _ message: String = "Assertion failed",
        file: StaticString = #file,
        line: UInt = #line
    ) throws {
        if condition {
            throw TestError.assertionFailed("\(message) at \(file):\(line)")
        }
    }
    
    /// Assert that two values are equal
    public static func assertEqual<T: Equatable>(
        _ actual: T,
        _ expected: T,
        _ message: String = "Values are not equal",
        file: StaticString = #file,
        line: UInt = #line
    ) throws {
        if actual != expected {
            throw TestError.assertionFailed("\(message): expected \(expected), got \(actual) at \(file):\(line)")
        }
    }
    
    /// Assert that a value is not nil
    public static func assertNotNil<T>(
        _ value: T?,
        _ message: String = "Value is nil",
        file: StaticString = #file,
        line: UInt = #line
    ) throws -> T {
        guard let value = value else {
            throw TestError.assertionFailed("\(message) at \(file):\(line)")
        }
        return value
    }
}
