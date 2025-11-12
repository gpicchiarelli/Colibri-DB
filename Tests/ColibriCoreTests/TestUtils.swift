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
        ColibrìDBConfiguration(
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
        [
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
        let deadline = Date().addingTimeInterval(timeout)
        
        while Date() < deadline {
            if condition() {
                return
            }
            try await Task.sleep(nanoseconds: 10_000_000) // 10ms
        }
        
        throw TestError.timeout("Condition not met within \(timeout) seconds")
    }
    
    /// Wait for an async operation with timeout
    public static func waitForAsync<T: Sendable>(
        timeout: TimeInterval = 5.0,
        operation: @Sendable @escaping () async throws -> T
    ) async throws -> T {
        try await withThrowingTaskGroup(of: T.self) { group in
            group.addTask {
                try await operation()
            }
            
            group.addTask {
                try await Task.sleep(nanoseconds: UInt64(timeout * 1_000_000_000))
                throw TestError.timeout("Async operation exceeded \(timeout) seconds")
            }
            
            guard let result = try await group.next() else {
                throw TestError.timeout("Async task group returned no result")
            }
            
            group.cancelAll()
            return result
        }
    }
    
    /// Measure synchronous execution time
    @discardableResult
    public static func measureTime<T>(_ operation: () throws -> T) rethrows -> (result: T, time: TimeInterval) {
        let start = DispatchTime.now()
        let result = try operation()
        let end = DispatchTime.now()
        let elapsed = Double(end.uptimeNanoseconds - start.uptimeNanoseconds) / 1_000_000_000
        return (result, elapsed)
    }
    
    /// Measure asynchronous execution time
    @discardableResult
    public static func measureAsyncTime<T>(_ operation: () async throws -> T) async rethrows -> (result: T, time: TimeInterval) {
        let start = DispatchTime.now()
        let result = try await operation()
        let end = DispatchTime.now()
        let elapsed = Double(end.uptimeNanoseconds - start.uptimeNanoseconds) / 1_000_000_000
        return (result, elapsed)
    }
    
    /// Generate random data for testing
    public static func generateRandomData(size: Int) -> Data {
        var data = Data(count: size)
        let result = data.withUnsafeMutableBytes { bytes in
            SecRandomCopyBytes(kSecRandomDefault, size, bytes.bindMemory(to: UInt8.self).baseAddress!)
        }
        guard result == errSecSuccess else {
            // Fallback to simple random data
            return Data((0..<size).map { _ in UInt8.random(in: 0...255) })
        }
        return data
    }
    
    /// Generate a random alphanumeric string
    public static func generateRandomString(length: Int = 10) -> String {
        let characters = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"
        return String((0..<length).compactMap { _ in characters.randomElement() })
    }
    
    /// Generate a random integer within a range
    public static func generateRandomInt(min: Int = 0, max: Int = 1_000) -> Int {
        Int.random(in: min...max)
    }
    
    /// Generate a random double within a range
    public static func generateRandomDouble(min: Double = 0.0, max: Double = 1.0) -> Double {
        Double.random(in: min...max)
    }
}

/// Test data generator for creating test objects
public struct TestDataGenerator {
    
    /// Generate a test table definition
    public static func generateTableDefinition(name: String = "test_table") -> TableDefinition {
        return TableDefinition(
            name: name,
            columns: [
                ColumnDefinition(name: "id", type: .int, nullable: false),
                ColumnDefinition(name: "name", type: .string, nullable: false),
                ColumnDefinition(name: "age", type: .int, nullable: true),
                ColumnDefinition(name: "salary", type: .double, nullable: true)
            ],
            primaryKey: ["id"]
        )
    }
    
    /// Generate a test row
    public static func generateTestRow(
        id: Int,
        name: String? = nil,
        age: Int? = nil,
        salary: Double? = nil
    ) -> Row {
        var row: Row = [
            "id": .int(Int64(id)),
            "name": .string(name ?? TestUtils.generateRandomString(length: 12))
        ]
        
        row["age"] = age.map { .int(Int64($0)) } ?? .null
        row["salary"] = salary.map { .double($0) } ?? .null
        return row
    }
    
    /// Generate a simple test row
    public static func generateSimpleTestRow(id: Int, name: String) -> Row {
        [
            "id": .int(Int64(id)),
            "name": .string(name)
        ]
    }
    
    /// Generate multiple test rows with deterministic but varied data.
    public static func generateTestRows(count: Int) -> [Row] {
        (1...count).map { index in
            generateTestRow(
                id: index,
                name: "User\(index)",
                age: 18 + (index % 50),
                salary: 30_000 + Double(index * 250)
            )
        }
    }
    
    /// Generate a representative set of SQL statements for parser tests.
    public static func generateSQLStatements() -> [String] {
        [
            "CREATE TABLE users (id INT PRIMARY KEY, name VARCHAR(100), age INT)",
            "INSERT INTO users VALUES (1, 'Alice', 25)",
            "INSERT INTO users VALUES (2, 'Bob', 30)",
            "SELECT * FROM users WHERE age > 25",
            "UPDATE users SET age = 26 WHERE id = 1",
            "DELETE FROM users WHERE age < 30",
            "CREATE INDEX idx_users_age ON users(age)",
            "DROP TABLE users"
        ]
    }
}

/// Test errors
public enum TestError: Error, LocalizedError {
    case timeout(String)
    case assertionFailed(String)
    case setupFailed(String)
    case teardownFailed(String)
    case invalidTestData(String)
    
    public var errorDescription: String? {
        switch self {
        case .timeout(let message):
            return "Test timeout: \(message)"
        case .assertionFailed(let message):
            return "Assertion failed: \(message)"
        case .setupFailed(let message):
            return "Test setup failed: \(message)"
        case .teardownFailed(let message):
            return "Test teardown failed: \(message)"
        case .invalidTestData(let message):
            return "Invalid test data: \(message)"
        }
    }
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
    
    /// Assert that two values are not equal
    public static func assertNotEqual<T: Equatable>(
        _ actual: T,
        _ expected: T,
        _ message: String = "Values should not be equal",
        file: StaticString = #file,
        line: UInt = #line
    ) throws {
        if actual == expected {
            throw TestError.assertionFailed("\(message): values are equal at \(file):\(line)")
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
    
    /// Assert that a value is nil
    public static func assertNil<T>(
        _ value: T?,
        _ message: String = "Value should be nil",
        file: StaticString = #file,
        line: UInt = #line
    ) throws {
        if value != nil {
            throw TestError.assertionFailed("\(message) at \(file):\(line)")
        }
    }
    
    /// Assert that a collection contains a value
    public static func assertContains<C: Collection>(
        _ collection: C,
        _ element: C.Element,
        _ message: String = "Collection should contain element",
        file: StaticString = #file,
        line: UInt = #line
    ) throws where C.Element: Equatable {
        if !collection.contains(element) {
            throw TestError.assertionFailed("\(message) at \(file):\(line)")
        }
    }
    
    /// Assert that a collection does not contain a value
    public static func assertNotContains<C: Collection>(
        _ collection: C,
        _ element: C.Element,
        _ message: String = "Collection should not contain element",
        file: StaticString = #file,
        line: UInt = #line
    ) throws where C.Element: Equatable {
        if collection.contains(element) {
            throw TestError.assertionFailed("\(message) at \(file):\(line)")
        }
    }
    
    /// Assert that an async operation throws an error
    public static func assertAsyncThrows<T>(
        _ operation: () async throws -> T,
        _ message: String = "Operation should throw",
        file: StaticString = #file,
        line: UInt = #line
    ) async throws {
        do {
            _ = try await operation()
            throw TestError.assertionFailed("\(message) at \(file):\(line)")
        } catch {
            // Expected to throw
        }
    }
    
    /// Assert that a synchronous operation throws an error
    public static func assertThrows<T>(
        _ operation: () throws -> T,
        _ message: String = "Operation should throw",
        file: StaticString = #file,
        line: UInt = #line
    ) throws {
        do {
            _ = try operation()
            throw TestError.assertionFailed("\(message) at \(file):\(line)")
        } catch {
            // Expected to throw
        }
    }
}
