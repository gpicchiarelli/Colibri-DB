//
//  TestStructure.swift
//  ColibrìDB Test Suite Structure
//
//  This file defines the overall test structure and common utilities
//  for the ColibrìDB test suite.
//

import Foundation
import Testing

/// Test categories for organizing tests
public enum TestCategory: String, CaseIterable {
    case unit = "Unit Tests"
    case integration = "Integration Tests"
    case performance = "Performance Tests"
    case stress = "Stress Tests"
    case concurrency = "Concurrency Tests"
    case recovery = "Recovery Tests"
    case distributed = "Distributed Tests"
    case security = "Security Tests"
    case invariants = "Invariant Tests"
}

/// Test utilities and helpers
public struct TestUtils {
    
    /// Create a temporary directory for test data
    public static func createTempDirectory() throws -> URL {
        let tempDir = FileManager.default.temporaryDirectory
        let testDir = tempDir.appendingPathComponent("ColibriDBTests_\(UUID().uuidString)")
        try FileManager.default.createDirectory(at: testDir, withIntermediateDirectories: true)
        return testDir
    }
    
    /// Clean up temporary directory
    public static func cleanupTempDirectory(_ url: URL) throws {
        try FileManager.default.removeItem(at: url)
    }
    
    /// Generate random test data
    public static func generateRandomData(size: Int = 1024) -> Data {
        var data = Data(count: size)
        let result = data.withUnsafeMutableBytes { bytes in
            SecRandomCopyBytes(kSecRandomDefault, size, bytes.bindMemory(to: UInt8.self).baseAddress!)
        }
        guard result == errSecSuccess else {
            fatalError("Failed to generate random data")
        }
        return data
    }
    
    /// Generate random string
    public static func generateRandomString(length: Int = 10) -> String {
        let characters = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"
        return String((0..<length).map { _ in characters.randomElement()! })
    }
    
    /// Generate random integer in range
    public static func generateRandomInt(min: Int = 0, max: Int = 1000) -> Int {
        return Int.random(in: min...max)
    }
    
    /// Generate random double in range
    public static func generateRandomDouble(min: Double = 0.0, max: Double = 1.0) -> Double {
        return Double.random(in: min...max)
    }
    
    /// Wait for async operation with timeout
    public static func waitForAsync<T>(
        timeout: TimeInterval = 5.0,
        operation: @escaping () async throws -> T
    ) async throws -> T {
        return try await withThrowingTaskGroup(of: T.self) { group in
            group.addTask {
                try await operation()
            }
            
            group.addTask {
                try await Task.sleep(nanoseconds: UInt64(timeout * 1_000_000_000))
                throw TestError.timeout
            }
            
            let result = try await group.next()!
            group.cancelAll()
            return result
        }
    }
    
    /// Measure execution time
    public static func measureTime<T>(_ operation: () throws -> T) rethrows -> (result: T, time: TimeInterval) {
        let startTime = Date()
        let result = try operation()
        let endTime = Date()
        return (result, endTime.timeIntervalSince(startTime))
    }
    
    /// Measure async execution time
    public static func measureAsyncTime<T>(_ operation: () async throws -> T) async rethrows -> (result: T, time: TimeInterval) {
        let startTime = Date()
        let result = try await operation()
        let endTime = Date()
        return (result, endTime.timeIntervalSince(startTime))
    }
}

/// Test errors
public enum TestError: Error, LocalizedError {
    case timeout
    case assertionFailed(String)
    case setupFailed(String)
    case teardownFailed(String)
    case invalidTestData(String)
    
    public var errorDescription: String? {
        switch self {
        case .timeout:
            return "Test operation timed out"
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

/// Base test class with common setup/teardown
@MainActor
public class BaseTest {
    var tempDirectory: URL?
    
    public func setUp() async throws {
        tempDirectory = try TestUtils.createTempDirectory()
    }
    
    public func tearDown() async throws {
        if let tempDir = tempDirectory {
            try TestUtils.cleanupTempDirectory(tempDir)
            tempDirectory = nil
        }
    }
}

/// Performance test base class
@MainActor
public class PerformanceTest: BaseTest {
    var performanceMetrics: [String: TimeInterval] = [:]
    
    public func recordMetric(_ name: String, time: TimeInterval) {
        performanceMetrics[name] = time
    }
    
    public func getMetric(_ name: String) -> TimeInterval? {
        return performanceMetrics[name]
    }
    
    public func getAllMetrics() -> [String: TimeInterval] {
        return performanceMetrics
    }
}

/// Concurrency test base class
@MainActor
public class ConcurrencyTest: BaseTest {
    var concurrentTasks: [Task<Void, Never>] = []
    
    public func addConcurrentTask(_ task: @escaping () async -> Void) {
        let task = Task {
            await task()
        }
        concurrentTasks.append(task)
    }
    
    public func waitForAllTasks() async {
        for task in concurrentTasks {
            await task.value
        }
        concurrentTasks.removeAll()
    }
    
    public func cancelAllTasks() {
        for task in concurrentTasks {
            task.cancel()
        }
        concurrentTasks.removeAll()
    }
}

/// Test data generators
public struct TestDataGenerator {
    
    /// Generate test table definition
    public static func generateTableDefinition(name: String = "test_table") -> TableDefinition {
        return TableDefinition(
            name: name,
            columns: [
                ColumnDefinition(name: "id", type: .integer, isPrimaryKey: true, isNullable: false),
                ColumnDefinition(name: "name", type: .string, isPrimaryKey: false, isNullable: false),
                ColumnDefinition(name: "age", type: .integer, isPrimaryKey: false, isNullable: true),
                ColumnDefinition(name: "salary", type: .double, isPrimaryKey: false, isNullable: true)
            ]
        )
    }
    
    /// Generate test row data
    public static func generateTestRow(id: Int, name: String? = nil, age: Int? = nil, salary: Double? = nil) -> Row {
        return Row(values: [
            "id": .int(id),
            "name": .string(name ?? TestUtils.generateRandomString()),
            "age": age.map { .int($0) } ?? .null,
            "salary": salary.map { .double($0) } ?? .null
        ])
    }
    
    /// Generate multiple test rows
    public static func generateTestRows(count: Int) -> [Row] {
        return (1...count).map { id in
            generateTestRow(
                id: id,
                name: "User\(id)",
                age: TestUtils.generateRandomInt(min: 18, max: 65),
                salary: TestUtils.generateRandomDouble(min: 30000, max: 150000)
            )
        }
    }
    
    /// Generate test SQL statements
    public static func generateSQLStatements() -> [String] {
        return [
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

/// Test assertions
public struct TestAssertions {
    
    /// Assert that a condition is true
    public static func assertTrue(_ condition: Bool, _ message: String = "Expected true") throws {
        if !condition {
            throw TestError.assertionFailed(message)
        }
    }
    
    /// Assert that a condition is false
    public static func assertFalse(_ condition: Bool, _ message: String = "Expected false") throws {
        if condition {
            throw TestError.assertionFailed(message)
        }
    }
    
    /// Assert that two values are equal
    public static func assertEqual<T: Equatable>(_ actual: T, _ expected: T, _ message: String = "Values not equal") throws {
        if actual != expected {
            throw TestError.assertionFailed("\(message): expected \(expected), got \(actual)")
        }
    }
    
    /// Assert that two values are not equal
    public static func assertNotEqual<T: Equatable>(_ actual: T, _ expected: T, _ message: String = "Values should not be equal") throws {
        if actual == expected {
            throw TestError.assertionFailed("\(message): values are equal (\(actual))")
        }
    }
    
    /// Assert that a value is nil
    public static func assertNil<T>(_ value: T?, _ message: String = "Expected nil") throws {
        if value != nil {
            throw TestError.assertionFailed("\(message): expected nil, got \(value!)")
        }
    }
    
    /// Assert that a value is not nil
    public static func assertNotNil<T>(_ value: T?, _ message: String = "Expected non-nil value") throws {
        if value == nil {
            throw TestError.assertionFailed(message)
        }
    }
    
    /// Assert that a collection contains an element
    public static func assertContains<T: Equatable>(_ collection: [T], _ element: T, _ message: String = "Element not found") throws {
        if !collection.contains(element) {
            throw TestError.assertionFailed("\(message): \(element) not found in \(collection)")
        }
    }
    
    /// Assert that a collection does not contain an element
    public static func assertNotContains<T: Equatable>(_ collection: [T], _ element: T, _ message: String = "Element should not be present") throws {
        if collection.contains(element) {
            throw TestError.assertionFailed("\(message): \(element) found in \(collection)")
        }
    }
    
    /// Assert that a value is within a range
    public static func assertInRange<T: Comparable>(_ value: T, min: T, max: T, _ message: String = "Value out of range") throws {
        if value < min || value > max {
            throw TestError.assertionFailed("\(message): \(value) not in range [\(min), \(max)]")
        }
    }
    
    /// Assert that an operation throws an error
    public static func assertThrows<T>(_ operation: () throws -> T, _ message: String = "Expected error") throws {
        do {
            _ = try operation()
            throw TestError.assertionFailed("\(message): operation did not throw")
        } catch {
            // Expected behavior
        }
    }
    
    /// Assert that an operation does not throw an error
    public static func assertNoThrow<T>(_ operation: () throws -> T, _ message: String = "Unexpected error") throws {
        do {
            _ = try operation()
        } catch {
            throw TestError.assertionFailed("\(message): \(error)")
        }
    }
    
    /// Assert that an async operation throws an error
    public static func assertAsyncThrows<T>(_ operation: () async throws -> T, _ message: String = "Expected error") async throws {
        do {
            _ = try await operation()
            throw TestError.assertionFailed("\(message): operation did not throw")
        } catch {
            // Expected behavior
        }
    }
    
    /// Assert that an async operation does not throw an error
    public static func assertAsyncNoThrow<T>(_ operation: () async throws -> T, _ message: String = "Unexpected error") async throws {
        do {
            _ = try await operation()
        } catch {
            throw TestError.assertionFailed("\(message): \(error)")
        }
    }
}
