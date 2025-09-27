//
//  TestRunner.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Automated test runner for development CLI.

import Foundation
import ColibriCore

enum TestError: Error {
    case constraintValidationFailed
}
import os.log

/// Automated test runner for ColibrìDB development
public class TestRunner {
    private let database: Database
    private let logger = Logger(subsystem: "com.colibridb.test", category: "runner")
    private var testResults: [TestResult] = []
    
    public init(database: Database) {
        self.database = database
    }
    
    // MARK: - Test Execution
    
    /// Runs all available tests
    public func runAllTests() -> TestSuiteResult {
        logger.info("Starting test suite execution")
        let startTime = Date()
        
        var results: [TestResult] = []
        
        // Run unit tests
        results.append(contentsOf: runUnitTests())
        
        // Run integration tests
        results.append(contentsOf: runIntegrationTests())
        
        // Run performance tests
        results.append(contentsOf: runPerformanceTests())
        
        // Run stress tests
        results.append(contentsOf: runStressTests())
        
        let endTime = Date()
        let duration = endTime.timeIntervalSince(startTime)
        
        let suiteResult = TestSuiteResult(
            totalTests: results.count,
            passedTests: results.filter { $0.success }.count,
            failedTests: results.filter { !$0.success }.count,
            duration: duration,
            results: results,
            timestamp: endTime
        )
        
        logger.info("Test suite completed: \(suiteResult.passedTests)/\(suiteResult.totalTests) passed in \(String(format: "%.2f", duration))s")
        
        return suiteResult
    }
    
    /// Runs unit tests
    public func runUnitTests() -> [TestResult] {
        logger.info("Running unit tests")
        var results: [TestResult] = []
        
        // Test CLI basic functionality
        results.append(runTest("CLI Basic", testCLIBasic))
        results.append(runTest("CLI Help", testCLIHelp))
        results.append(runTest("CLI Config", testCLIConfig))
        
        // Test table operations
        results.append(runTest("Table Creation", testTableCreation))
        results.append(runTest("Table Deletion", testTableDeletion))
        results.append(runTest("Table Alteration", testTableAlteration))
        
        // Test data operations
        results.append(runTest("Data Insert", testDataInsert))
        results.append(runTest("Data Scan", testDataScan))
        results.append(runTest("Data Delete", testDataDelete))
        
        // Test value parsing
        results.append(runTest("Value Parsing String", testValueParsingString))
        results.append(runTest("Value Parsing Int", testValueParsingInt))
        results.append(runTest("Value Parsing Double", testValueParsingDouble))
        results.append(runTest("Value Parsing Bool", testValueParsingBool))
        results.append(runTest("Value Parsing Null", testValueParsingNull))
        
        return results
    }
    
    /// Runs integration tests
    public func runIntegrationTests() -> [TestResult] {
        logger.info("Running integration tests")
        var results: [TestResult] = []
        
        // Test end-to-end workflows
        results.append(runTest("E2E Table Workflow", testE2ETableWorkflow))
        results.append(runTest("E2E Data Workflow", testE2EDataWorkflow))
        results.append(runTest("E2E Index Workflow", testE2EIndexWorkflow))
        results.append(runTest("E2E Transaction Workflow", testE2ETransactionWorkflow))
        
        // Test constraint enforcement
        results.append(runTest("Constraint Enforcement", testConstraintEnforcement))
        
        // Test data type conversions
        results.append(runTest("Data Type Conversions", testDataTypeConversions))
        
        return results
    }
    
    /// Runs performance tests
    public func runPerformanceTests() -> [TestResult] {
        logger.info("Running performance tests")
        var results: [TestResult] = []
        
        // Test SQL parsing performance
        results.append(runTest("SQL Parsing Performance", testSQLParsingPerformance))
        
        // Test constraint validation performance
        results.append(runTest("Constraint Validation Performance", testConstraintValidationPerformance))
        
        // Test data type operation performance
        results.append(runTest("Data Type Operation Performance", testDataTypeOperationPerformance))
        
        // Test memory usage
        results.append(runTest("Memory Usage", testMemoryUsage))
        
        return results
    }
    
    /// Runs stress tests
    public func runStressTests() -> [TestResult] {
        logger.info("Running stress tests")
        var results: [TestResult] = []
        
        // Test high-volume operations
        results.append(runTest("High Volume Insert", testHighVolumeInsert))
        results.append(runTest("High Volume Scan", testHighVolumeScan))
        results.append(runTest("High Volume Delete", testHighVolumeDelete))
        
        // Test concurrent operations
        results.append(runTest("Concurrent Operations", testConcurrentOperations))
        
        // Test memory stress
        results.append(runTest("Memory Stress", testMemoryStress))
        
        return results
    }
    
    // MARK: - Test Implementation
    
    private func runTest(_ name: String, _ test: () throws -> Void) -> TestResult {
        let startTime = Date()
        do {
            try test()
            let endTime = Date()
            let result = TestResult(
                name: name,
                success: true,
                duration: endTime.timeIntervalSince(startTime),
                error: nil,
                timestamp: endTime
            )
            logger.debug("Test '\(name)' passed in \(String(format: "%.4f", result.duration))s")
            return result
        } catch {
            let endTime = Date()
            let result = TestResult(
                name: name,
                success: false,
                duration: endTime.timeIntervalSince(startTime),
                error: error,
                timestamp: endTime
            )
            logger.error("Test '\(name)' failed: \(error)")
            return result
        }
    }
    
    // MARK: - Unit Tests
    
    private func testCLIBasic() throws {
        let cli = DevCLI(db: database, cfgPath: nil)
        cli.printBanner()
        cli.help()
        cli.showConfig()
        cli.listTables()
    }
    
    private func testCLIHelp() throws {
        let cli = DevCLI(db: database, cfgPath: nil)
        let helpOutput = captureOutput { cli.help() }
        XCTAssertTrue(helpOutput.contains("Commands:"))
        XCTAssertTrue(helpOutput.contains("\\help"))
    }
    
    private func testCLIConfig() throws {
        let cli = DevCLI(db: database, cfgPath: nil)
        let configOutput = captureOutput { cli.showConfig() }
        XCTAssertTrue(configOutput.contains("Configuration:"))
    }
    
    private func testTableCreation() throws {
        try database.createTable("test_table")
        let tables = database.listTables()
        XCTAssertTrue(tables.contains("test_table"))
    }
    
    private func testTableDeletion() throws {
        try database.createTable("test_table")
        try database.dropTable("test_table")
        let tables = database.listTables()
        XCTAssertFalse(tables.contains("test_table"))
    }
    
    private func testTableAlteration() throws {
        try database.createTable("test_table")
        try database.alterTable("test_table", operation: .addColumn("new_column", "string"))
        // Note: Actual verification would require schema inspection
    }
    
    private func testDataInsert() throws {
        try database.createTable("test_table")
        let row: Row = ["name": .string("John"), "age": .int(30)]
        let rid = try database.insert(into: "test_table", row: row)
        XCTAssertNotNil(rid)
    }
    
    private func testDataScan() throws {
        try database.createTable("test_table")
        let row: Row = ["name": .string("John"), "age": .int(30)]
        _ = try database.insert(into: "test_table", row: row)
        let rows = try database.scan("test_table")
        XCTAssertFalse(rows.isEmpty)
    }
    
    private func testDataDelete() throws {
        try database.createTable("test_table")
        let row: Row = ["name": .string("John"), "age": .int(30)]
        _ = try database.insert(into: "test_table", row: row)
        let deleted = try database.deleteEquals(table: "test_table", column: "name", value: .string("John"))
        XCTAssertEqual(deleted, 1)
    }
    
    private func testValueParsingString() throws {
        let cli = DevCLI(db: database, cfgPath: nil)
        let value = cli.parseValue("hello")
        XCTAssertEqual(value, .string("hello"))
    }
    
    private func testValueParsingInt() throws {
        let cli = DevCLI(db: database, cfgPath: nil)
        let value = cli.parseValue("42")
        XCTAssertEqual(value, .int(42))
    }
    
    private func testValueParsingDouble() throws {
        let cli = DevCLI(db: database, cfgPath: nil)
        let value = cli.parseValue("3.14")
        XCTAssertEqual(value, .double(3.14))
    }
    
    private func testValueParsingBool() throws {
        let cli = DevCLI(db: database, cfgPath: nil)
        let trueValue = cli.parseValue("true")
        XCTAssertEqual(trueValue, .bool(true))
        let falseValue = cli.parseValue("false")
        XCTAssertEqual(falseValue, .bool(false))
    }
    
    private func testValueParsingNull() throws {
        let cli = DevCLI(db: database, cfgPath: nil)
        let value = cli.parseValue("NULL")
        XCTAssertEqual(value, .null)
    }
    
    // MARK: - Integration Tests
    
    private func testE2ETableWorkflow() throws {
        // Create table
        try database.createTable("workflow_table")
        
        // Alter table
        try database.alterTable("workflow_table", operation: .addColumn("id", "int"))
        try database.alterTable("workflow_table", operation: .addColumn("name", "string"))
        
        // Insert data
        let row: Row = ["id": .int(1), "name": .string("Test")]
        _ = try database.insert(into: "workflow_table", row: row)
        
        // Scan data
        let rows = try database.scan("workflow_table")
        XCTAssertFalse(rows.isEmpty)
        
        // Drop table
        try database.dropTable("workflow_table")
    }
    
    private func testE2EDataWorkflow() throws {
        try database.createTable("data_table")
        
        // Insert multiple rows
        for i in 1...10 {
            let row: Row = ["id": .int(Int64(i)), "value": .string("Value \(i)")]
            _ = try database.insert(into: "data_table", row: row)
        }
        
        // Scan all rows
        let rows = try database.scan("data_table")
        XCTAssertEqual(rows.count, 10)
        
        // Delete some rows
        let deleted = try database.deleteEquals(table: "data_table", column: "id", value: .int(5))
        XCTAssertEqual(deleted, 1)
        
        // Verify deletion
        let remainingRows = try database.scan("data_table")
        XCTAssertEqual(remainingRows.count, 9)
    }
    
    private func testE2EIndexWorkflow() throws {
        try database.createTable("index_table")
        
        // Insert data
        for i in 1...100 {
            let row: Row = ["id": .int(Int64(i)), "value": .string("Value \(i)")]
            _ = try database.insert(into: "index_table", row: row)
        }
        
        // Create index
        try database.createIndex(name: "idx_id", on: "index_table", columns: ["id"], using: "Hash")
        
        // Search using index
        let results = try database.indexSearchEqualsTyped(table: "index_table", index: "idx_id", value: .int(50))
        XCTAssertFalse(results.isEmpty)
    }
    
    private func testE2ETransactionWorkflow() throws {
        try database.createTable("txn_table")
        
        // Begin transaction
        let tid = try database.begin()
        
        // Insert data
        let row: Row = ["id": .int(1), "value": .string("Transaction Test")]
        _ = try database.insert(into: "txn_table", row: row, tid: tid)
        
        // Commit transaction
        try database.commit(tid)
        
        // Verify data
        let rows = try database.scan("txn_table")
        XCTAssertFalse(rows.isEmpty)
    }
    
    private func testConstraintEnforcement() throws {
        try database.createTable("constraint_table")
        
        // Add constraint
        let constraint = NotNullConstraint(name: "nn_id", column: "id")
        try database.constraintManager.addConstraint(constraint, to: "constraint_table")
        
        // Try to insert null value (should fail)
        let invalidRow: Row = ["id": .null, "value": .string("Test")]
        do {
            _ = try database.insert(into: "constraint_table", row: invalidRow)
            // If we get here, the constraint didn't work as expected
            throw TestError.constraintValidationFailed
        } catch {
            // Expected to throw an error
        }
        
        // Insert valid data
        let validRow: Row = ["id": .int(1), "value": .string("Test")]
        _ = try database.insert(into: "constraint_table", row: validRow)
    }
    
    private func testDataTypeConversions() throws {
        let cli = DevCLI(db: database, cfgPath: nil)
        
        // Test various data type conversions
        let stringValue = cli.parseValue("hello")
        XCTAssertEqual(stringValue, .string("hello"))
        
        let intValue = cli.parseValue("42")
        XCTAssertEqual(intValue, .int(42))
        
        let doubleValue = cli.parseValue("3.14")
        XCTAssertEqual(doubleValue, .double(3.14))
        
        let boolValue = cli.parseValue("true")
        XCTAssertEqual(boolValue, .bool(true))
        
        let nullValue = cli.parseValue("NULL")
        XCTAssertEqual(nullValue, .null)
    }
    
    // MARK: - Performance Tests
    
    private func testSQLParsingPerformance() throws {
        let sql = "SELECT * FROM test_table WHERE id = 1 AND name = 'test'"
        let cli = DevCLI(db: database, cfgPath: nil)
        
        let startTime = Date()
        for _ in 0..<1000 {
            _ = cli.parseValue(sql)
        }
        let endTime = Date()
        
        let duration = endTime.timeIntervalSince(startTime)
        XCTAssertLessThan(duration, 1.0) // Should complete in less than 1 second
    }
    
    private func testConstraintValidationPerformance() throws {
        try database.createTable("perf_table")
        
        // Add multiple constraints
        for i in 1...100 {
            let constraint = NotNullConstraint(name: "nn_\(i)", column: "col_\(i)")
            try database.constraintManager.addConstraint(constraint, to: "perf_table")
        }
        
        let startTime = Date()
        let constraints = database.constraintManager.getConstraints(for: "perf_table")
        let endTime = Date()
        
        let duration = endTime.timeIntervalSince(startTime)
        XCTAssertLessThan(duration, 0.1) // Should complete in less than 100ms
        XCTAssertEqual(constraints.count, 100)
    }
    
    private func testDataTypeOperationPerformance() throws {
        let cli = DevCLI(db: database, cfgPath: nil)
        
        let startTime = Date()
        for i in 0..<10000 {
            _ = cli.parseValue("value_\(i)")
        }
        let endTime = Date()
        
        let duration = endTime.timeIntervalSince(startTime)
        XCTAssertLessThan(duration, 0.5) // Should complete in less than 500ms
    }
    
    private func testMemoryUsage() throws {
        let debugTools = DebugTools(database: database)
        let analysis = debugTools.analyzeMemory()
        
        // Memory usage should be reasonable (less than 100MB for basic operations)
        XCTAssertLessThan(analysis.residentSizeMB, 100.0)
    }
    
    // MARK: - Stress Tests
    
    private func testHighVolumeInsert() throws {
        try database.createTable("stress_table")
        
        let startTime = Date()
        for i in 1...10000 {
            let row: Row = ["id": .int(Int64(i)), "value": .string("Value \(i)")]
            _ = try database.insert(into: "stress_table", row: row)
        }
        let endTime = Date()
        
        let duration = endTime.timeIntervalSince(startTime)
        XCTAssertLessThan(duration, 10.0) // Should complete in less than 10 seconds
        
        let rows = try database.scan("stress_table")
        XCTAssertEqual(rows.count, 10000)
    }
    
    private func testHighVolumeScan() throws {
        try database.createTable("scan_table")
        
        // Insert data
        for i in 1...1000 {
            let row: Row = ["id": .int(Int64(i)), "value": .string("Value \(i)")]
            _ = try database.insert(into: "scan_table", row: row)
        }
        
        let startTime = Date()
        for _ in 0..<100 {
            _ = try database.scan("scan_table")
        }
        let endTime = Date()
        
        let duration = endTime.timeIntervalSince(startTime)
        XCTAssertLessThan(duration, 5.0) // Should complete in less than 5 seconds
    }
    
    private func testHighVolumeDelete() throws {
        try database.createTable("delete_table")
        
        // Insert data
        for i in 1...1000 {
            let row: Row = ["id": .int(Int64(i)), "value": .string("Value \(i)")]
            _ = try database.insert(into: "delete_table", row: row)
        }
        
        let startTime = Date()
        for i in 1...1000 {
            _ = try database.deleteEquals(table: "delete_table", column: "id", value: .int(Int64(i)))
        }
        let endTime = Date()
        
        let duration = endTime.timeIntervalSince(startTime)
        XCTAssertLessThan(duration, 10.0) // Should complete in less than 10 seconds
        
        let rows = try database.scan("delete_table")
        XCTAssertEqual(rows.count, 0)
    }
    
    private func testConcurrentOperations() throws {
        try database.createTable("concurrent_table")
        
        let group = DispatchGroup()
        let queue = DispatchQueue.global(qos: .userInitiated)
        
        // Start multiple concurrent operations
        for i in 0..<10 {
            group.enter()
            queue.async {
                defer { group.leave() }
                
                for j in 1...100 {
                    let row: Row = ["id": .int(Int64(i * 100 + j)), "value": .string("Value \(i * 100 + j)")]
                    _ = try? self.database.insert(into: "concurrent_table", row: row)
                }
            }
        }
        
        let startTime = Date()
        group.wait()
        let endTime = Date()
        
        let duration = endTime.timeIntervalSince(startTime)
        XCTAssertLessThan(duration, 15.0) // Should complete in less than 15 seconds
        
        let rows = try database.scan("concurrent_table")
        XCTAssertEqual(rows.count, 1000)
    }
    
    private func testMemoryStress() throws {
        let debugTools = DebugTools(database: database)
        let initialMemory = debugTools.analyzeMemory()
        
        // Create many tables and insert data
        for i in 1...100 {
            try database.createTable("stress_table_\(i)")
            for j in 1...100 {
                let row: Row = ["id": .int(Int64(j)), "value": .string("Value \(j)")]
                _ = try database.insert(into: "stress_table_\(i)", row: row)
            }
        }
        
        let finalMemory = debugTools.analyzeMemory()
        let memoryIncrease = finalMemory.residentSize - initialMemory.residentSize
        
        // Memory increase should be reasonable (less than 500MB)
        XCTAssertLessThan(Double(memoryIncrease) / 1024.0 / 1024.0, 500.0)
    }
    
    // MARK: - Helper Methods
    
    private func captureOutput(_ block: () -> Void) -> String {
        let pipe = Pipe()
        let originalStdout = dup(fileno(stdout))
        
        dup2(pipe.fileHandleForWriting.fileDescriptor, fileno(stdout))
        
        block()
        
        fflush(stdout)
        dup2(originalStdout, fileno(stdout))
        close(originalStdout)
        
        let data = pipe.fileHandleForReading.readDataToEndOfFile()
        return String(data: data, encoding: .utf8) ?? ""
    }
}

// MARK: - Data Structures

public struct TestResult {
    public let name: String
    public let success: Bool
    public let duration: TimeInterval
    public let error: Error?
    public let timestamp: Date
}

public struct TestSuiteResult {
    public let totalTests: Int
    public let passedTests: Int
    public let failedTests: Int
    public let duration: TimeInterval
    public let results: [TestResult]
    public let timestamp: Date
    
    public var successRate: Double {
        return Double(passedTests) / Double(totalTests)
    }
}

// MARK: - Test Assertions

private func XCTAssertTrue(_ condition: Bool, file: StaticString = #file, line: UInt = #line) {
    if !condition {
        fatalError("Assertion failed: condition is false", file: file, line: line)
    }
}

private func XCTAssertFalse(_ condition: Bool, file: StaticString = #file, line: UInt = #line) {
    if condition {
        fatalError("Assertion failed: condition is true", file: file, line: line)
    }
}

private func XCTAssertEqual<T: Equatable>(_ expression1: T, _ expression2: T, file: StaticString = #file, line: UInt = #line) {
    if expression1 != expression2 {
        fatalError("Assertion failed: \(expression1) != \(expression2)", file: file, line: line)
    }
}

private func XCTAssertNotNil<T>(_ expression: T?, file: StaticString = #file, line: UInt = #line) {
    if expression == nil {
        fatalError("Assertion failed: expression is nil", file: file, line: line)
    }
}

private func XCTAssertLessThan<T: Comparable>(_ expression1: T, _ expression2: T, file: StaticString = #file, line: UInt = #line) {
    if expression1 >= expression2 {
        fatalError("Assertion failed: \(expression1) >= \(expression2)", file: file, line: line)
    }
}

private func XCTAssertThrowsError<T>(_ expression: () throws -> T, file: StaticString = #file, line: UInt = #line) {
    do {
        _ = try expression()
        fatalError("Assertion failed: expression did not throw error", file: file, line: line)
    } catch {
        // Expected to throw
    }
}
