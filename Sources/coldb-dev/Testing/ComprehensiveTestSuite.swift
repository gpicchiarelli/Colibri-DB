//
//  ComprehensiveTestSuite.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-01-27.
//
// ColibrDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Comprehensive test suite for all ColibrDB functionality.

import Foundation
import ColibriCore
import os.log

/// Comprehensive test suite for ColibrDB
public final class ComprehensiveTestSuite {
    private let logger = Logger(subsystem: "com.colibridb.testing", category: "suite")
    private let database: Database
    private let config: TestConfig
    
    // Test results
    private var testResults: [TestResult] = []
    private let resultsLock = NSLock()
    
    // Test categories
    private let unitTests: UnitTestSuite
    private let integrationTests: IntegrationTestSuite
    private let performanceTests: PerformanceTestSuite
    private let stressTests: StressTestSuite
    private let regressionTests: RegressionTestSuite
    private let memoryTests: MemoryTestSuite
    private let concurrencyTests: ConcurrencyTestSuite
    private let apiTests: APITestSuite
    
    // External test runners
    private let xcTestRunner: XCTestRunner
    private let swiftTestingRunner: SwiftTestingRunner
    private let benchmarkRunner: BenchmarkRunner
    
    public init(database: Database, config: TestConfig, outputDirectory: String = "dev-environment/logs") {
        self.database = database
        self.config = config
        
        // Initialize test suites
        self.unitTests = UnitTestSuite(database: database, config: config)
        self.integrationTests = IntegrationTestSuite(database: database, config: config)
        self.performanceTests = PerformanceTestSuite(database: database, config: config)
        self.stressTests = StressTestSuite(database: database, config: config)
        self.regressionTests = RegressionTestSuite(database: database, config: config)
        self.memoryTests = MemoryTestSuite(database: database, config: config)
        self.concurrencyTests = ConcurrencyTestSuite(database: database, config: config)
        self.apiTests = APITestSuite(database: database, config: config)
        
        // Initialize external test runners
        self.xcTestRunner = XCTestRunner(
            testBundlePath: "Tests/ColibriCoreTests",
            outputDirectory: outputDirectory
        )
        self.swiftTestingRunner = SwiftTestingRunner(
            testExecutablePath: ".build/debug/ColibriCoreTests",
            outputDirectory: outputDirectory
        )
        self.benchmarkRunner = BenchmarkRunner(
            benchmarkExecutablePath: ".build/debug/Benchmarks",
            outputDirectory: outputDirectory
        )
    }
    
    // MARK: - Test Execution
    
    /// Runs all tests including external test frameworks
    public func runAllTests() -> TestSuiteResult {
        logger.info("Starting comprehensive test suite execution")
        
        let startTime = Date()
        var allResults: [TestResult] = []
        
        // Run internal test suites
        let internalResults = runInternalTests()
        allResults.append(contentsOf: internalResults.results)
        
        // Run XCTest tests
        let xcTestResults = runXCTestTests()
        allResults.append(contentsOf: xcTestResults.results)
        
        // Run Swift Testing tests
        let swiftTestingResults = runSwiftTestingTests()
        allResults.append(contentsOf: swiftTestingResults.results)
        
        let endTime = Date()
        let totalDuration = endTime.timeIntervalSince(startTime)
        
        let totalTests = allResults.count
        let passedTests = allResults.filter { $0.success }.count
        let failedTests = totalTests - passedTests
        
        let result = TestSuiteResult(
            totalTests: totalTests,
            passedTests: passedTests,
            failedTests: failedTests,
            duration: totalDuration,
            results: allResults,
            timestamp: endTime
        )
        
        logger.info("Comprehensive test suite completed: \(passedTests)/\(totalTests) passed in \(String(format: "%.2f", totalDuration))s")
        
        return result
    }
    
    /// Runs only internal test suites
    public func runInternalTests() -> TestSuiteResult {
        logger.info("Starting comprehensive test suite")
        
        let startTime = Date()
        var totalTests = 0
        var passedTests = 0
        var failedTests = 0
        var skippedTests = 0
        
        // Run test categories
        let unitResult = runUnitTests()
        totalTests += unitResult.totalTests
        passedTests += unitResult.passedTests
        failedTests += unitResult.failedTests
        skippedTests += unitResult.skippedTests
        
        let integrationResult = runIntegrationTests()
        totalTests += integrationResult.totalTests
        passedTests += integrationResult.passedTests
        failedTests += integrationResult.failedTests
        skippedTests += integrationResult.skippedTests
        
        let performanceResult = runPerformanceTests()
        totalTests += performanceResult.totalTests
        passedTests += performanceResult.passedTests
        failedTests += performanceResult.failedTests
        skippedTests += performanceResult.skippedTests
        
        let stressResult = runStressTests()
        totalTests += stressResult.totalTests
        passedTests += stressResult.passedTests
        failedTests += stressResult.failedTests
        skippedTests += stressResult.skippedTests
        
        let regressionResult = runRegressionTests()
        totalTests += regressionResult.totalTests
        passedTests += regressionResult.passedTests
        failedTests += regressionResult.failedTests
        skippedTests += regressionResult.skippedTests
        
        let memoryResult = runMemoryTests()
        totalTests += memoryResult.totalTests
        passedTests += memoryResult.passedTests
        failedTests += memoryResult.failedTests
        skippedTests += memoryResult.skippedTests
        
        let concurrencyResult = runConcurrencyTests()
        totalTests += concurrencyResult.totalTests
        passedTests += concurrencyResult.passedTests
        failedTests += concurrencyResult.failedTests
        skippedTests += concurrencyResult.skippedTests
        
        let apiResult = runAPITests()
        totalTests += apiResult.totalTests
        passedTests += apiResult.passedTests
        failedTests += apiResult.failedTests
        skippedTests += apiResult.skippedTests
        
        let endTime = Date()
        let duration = endTime.timeIntervalSince(startTime)
        
        let result = TestSuiteResult(
            totalTests: totalTests,
            passedTests: passedTests,
            failedTests: failedTests,
            skippedTests: skippedTests,
            duration: duration,
            successRate: totalTests > 0 ? Double(passedTests) / Double(totalTests) : 0.0,
            categories: [
                "unit": unitResult,
                "integration": integrationResult,
                "performance": performanceResult,
                "stress": stressResult,
                "regression": regressionResult,
                "memory": memoryResult,
                "concurrency": concurrencyResult,
                "api": apiResult
            ]
        )
        
        logger.info("Comprehensive test suite completed: \(passedTests)/\(totalTests) passed")
        
        return result
    }
    
    /// Runs unit tests
    public func runUnitTests() -> TestCategoryResult {
        logger.info("Running unit tests")
        return unitTests.runTests()
    }
    
    /// Runs integration tests
    public func runIntegrationTests() -> TestCategoryResult {
        logger.info("Running integration tests")
        return integrationTests.runTests()
    }
    
    /// Runs performance tests
    public func runPerformanceTests() -> TestCategoryResult {
        logger.info("Running performance tests")
        return performanceTests.runTests()
    }
    
    /// Runs stress tests
    public func runStressTests() -> TestCategoryResult {
        logger.info("Running stress tests")
        return stressTests.runTests()
    }
    
    /// Runs regression tests
    public func runRegressionTests() -> TestCategoryResult {
        logger.info("Running regression tests")
        return regressionTests.runTests()
    }
    
    /// Runs memory tests
    public func runMemoryTests() -> TestCategoryResult {
        logger.info("Running memory tests")
        return memoryTests.runTests()
    }
    
    /// Runs concurrency tests
    public func runConcurrencyTests() -> TestCategoryResult {
        logger.info("Running concurrency tests")
        return concurrencyTests.runTests()
    }
    
    /// Runs API tests
    public func runAPITests() -> TestCategoryResult {
        logger.info("Running API tests")
        return apiTests.runTests()
    }
    
    // MARK: - Test Results
    
    /// Gets test results
    public func getTestResults() -> [TestResult] {
        resultsLock.lock()
        defer { resultsLock.unlock() }
        return testResults
    }
    
    /// Adds test result
    private func addTestResult(_ result: TestResult) {
        resultsLock.lock()
        defer { resultsLock.unlock() }
        testResults.append(result)
    }
}

// MARK: - Unit Test Suite

/// Unit test suite
public final class UnitTestSuite {
    private let database: Database
    private let config: TestConfig
    private let logger = Logger(subsystem: "com.colibridb.testing", category: "unit")
    
    public init(database: Database, config: TestConfig) {
        self.database = database
        self.config = config
    }
    
    public func runTests() -> TestCategoryResult {
        let startTime = Date()
        var results: [TestResult] = []
        
        // Test SQL parser
        results.append(testSQLParser())
        
        // Test query executor
        results.append(testQueryExecutor())
        
        // Test transaction manager
        results.append(testTransactionManager())
        
        // Test index manager
        results.append(testIndexManager())
        
        // Test storage manager
        results.append(testStorageManager())
        
        // Test buffer pool
        results.append(testBufferPool())
        
        // Test constraint manager
        results.append(testConstraintManager())
        
        // Test data types
        results.append(testDataTypes())
        
        // Test functions
        results.append(testFunctions())
        
        // Test error handling
        results.append(testErrorHandling())
        
        let endTime = Date()
        let duration = endTime.timeIntervalSince(startTime)
        
        let passedTests = results.filter { $0.status == .passed }.count
        let failedTests = results.filter { $0.status == .failed }.count
        let skippedTests = results.filter { $0.status == .skipped }.count
        
        return TestCategoryResult(
            category: "unit",
            totalTests: results.count,
            passedTests: passedTests,
            failedTests: failedTests,
            skippedTests: skippedTests,
            duration: duration,
            results: results
        )
    }
    
    private func testSQLParser() -> TestResult {
        let testName = "SQL Parser"
        let startTime = Date()
        
        do {
            // Test basic SQL parsing
            let parser = SimpleSQLParser()
            let result = try parser.parse("SELECT * FROM users WHERE id = 1")
            
            if result.type == .select {
                return TestResult(
                    name: testName,
                    status: .passed,
                    duration: Date().timeIntervalSince(startTime),
                    message: "SQL parser working correctly"
                )
            } else {
                return TestResult(
                    name: testName,
                    status: .failed,
                    duration: Date().timeIntervalSince(startTime),
                    message: "SQL parser returned wrong type"
                )
            }
        } catch {
            return TestResult(
                name: testName,
                status: .failed,
                duration: Date().timeIntervalSince(startTime),
                message: "SQL parser failed: \(error)"
            )
        }
    }
    
    private func testQueryExecutor() -> TestResult {
        let testName = "Query Executor"
        let startTime = Date()
        
        do {
            // Test query execution
            let executor = QueryExecutor(database: database)
            let result = try executor.execute("SELECT 1 as test")
            
            if result.rows.count == 1 {
                return TestResult(
                    name: testName,
                    status: .passed,
                    duration: Date().timeIntervalSince(startTime),
                    message: "Query executor working correctly"
                )
            } else {
                return TestResult(
                    name: testName,
                    status: .failed,
                    duration: Date().timeIntervalSince(startTime),
                    message: "Query executor returned wrong result count"
                )
            }
        } catch {
            return TestResult(
                name: testName,
                status: .failed,
                duration: Date().timeIntervalSince(startTime),
                message: "Query executor failed: \(error)"
            )
        }
    }
    
    private func testTransactionManager() -> TestResult {
        let testName = "Transaction Manager"
        let startTime = Date()
        
        do {
            // Test transaction creation
            let transaction = try database.transactionManager.beginTransaction()
            
            if transaction.id > 0 {
                try database.transactionManager.commitTransaction(transaction.id)
                return TestResult(
                    name: testName,
                    status: .passed,
                    duration: Date().timeIntervalSince(startTime),
                    message: "Transaction manager working correctly"
                )
            } else {
                return TestResult(
                    name: testName,
                    status: .failed,
                    duration: Date().timeIntervalSince(startTime),
                    message: "Transaction manager created invalid transaction"
                )
            }
        } catch {
            return TestResult(
                name: testName,
                status: .failed,
                duration: Date().timeIntervalSince(startTime),
                message: "Transaction manager failed: \(error)"
            )
        }
    }
    
    private func testIndexManager() -> TestResult {
        let testName = "Index Manager"
        let startTime = Date()
        
        do {
            // Test index creation
            let index = try database.indexManager.createIndex(
                name: "test_index",
                tableName: "test_table",
                columnName: "id",
                type: .hash
            )
            
            if index.name == "test_index" {
                return TestResult(
                    name: testName,
                    status: .passed,
                    duration: Date().timeIntervalSince(startTime),
                    message: "Index manager working correctly"
                )
            } else {
                return TestResult(
                    name: testName,
                    status: .failed,
                    duration: Date().timeIntervalSince(startTime),
                    message: "Index manager created invalid index"
                )
            }
        } catch {
            return TestResult(
                name: testName,
                status: .failed,
                duration: Date().timeIntervalSince(startTime),
                message: "Index manager failed: \(error)"
            )
        }
    }
    
    private func testStorageManager() -> TestResult {
        let testName = "Storage Manager"
        let startTime = Date()
        
        do {
            // Test storage operations
            let data = "test data".data(using: .utf8)!
            let pageId = try database.storageManager.writePage(data: data)
            
            if pageId > 0 {
                let readData = try database.storageManager.readPage(pageId: pageId)
                if readData == data {
                    return TestResult(
                        name: testName,
                        status: .passed,
                        duration: Date().timeIntervalSince(startTime),
                        message: "Storage manager working correctly"
                    )
                } else {
                    return TestResult(
                        name: testName,
                        status: .failed,
                        duration: Date().timeIntervalSince(startTime),
                        message: "Storage manager read wrong data"
                    )
                }
            } else {
                return TestResult(
                    name: testName,
                    status: .failed,
                    duration: Date().timeIntervalSince(startTime),
                    message: "Storage manager returned invalid page ID"
                )
            }
        } catch {
            return TestResult(
                name: testName,
                status: .failed,
                duration: Date().timeIntervalSince(startTime),
                message: "Storage manager failed: \(error)"
            )
        }
    }
    
    private func testBufferPool() -> TestResult {
        let testName = "Buffer Pool"
        let startTime = Date()
        
        do {
            // Test buffer pool operations
            let data = "test data".data(using: .utf8)!
            let pageId = try database.bufferPool.allocatePage(data: data)
            
            if pageId > 0 {
                let readData = try database.bufferPool.getPage(pageId: pageId)
                if readData == data {
                    return TestResult(
                        name: testName,
                        status: .passed,
                        duration: Date().timeIntervalSince(startTime),
                        message: "Buffer pool working correctly"
                    )
                } else {
                    return TestResult(
                        name: testName,
                        status: .failed,
                        duration: Date().timeIntervalSince(startTime),
                        message: "Buffer pool read wrong data"
                    )
                }
            } else {
                return TestResult(
                    name: testName,
                    status: .failed,
                    duration: Date().timeIntervalSince(startTime),
                    message: "Buffer pool returned invalid page ID"
                )
            }
        } catch {
            return TestResult(
                name: testName,
                status: .failed,
                duration: Date().timeIntervalSince(startTime),
                message: "Buffer pool failed: \(error)"
            )
        }
    }
    
    private func testConstraintManager() -> TestResult {
        let testName = "Constraint Manager"
        let startTime = Date()
        
        do {
            // Test constraint creation
            let constraint = try database.constraintManager.addConstraint(
                tableName: "test_table",
                type: .primaryKey,
                columnName: "id"
            )
            
            if constraint.id > 0 {
                return TestResult(
                    name: testName,
                    status: .passed,
                    duration: Date().timeIntervalSince(startTime),
                    message: "Constraint manager working correctly"
                )
            } else {
                return TestResult(
                    name: testName,
                    status: .failed,
                    duration: Date().timeIntervalSince(startTime),
                    message: "Constraint manager created invalid constraint"
                )
            }
        } catch {
            return TestResult(
                name: testName,
                status: .failed,
                duration: Date().timeIntervalSince(startTime),
                message: "Constraint manager failed: \(error)"
            )
        }
    }
    
    private func testDataTypes() -> TestResult {
        let testName = "Data Types"
        let startTime = Date()
        
        do {
            // Test data type conversions
            let intValue = try DataType.integer.convert("123")
            let stringValue = try DataType.varchar(100).convert("test")
            let boolValue = try DataType.boolean.convert("true")
            
            if intValue as? Int == 123 &&
               stringValue as? String == "test" &&
               boolValue as? Bool == true {
                return TestResult(
                    name: testName,
                    status: .passed,
                    duration: Date().timeIntervalSince(startTime),
                    message: "Data types working correctly"
                )
            } else {
                return TestResult(
                    name: testName,
                    status: .failed,
                    duration: Date().timeIntervalSince(startTime),
                    message: "Data type conversions failed"
                )
            }
        } catch {
            return TestResult(
                name: testName,
                status: .failed,
                duration: Date().timeIntervalSince(startTime),
                message: "Data types failed: \(error)"
            )
        }
    }
    
    private func testFunctions() -> TestResult {
        let testName = "Functions"
        let startTime = Date()
        
        do {
            // Test built-in functions
            let countResult = try Function.count([1, 2, 3, 4, 5])
            let sumResult = try Function.sum([1, 2, 3, 4, 5])
            let avgResult = try Function.avg([1, 2, 3, 4, 5])
            
            if countResult as? Int == 5 &&
               sumResult as? Int == 15 &&
               avgResult as? Double == 3.0 {
                return TestResult(
                    name: testName,
                    status: .passed,
                    duration: Date().timeIntervalSince(startTime),
                    message: "Functions working correctly"
                )
            } else {
                return TestResult(
                    name: testName,
                    status: .failed,
                    duration: Date().timeIntervalSince(startTime),
                    message: "Function calculations failed"
                )
            }
        } catch {
            return TestResult(
                name: testName,
                status: .failed,
                duration: Date().timeIntervalSince(startTime),
                message: "Functions failed: \(error)"
            )
        }
    }
    
    private func testErrorHandling() -> TestResult {
        let testName = "Error Handling"
        let startTime = Date()
        
        do {
            // Test error handling
            try database.execute("INVALID SQL STATEMENT")
            return TestResult(
                name: testName,
                status: .failed,
                duration: Date().timeIntervalSince(startTime),
                message: "Error handling should have caught invalid SQL"
            )
        } catch {
            return TestResult(
                name: testName,
                status: .passed,
                duration: Date().timeIntervalSince(startTime),
                message: "Error handling working correctly"
            )
        }
    }
}

// MARK: - Supporting Types

/// Test configuration
public struct TestConfig {
    public let timeout: TimeInterval
    public let retries: Int
    public let verbose: Bool
    public let parallel: Bool
    public let categories: [String]
    
    public init(
        timeout: TimeInterval = 30.0,
        retries: Int = 3,
        verbose: Bool = false,
        parallel: Bool = false,
        categories: [String] = []
    ) {
        self.timeout = timeout
        self.retries = retries
        self.verbose = verbose
        self.parallel = parallel
        self.categories = categories
    }
}

/// Test result
public struct TestResult {
    public let name: String
    public let status: TestStatus
    public let duration: TimeInterval
    public let message: String
    public let timestamp: Date
    
    public init(name: String, status: TestStatus, duration: TimeInterval, message: String) {
        self.name = name
        self.status = status
        self.duration = duration
        self.message = message
        self.timestamp = Date()
    }
}

/// Test status
public enum TestStatus {
    case passed
    case failed
    case skipped
    case error
}

/// Test category result
public struct TestCategoryResult {
    public let category: String
    public let totalTests: Int
    public let passedTests: Int
    public let failedTests: Int
    public let skippedTests: Int
    public let duration: TimeInterval
    public let results: [TestResult]
}

/// Test suite result
public struct TestSuiteResult {
    public let totalTests: Int
    public let passedTests: Int
    public let failedTests: Int
    public let skippedTests: Int
    public let duration: TimeInterval
    public let successRate: Double
    public let categories: [String: TestCategoryResult]
}

// MARK: - Placeholder Test Suites

/// Integration test suite
public final class IntegrationTestSuite {
    private let database: Database
    private let config: TestConfig
    
    public init(database: Database, config: TestConfig) {
        self.database = database
        self.config = config
    }
    
    public func runTests() -> TestCategoryResult {
        // Implementation for integration tests
        return TestCategoryResult(
            category: "integration",
            totalTests: 0,
            passedTests: 0,
            failedTests: 0,
            skippedTests: 0,
            duration: 0.0,
            results: []
        )
    }
}

/// Performance test suite
public final class PerformanceTestSuite {
    private let database: Database
    private let config: TestConfig
    
    public init(database: Database, config: TestConfig) {
        self.database = database
        self.config = config
    }
    
    public func runTests() -> TestCategoryResult {
        // Implementation for performance tests
        return TestCategoryResult(
            category: "performance",
            totalTests: 0,
            passedTests: 0,
            failedTests: 0,
            skippedTests: 0,
            duration: 0.0,
            results: []
        )
    }
}

/// Stress test suite
public final class StressTestSuite {
    private let database: Database
    private let config: TestConfig
    
    public init(database: Database, config: TestConfig) {
        self.database = database
        self.config = config
    }
    
    public func runTests() -> TestCategoryResult {
        // Implementation for stress tests
        return TestCategoryResult(
            category: "stress",
            totalTests: 0,
            passedTests: 0,
            failedTests: 0,
            skippedTests: 0,
            duration: 0.0,
            results: []
        )
    }
}

/// Regression test suite
public final class RegressionTestSuite {
    private let database: Database
    private let config: TestConfig
    
    public init(database: Database, config: TestConfig) {
        self.database = database
        self.config = config
    }
    
    public func runTests() -> TestCategoryResult {
        // Implementation for regression tests
        return TestCategoryResult(
            category: "regression",
            totalTests: 0,
            passedTests: 0,
            failedTests: 0,
            skippedTests: 0,
            duration: 0.0,
            results: []
        )
    }
}

/// Memory test suite
public final class MemoryTestSuite {
    private let database: Database
    private let config: TestConfig
    
    public init(database: Database, config: TestConfig) {
        self.database = database
        self.config = config
    }
    
    public func runTests() -> TestCategoryResult {
        // Implementation for memory tests
        return TestCategoryResult(
            category: "memory",
            totalTests: 0,
            passedTests: 0,
            failedTests: 0,
            skippedTests: 0,
            duration: 0.0,
            results: []
        )
    }
}

/// Concurrency test suite
public final class ConcurrencyTestSuite {
    private let database: Database
    private let config: TestConfig
    
    public init(database: Database, config: TestConfig) {
        self.database = database
        self.config = config
    }
    
    public func runTests() -> TestCategoryResult {
        // Implementation for concurrency tests
        return TestCategoryResult(
            category: "concurrency",
            totalTests: 0,
            passedTests: 0,
            failedTests: 0,
            skippedTests: 0,
            duration: 0.0,
            results: []
        )
    }
}

/// API test suite
public final class APITestSuite {
    private let database: Database
    private let config: TestConfig
    
    public init(database: Database, config: TestConfig) {
        self.database = database
        self.config = config
    }
    
    public func runTests() -> TestCategoryResult {
        // Implementation for API tests
        return TestCategoryResult(
            category: "api",
            totalTests: 0,
            passedTests: 0,
            failedTests: 0,
            skippedTests: 0,
            duration: 0.0,
            results: []
        )
    }
    
    // MARK: - External Test Runners
    
    /// Runs XCTest tests
    public func runXCTestTests() -> TestSuiteResult {
        logger.info("Running XCTest tests")
        
        let xcTestResult = xcTestRunner.runAllTests()
        
        // Convert XCTest results to TestResult format
        let testResults = xcTestResult.testResults.map { xcTestResult in
            TestResult(
                name: xcTestResult.name,
                category: "xctest",
                success: xcTestResult.success,
                duration: xcTestResult.duration,
                error: xcTestResult.error,
                timestamp: Date()
            )
        }
        
        return TestSuiteResult(
            totalTests: xcTestResult.totalTests,
            passedTests: xcTestResult.passedTests,
            failedTests: xcTestResult.failedTests,
            duration: xcTestResult.duration,
            results: testResults,
            timestamp: xcTestResult.timestamp
        )
    }
    
    /// Runs Swift Testing tests
    public func runSwiftTestingTests() -> TestSuiteResult {
        logger.info("Running Swift Testing tests")
        
        let swiftTestingResult = swiftTestingRunner.runAllTests()
        
        // Convert Swift Testing results to TestResult format
        let testResults = swiftTestingResult.testResults.map { swiftTestResult in
            TestResult(
                name: swiftTestResult.name,
                category: "swift-testing",
                success: swiftTestResult.success,
                duration: swiftTestResult.duration,
                error: swiftTestResult.error,
                timestamp: Date()
            )
        }
        
        return TestSuiteResult(
            totalTests: swiftTestingResult.totalTests,
            passedTests: swiftTestingResult.passedTests,
            failedTests: swiftTestingResult.failedTests,
            duration: swiftTestingResult.duration,
            results: testResults,
            timestamp: swiftTestingResult.timestamp
        )
    }
    
    /// Runs benchmarks
    public func runBenchmarks() -> BenchmarkResult {
        logger.info("Running benchmarks")
        
        let benchmarkResult = benchmarkRunner.runAllBenchmarks()
        
        logger.info("Benchmarks completed: \(benchmarkResult.scenarios.count) scenarios, average throughput: \(String(format: "%.2f", benchmarkResult.averageThroughput)) ops/s")
        
        return benchmarkResult
    }
    
    /// Runs benchmarks by category
    public func runBenchmarksByCategory(_ category: BenchmarkCategory) -> BenchmarkResult {
        logger.info("Running benchmarks for category: \(category)")
        
        let benchmarkResult = benchmarkRunner.runBenchmarksByCategory(category)
        
        logger.info("Benchmarks completed: \(benchmarkResult.scenarios.count) scenarios, average throughput: \(String(format: "%.2f", benchmarkResult.averageThroughput)) ops/s")
        
        return benchmarkResult
    }
}
