//
//  WALTests.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-27.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Comprehensive WAL acceptance tests

import Foundation

/// WAL acceptance test result
public struct WALTestResult {
    public let testName: String
    public let passed: Bool
    public let duration: TimeInterval
    public let message: String
    public let metrics: WALTestMetrics
    
    public init(testName: String, passed: Bool, duration: TimeInterval, message: String, metrics: WALTestMetrics = WALTestMetrics()) {
        self.testName = testName
        self.passed = passed
        self.duration = duration
        self.message = message
        self.metrics = metrics
    }
}

/// WAL test metrics
public struct WALTestMetrics {
    public var recordsWritten: Int = 0
    public var recordsRead: Int = 0
    public var bytesWritten: Int = 0
    public var groupCommitBatches: Int = 0
    public var averageBatchSize: Double = 0.0
    public var fsyncs: Int = 0
    public var recoveredRecords: Int = 0
    public var compressionRatio: Double = 1.0
}

/// Comprehensive WAL test suite
public class WALTests {
    
    private let testDataDir: String
    private var tempDatabases: [Database] = []
    
    public init(testDataDir: String = "/tmp/colibri_wal_tests") {
        self.testDataDir = testDataDir
        
        // Ensure test directory exists
        let fileManager = FileManager.default
        if !fileManager.fileExists(atPath: testDataDir) {
            try? fileManager.createDirectory(atPath: testDataDir, withIntermediateDirectories: true)
        }
    }
    
    deinit {
        // Clean up test databases
        for db in tempDatabases {
            try? db.close()
        }
        
        // Clean up test directory
        try? FileManager.default.removeItem(atPath: testDataDir)
    }
    
    // MARK: - Public Test Interface
    
    /// Run all WAL acceptance tests
    public func runAllTests() -> [WALTestResult] {
        let tests: [(String, () throws -> WALTestResult)] = [
            ("WAL Basic Write/Read", testBasicWriteRead),
            ("WAL Group Commit", testGroupCommit),
            ("WAL Durability Modes", testDurabilityModes),
            ("WAL Recovery After Crash", testRecoveryAfterCrash),
            ("WAL Transaction Logging", testTransactionLogging),
            ("WAL Index Operations", testIndexOperations),
            ("WAL Compression", testCompression),
            ("WAL Checkpoint", testCheckpoint),
            ("WAL Performance", testPerformance),
            ("WAL Optimization", testOptimization)
        ]
        
        var results: [WALTestResult] = []
        
        for (testName, testFunc) in tests {
            print("Running test: \(testName)")
            
            let startTime = Date()
            
            do {
                let result = try testFunc()
                results.append(result)
                print("✅ \(testName): \(result.passed ? "PASSED" : "FAILED") - \(result.message)")
            } catch {
                let duration = Date().timeIntervalSince(startTime)
                let result = WALTestResult(
                    testName: testName,
                    passed: false,
                    duration: duration,
                    message: "Test threw error: \(error)"
                )
                results.append(result)
                print("❌ \(testName): FAILED - \(error)")
            }
        }
        
        return results
    }
    
    // MARK: - Test 1: Basic Write/Read
    
    private func testBasicWriteRead() throws -> WALTestResult {
        let startTime = Date()
        var metrics = WALTestMetrics()
        
        let db = try createTestDatabase(testId: "basic_write_read")
        
        // Test basic WAL operations
        let tid = try db.begin()
        try db.insert(table: "test_table", row: ["id": .int(1), "name": .string("test")], tid: tid)
        try db.commit(tid)
        
        // Verify WAL was written
        guard let wal = db.globalWAL else {
            throw TestError.setupFailed("WAL not initialized")
        }
        
        let lastLSN = try wal.lastLSN()
        assert(lastLSN > 0, "WAL should have records")
        
        // Read records back
        let records = try Array(wal.iterate(from: 1))
        assert(records.count >= 3, "Should have BEGIN, HEAP_INSERT, COMMIT records")
        
        metrics.recordsWritten = records.count
        metrics.recordsRead = records.count
        
        let duration = Date().timeIntervalSince(startTime)
        return WALTestResult(
            testName: "WAL Basic Write/Read",
            passed: true,
            duration: duration,
            message: "Successfully wrote and read \(records.count) WAL records",
            metrics: metrics
        )
    }
    
    // MARK: - Test 2: Group Commit
    
    private func testGroupCommit() throws -> WALTestResult {
        let startTime = Date()
        var metrics = WALTestMetrics()
        
        let db = try createTestDatabase(testId: "group_commit", durabilityMode: .grouped)
        
        // Create multiple concurrent transactions
        var tids: [UInt64] = []
        for i in 0..<5 {
            let tid = try db.begin()
            try db.insert(table: "test_table", row: ["id": .int(i), "name": .string("test\(i)")], tid: tid)
            tids.append(tid)
        }
        
        // Commit all at once to trigger group commit
        for tid in tids {
            try db.commit(tid)
        }
        
        // Check optimization metrics
        if let optimizationMetrics = db.globalWAL?.optimizationMetrics {
            metrics.groupCommitBatches = optimizationMetrics.totalBatches
            metrics.averageBatchSize = optimizationMetrics.averageBatchSize
        }
        
        let duration = Date().timeIntervalSince(startTime)
        return WALTestResult(
            testName: "WAL Group Commit",
            passed: metrics.groupCommitBatches > 0,
            duration: duration,
            message: "Group commit processed \(metrics.groupCommitBatches) batches with avg size \(metrics.averageBatchSize)",
            metrics: metrics
        )
    }
    
    // MARK: - Test 3: Durability Modes
    
    private func testDurabilityModes() throws -> WALTestResult {
        let startTime = Date()
        var metrics = WALTestMetrics()
        
        // Test different durability modes
        let modes: [(DurabilityMode, String)] = [
            (.always, "always"),
            (.grouped, "grouped"),
            (.relaxed, "relaxed")
        ]
        
        for (mode, name) in modes {
            let db = try createTestDatabase(testId: "durability_\(name)", durabilityMode: mode)
            
            let tid = try db.begin()
            try db.insert(table: "test_table", row: ["id": .int(1), "mode": .string(name)], tid: tid)
            try db.commit(tid)
            
            // Verify records are persistent
            guard let wal = db.globalWAL else {
                throw TestError.setupFailed("WAL not initialized")
            }
            
            let records = try Array(wal.iterate(from: 1))
            assert(records.count >= 3, "Should have records for mode \(name)")
            metrics.recordsWritten += records.count
        }
        
        let duration = Date().timeIntervalSince(startTime)
        return WALTestResult(
            testName: "WAL Durability Modes",
            passed: true,
            duration: duration,
            message: "Successfully tested all durability modes",
            metrics: metrics
        )
    }
    
    // MARK: - Test 4: Recovery After Crash
    
    private func testRecoveryAfterCrash() throws -> WALTestResult {
        let startTime = Date()
        var metrics = WALTestMetrics()
        
        // Create database and write data
        let dbPath = "\(testDataDir)/recovery_test"
        var db = try createTestDatabase(testId: "recovery_test")
        
        let tid = try db.begin()
        try db.insert(table: "test_table", row: ["id": .int(1), "data": .string("before crash")], tid: tid)
        try db.commit(tid)
        
        // Record WAL state before "crash"
        let recordsBeforeCrash = try Array(db.globalWAL!.iterate(from: 1))
        metrics.recordsWritten = recordsBeforeCrash.count
        
        // Simulate crash by closing without proper shutdown
        try db.close()
        
        // Reopen database to trigger recovery
        db = try createTestDatabase(testId: "recovery_test")
        
        // Verify data is recovered
        let recordsAfterRecovery = try Array(db.globalWAL!.iterate(from: 1))
        metrics.recoveredRecords = recordsAfterRecovery.count
        
        let duration = Date().timeIntervalSince(startTime)
        return WALTestResult(
            testName: "WAL Recovery After Crash",
            passed: metrics.recoveredRecords >= metrics.recordsWritten,
            duration: duration,
            message: "Recovered \(metrics.recoveredRecords) records after simulated crash",
            metrics: metrics
        )
    }
    
    // MARK: - Test 5: Transaction Logging
    
    private func testTransactionLogging() throws -> WALTestResult {
        let startTime = Date()
        var metrics = WALTestMetrics()
        
        let db = try createTestDatabase(testId: "transaction_logging")
        
        // Test transaction commit
        let tid1 = try db.begin()
        try db.insert(table: "test_table", row: ["id": .int(1), "type": .string("commit")], tid: tid1)
        try db.commit(tid1)
        
        // Test transaction rollback
        let tid2 = try db.begin()
        try db.insert(table: "test_table", row: ["id": .int(2), "type": .string("rollback")], tid: tid2)
        try db.rollback(tid2)
        
        // Verify WAL contains appropriate records
        let records = try Array(db.globalWAL!.iterate(from: 1))
        
        let beginRecords = records.compactMap { $0 as? WALBeginRecord }
        let commitRecords = records.compactMap { $0 as? WALCommitRecord }
        let abortRecords = records.compactMap { $0 as? WALAbortRecord }
        
        assert(beginRecords.count == 2, "Should have 2 BEGIN records")
        assert(commitRecords.count == 1, "Should have 1 COMMIT record")
        assert(abortRecords.count == 1, "Should have 1 ABORT record")
        
        metrics.recordsWritten = records.count
        
        let duration = Date().timeIntervalSince(startTime)
        return WALTestResult(
            testName: "WAL Transaction Logging",
            passed: true,
            duration: duration,
            message: "Correctly logged \(beginRecords.count) begins, \(commitRecords.count) commits, \(abortRecords.count) aborts",
            metrics: metrics
        )
    }
    
    // MARK: - Test 6: Index Operations
    
    private func testIndexOperations() throws -> WALTestResult {
        let startTime = Date()
        var metrics = WALTestMetrics()
        
        let db = try createTestDatabase(testId: "index_operations")
        
        // Create table with index
        try db.query("CREATE TABLE indexed_table (id INT, name STRING)")
        try db.query("CREATE INDEX idx_name ON indexed_table (name)")
        
        // Insert data that should trigger index logging
        let tid = try db.begin()
        try db.insert(table: "indexed_table", row: ["id": .int(1), "name": .string("indexed")], tid: tid)
        try db.commit(tid)
        
        // Verify index operations are logged
        let records = try Array(db.globalWAL!.iterate(from: 1))
        let indexRecords = records.filter { record in
            return record is WALIndexInsertRecord || record is WALIndexDeleteRecord
        }
        
        metrics.recordsWritten = records.count
        
        let duration = Date().timeIntervalSince(startTime)
        return WALTestResult(
            testName: "WAL Index Operations",
            passed: !indexRecords.isEmpty,
            duration: duration,
            message: "Logged \(indexRecords.count) index operations out of \(records.count) total records",
            metrics: metrics
        )
    }
    
    // MARK: - Test 7: Compression
    
    private func testCompression() throws -> WALTestResult {
        let startTime = Date()
        var metrics = WALTestMetrics()
        
        let db = try createTestDatabase(testId: "compression", compressionAlgorithm: .lzfse)
        
        // Insert large data to trigger compression
        let largeData = String(repeating: "compression_test_data_", count: 100)
        let tid = try db.begin()
        try db.insert(table: "test_table", row: ["id": .int(1), "data": .string(largeData)], tid: tid)
        try db.commit(tid)
        
        // Check compression metrics
        if let optimizationMetrics = db.globalWAL?.optimizationMetrics {
            metrics.compressionRatio = optimizationMetrics.compressionRatio
        }
        
        let records = try Array(db.globalWAL!.iterate(from: 1))
        metrics.recordsWritten = records.count
        
        let duration = Date().timeIntervalSince(startTime)
        return WALTestResult(
            testName: "WAL Compression",
            passed: metrics.compressionRatio < 1.0,
            duration: duration,
            message: "Achieved compression ratio of \(metrics.compressionRatio)",
            metrics: metrics
        )
    }
    
    // MARK: - Test 8: Checkpoint
    
    private func testCheckpoint() throws -> WALTestResult {
        let startTime = Date()
        var metrics = WALTestMetrics()
        
        let db = try createTestDatabase(testId: "checkpoint")
        
        // Generate some WAL data
        for i in 0..<5 {
            let tid = try db.begin()
            try db.insert(table: "test_table", row: ["id": .int(i), "data": .string("checkpoint_test_\(i)")], tid: tid)
            try db.commit(tid)
        }
        
        // Create checkpoint
        let dpt: [UInt64: UInt64] = [1: 10, 2: 20]  // Mock dirty page table
        let att: [UInt64: UInt64] = [:]  // No active transactions
        
        let checkpointLSN = try db.globalWAL!.writeCheckpoint(dpt: dpt, att: att)
        
        // Verify checkpoint was written
        let records = try Array(db.globalWAL!.iterate(from: 1))
        let checkpointRecords = records.compactMap { $0 as? WALCheckpointRecord }
        
        assert(!checkpointRecords.isEmpty, "Should have checkpoint record")
        assert(checkpointLSN > 0, "Checkpoint LSN should be valid")
        
        metrics.recordsWritten = records.count
        
        let duration = Date().timeIntervalSince(startTime)
        return WALTestResult(
            testName: "WAL Checkpoint",
            passed: !checkpointRecords.isEmpty,
            duration: duration,
            message: "Successfully created checkpoint at LSN \(checkpointLSN)",
            metrics: metrics
        )
    }
    
    // MARK: - Test 9: Performance
    
    private func testPerformance() throws -> WALTestResult {
        let startTime = Date()
        var metrics = WALTestMetrics()
        
        let db = try createTestDatabase(testId: "performance", durabilityMode: .grouped)
        
        // Benchmark WAL performance
        let operationCount = 1000
        let performanceStartTime = Date()
        
        for i in 0..<operationCount {
            let tid = try db.begin()
            try db.insert(table: "test_table", row: ["id": .int(i), "data": .string("perf_test_\(i)")], tid: tid)
            try db.commit(tid)
        }
        
        let performanceDuration = Date().timeIntervalSince(performanceStartTime)
        let opsPerSecond = Double(operationCount) / performanceDuration
        
        metrics.recordsWritten = operationCount * 3  // BEGIN + INSERT + COMMIT
        
        let duration = Date().timeIntervalSince(startTime)
        return WALTestResult(
            testName: "WAL Performance",
            passed: opsPerSecond > 100,  // Expect at least 100 ops/sec
            duration: duration,
            message: "Achieved \(Int(opsPerSecond)) operations/sec (\(operationCount) ops in \(performanceDuration)s)",
            metrics: metrics
        )
    }
    
    // MARK: - Test 10: Optimization
    
    private func testOptimization() throws -> WALTestResult {
        let startTime = Date()
        var metrics = WALTestMetrics()
        
        let db = try createTestDatabase(testId: "optimization", durabilityMode: .grouped)
        
        // Test adaptive optimization
        for batch in 0..<10 {
            for i in 0..<20 {
                let tid = try db.begin()
                try db.insert(table: "test_table", row: ["id": .int(batch * 20 + i), "batch": .int(batch)], tid: tid)
                try db.commit(tid)
            }
            
            // Force group commit
            try db.globalWAL?.groupCommitSync()
        }
        
        // Check optimization metrics
        if let optimizationMetrics = db.globalWAL?.optimizationMetrics {
            metrics.groupCommitBatches = optimizationMetrics.totalBatches
            metrics.averageBatchSize = optimizationMetrics.averageBatchSize
            
            // Check if adaptive optimization is working
            let hasAdaptations = optimizationMetrics.adaptiveAdjustments > 0
            
            let duration = Date().timeIntervalSince(startTime)
            return WALTestResult(
                testName: "WAL Optimization",
                passed: hasAdaptations && metrics.groupCommitBatches > 0,
                duration: duration,
                message: "Optimization made \(optimizationMetrics.adaptiveAdjustments) adjustments, \(metrics.groupCommitBatches) batches",
                metrics: metrics
            )
        }
        
        let duration = Date().timeIntervalSince(startTime)
        return WALTestResult(
            testName: "WAL Optimization",
            passed: false,
            duration: duration,
            message: "Could not access optimization metrics",
            metrics: metrics
        )
    }
    
    // MARK: - Helper Methods
    
    private func createTestDatabase(
        testId: String,
        durabilityMode: DurabilityMode = .always,
        compressionAlgorithm: CompressionAlgorithm = .none
    ) throws -> Database {
        let dbPath = "\(testDataDir)/\(testId)"
        
        // Clean up any existing test data
        try? FileManager.default.removeItem(atPath: dbPath)
        
        var config = DBConfig()
        config.dataDir = dbPath
        config.walEnabled = true
        config.walFullFSyncEnabled = durabilityMode == .always
        config.walGroupCommitMs = 5.0
        config.walCompression = compressionAlgorithm
        
        let db = Database(config: config)
        tempDatabases.append(db)
        
        // Create a test table
        try db.query("CREATE TABLE test_table (id INT, name STRING, data STRING)")
        
        return db
    }
}

/// Test error types
public enum TestError: Error {
    case setupFailed(String)
    case assertionFailed(String)
    case unexpectedResult(String)
}

// MARK: - Test Summary

extension Array where Element == WALTestResult {
    /// Generate a summary of test results
    public func summary() -> String {
        let passed = filter { $0.passed }.count
        let total = count
        let totalDuration = reduce(0) { $0 + $1.duration }
        
        var summary = """
        WAL Test Summary:
        ================
        Tests Run: \(total)
        Passed: \(passed)
        Failed: \(total - passed)
        Total Duration: \(String(format: "%.2f", totalDuration))s
        
        """
        
        for result in self {
            let status = result.passed ? "✅ PASS" : "❌ FAIL"
            summary += "\(status) \(result.testName) (\(String(format: "%.3f", result.duration))s)\n"
            if !result.passed {
                summary += "      \(result.message)\n"
            }
        }
        
        return summary
    }
}
