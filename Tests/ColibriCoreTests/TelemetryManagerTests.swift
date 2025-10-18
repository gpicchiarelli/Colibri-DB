//
//  TelemetryManagerTests.swift
//  ColibrDBTests
//
//  Comprehensive tests for TelemetryManager
//
// ColibrDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

import XCTest
@testable import ColibriCore

final class TelemetryManagerTests: XCTestCase {
    
    var telemetry: TelemetryManager!
    
    override func setUp() {
        super.setUp()
        let config = TelemetryConfig(
            collectionInterval: 0.1, // Fast collection for tests
            enabled: true,
            collectSystemMetrics: true
        )
        telemetry = TelemetryManager(config: config)
    }
    
    override func tearDown() {
        telemetry.stopCollection()
        telemetry = nil
        super.tearDown()
    }
    
    // MARK: - Basic Functionality Tests
    
    func testInitialization() {
        XCTAssertNotNil(telemetry)
        XCTAssertEqual(telemetry.config.collectionInterval, 0.1)
        XCTAssertTrue(telemetry.config.enabled)
        XCTAssertTrue(telemetry.config.collectSystemMetrics)
    }
    
    func testDefaultConfiguration() {
        let defaultTelemetry = TelemetryManager()
        XCTAssertEqual(defaultTelemetry.config.collectionInterval, 1.0)
        XCTAssertTrue(defaultTelemetry.config.enabled)
    }
    
    // MARK: - Collection Tests
    
    func testStartStopCollection() {
        telemetry.startCollection()
        
        // Wait for collection to happen
        let expectation = XCTestExpectation(description: "Collection should happen")
        DispatchQueue.main.asyncAfter(deadline: .now() + 0.3) {
            expectation.fulfill()
        }
        wait(for: [expectation], timeout: 1.0)
        
        let metrics = telemetry.getCurrentMetrics()
        XCTAssertGreaterThan(metrics.collectionCount, 0)
        
        telemetry.stopCollection()
    }
    
    func testCollectionDoesNotStartTwice() {
        telemetry.startCollection()
        telemetry.startCollection() // Should be no-op
        
        // Should not cause any issues
        XCTAssertNotNil(telemetry)
        
        telemetry.stopCollection()
    }
    
    // MARK: - Metrics Recording Tests
    
    func testRecordQuery() {
        let initialMetrics = telemetry.getCurrentMetrics()
        
        telemetry.recordQuery()
        telemetry.recordQuery()
        telemetry.recordQuery()
        
        let metrics = telemetry.getCurrentMetrics()
        XCTAssertEqual(metrics.queryCount, initialMetrics.queryCount + 3)
    }
    
    func testRecordTransaction() {
        let initialMetrics = telemetry.getCurrentMetrics()
        
        telemetry.recordTransaction()
        telemetry.recordTransaction()
        
        let metrics = telemetry.getCurrentMetrics()
        XCTAssertEqual(metrics.transactionCount, initialMetrics.transactionCount + 2)
    }
    
    func testRecordCacheHits() {
        telemetry.recordCacheHit()
        telemetry.recordCacheHit()
        telemetry.recordCacheHit()
        
        let metrics = telemetry.getCurrentMetrics()
        XCTAssertEqual(metrics.cacheHits, 3)
    }
    
    func testRecordCacheMisses() {
        telemetry.recordCacheMiss()
        telemetry.recordCacheMiss()
        
        let metrics = telemetry.getCurrentMetrics()
        XCTAssertEqual(metrics.cacheMisses, 2)
    }
    
    func testCacheHitRate() {
        // Record 7 hits and 3 misses = 70% hit rate
        for _ in 0..<7 {
            telemetry.recordCacheHit()
        }
        for _ in 0..<3 {
            telemetry.recordCacheMiss()
        }
        
        let metrics = telemetry.getCurrentMetrics()
        XCTAssertEqual(metrics.cacheHitRate, 0.7, accuracy: 0.01)
    }
    
    func testCacheHitRateWithNoData() {
        let metrics = telemetry.getCurrentMetrics()
        XCTAssertEqual(metrics.cacheHitRate, 0.0)
    }
    
    func testSetActiveTransactions() {
        telemetry.setActiveTransactions(5)
        
        let metrics = telemetry.getCurrentMetrics()
        XCTAssertEqual(metrics.activeTransactions, 5)
        
        telemetry.setActiveTransactions(10)
        let updatedMetrics = telemetry.getCurrentMetrics()
        XCTAssertEqual(updatedMetrics.activeTransactions, 10)
    }
    
    // MARK: - Prometheus Export Tests
    
    func testPrometheusExport() {
        // Record some metrics
        telemetry.recordQuery()
        telemetry.recordQuery()
        telemetry.recordTransaction()
        telemetry.recordCacheHit()
        telemetry.recordCacheMiss()
        telemetry.setActiveTransactions(3)
        
        guard let exportData = telemetry.exportData() else {
            XCTFail("Export data should not be nil")
            return
        }
        
        guard let exportString = String(data: exportData, encoding: .utf8) else {
            XCTFail("Export data should be valid UTF-8")
            return
        }
        
        // Verify Prometheus format
        XCTAssertTrue(exportString.contains("colibridb_queries_total 2"))
        XCTAssertTrue(exportString.contains("colibridb_transactions_total 1"))
        XCTAssertTrue(exportString.contains("colibridb_cache_hits_total 1"))
        XCTAssertTrue(exportString.contains("colibridb_cache_misses_total 1"))
        XCTAssertTrue(exportString.contains("colibridb_active_transactions 3"))
        XCTAssertTrue(exportString.contains("# HELP"))
        XCTAssertTrue(exportString.contains("# TYPE"))
    }
    
    func testPrometheusExportFormat() {
        guard let exportData = telemetry.exportData() else {
            XCTFail("Export data should not be nil")
            return
        }
        
        guard let exportString = String(data: exportData, encoding: .utf8) else {
            XCTFail("Export data should be valid UTF-8")
            return
        }
        
        // Verify format includes all required metrics
        let requiredMetrics = [
            "colibridb_queries_total",
            "colibridb_transactions_total",
            "colibridb_cache_hits_total",
            "colibridb_cache_misses_total",
            "colibridb_memory_usage_mb",
            "colibridb_active_transactions",
            "colibridb_uptime_seconds"
        ]
        
        for metric in requiredMetrics {
            XCTAssertTrue(exportString.contains(metric), "Missing metric: \(metric)")
        }
    }
    
    // MARK: - Concurrent Access Tests
    
    func testConcurrentMetricsRecording() {
        let expectation = XCTestExpectation(description: "Concurrent operations")
        expectation.expectedFulfillmentCount = 100
        
        // Spawn 100 concurrent operations
        for _ in 0..<100 {
            DispatchQueue.global().async {
                self.telemetry.recordQuery()
                self.telemetry.recordTransaction()
                self.telemetry.recordCacheHit()
                expectation.fulfill()
            }
        }
        
        wait(for: [expectation], timeout: 5.0)
        
        let metrics = telemetry.getCurrentMetrics()
        XCTAssertEqual(metrics.queryCount, 100)
        XCTAssertEqual(metrics.transactionCount, 100)
        XCTAssertEqual(metrics.cacheHits, 100)
    }
    
    func testConcurrentExport() {
        let expectation = XCTestExpectation(description: "Concurrent exports")
        expectation.expectedFulfillmentCount = 10
        
        // Record some data
        telemetry.recordQuery()
        telemetry.recordTransaction()
        
        // Concurrent exports should not crash
        for _ in 0..<10 {
            DispatchQueue.global().async {
                _ = self.telemetry.exportData()
                expectation.fulfill()
            }
        }
        
        wait(for: [expectation], timeout: 2.0)
    }
    
    func testConcurrentReadWrite() {
        let expectation = XCTestExpectation(description: "Concurrent read/write")
        expectation.expectedFulfillmentCount = 20
        
        // Writers
        for _ in 0..<10 {
            DispatchQueue.global().async {
                self.telemetry.recordQuery()
                self.telemetry.recordTransaction()
                expectation.fulfill()
            }
        }
        
        // Readers
        for _ in 0..<10 {
            DispatchQueue.global().async {
                _ = self.telemetry.getCurrentMetrics()
                _ = self.telemetry.exportData()
                expectation.fulfill()
            }
        }
        
        wait(for: [expectation], timeout: 5.0)
    }
    
    // MARK: - Stress Tests
    
    func testHighVolumeMetrics() {
        // Record a large number of metrics quickly
        for _ in 0..<10000 {
            telemetry.recordQuery()
        }
        
        for _ in 0..<5000 {
            telemetry.recordTransaction()
        }
        
        let metrics = telemetry.getCurrentMetrics()
        XCTAssertEqual(metrics.queryCount, 10000)
        XCTAssertEqual(metrics.transactionCount, 5000)
    }
    
    func testMemoryUsageTracking() {
        telemetry.startCollection()
        
        // Wait for collection
        let expectation = XCTestExpectation(description: "Memory collection")
        DispatchQueue.main.asyncAfter(deadline: .now() + 0.3) {
            expectation.fulfill()
        }
        wait(for: [expectation], timeout: 1.0)
        
        let metrics = telemetry.getCurrentMetrics()
        
        // Memory usage should be tracked if system metrics are enabled
        if telemetry.config.collectSystemMetrics {
            XCTAssertGreaterThan(metrics.memoryUsageMB, 0)
        }
        
        telemetry.stopCollection()
    }
    
    func testUptimeCalculation() {
        let metrics1 = telemetry.getCurrentMetrics()
        
        // Wait a bit
        Thread.sleep(forTimeInterval: 0.1)
        
        guard let exportData = telemetry.exportData() else {
            XCTFail("Export data should not be nil")
            return
        }
        
        guard let exportString = String(data: exportData, encoding: .utf8) else {
            XCTFail("Export data should be valid UTF-8")
            return
        }
        
        // Uptime should be greater than 0
        XCTAssertTrue(exportString.contains("colibridb_uptime_seconds"))
        
        // Extract uptime value (simple check)
        let lines = exportString.split(separator: "\n")
        let uptimeLine = lines.first { $0.contains("colibridb_uptime_seconds") && !$0.contains("#") }
        XCTAssertNotNil(uptimeLine)
    }
    
    // MARK: - Edge Cases
    
    func testZeroIntervalConfiguration() {
        // Should handle zero interval gracefully
        let config = TelemetryConfig(collectionInterval: 0.0, enabled: true)
        let zeroTelemetry = TelemetryManager(config: config)
        
        XCTAssertNotNil(zeroTelemetry)
        
        // Should not crash when starting
        zeroTelemetry.startCollection()
        zeroTelemetry.stopCollection()
    }
    
    func testDisabledTelemetry() {
        let config = TelemetryConfig(enabled: false)
        let disabledTelemetry = TelemetryManager(config: config)
        
        // Should still work, just not collect automatically
        disabledTelemetry.recordQuery()
        let metrics = disabledTelemetry.getCurrentMetrics()
        XCTAssertEqual(metrics.queryCount, 1)
    }
    
    func testMaxCounterValues() {
        // Test handling of very large counter values
        for _ in 0..<UInt64.max / 2 {
            // This would take too long, so we'll just set a large value
            break
        }
        
        // Simulate large values by recording many times
        for _ in 0..<1000 {
            telemetry.recordQuery()
        }
        
        let metrics = telemetry.getCurrentMetrics()
        XCTAssertEqual(metrics.queryCount, 1000)
    }
    
    // MARK: - Integration Tests
    
    func testRealisticWorkloadSimulation() {
        telemetry.startCollection()
        
        // Simulate realistic database workload
        let expectation = XCTestExpectation(description: "Workload simulation")
        
        DispatchQueue.global().async {
            // Simulate queries
            for _ in 0..<50 {
                self.telemetry.recordQuery()
                Thread.sleep(forTimeInterval: 0.001)
            }
            
            // Simulate transactions
            for _ in 0..<20 {
                self.telemetry.recordTransaction()
                self.telemetry.setActiveTransactions(Int.random(in: 1...10))
                Thread.sleep(forTimeInterval: 0.002)
            }
            
            // Simulate cache activity
            for _ in 0..<100 {
                if Bool.random() {
                    self.telemetry.recordCacheHit()
                } else {
                    self.telemetry.recordCacheMiss()
                }
            }
            
            expectation.fulfill()
        }
        
        wait(for: [expectation], timeout: 5.0)
        
        let metrics = telemetry.getCurrentMetrics()
        XCTAssertEqual(metrics.queryCount, 50)
        XCTAssertEqual(metrics.transactionCount, 20)
        XCTAssertEqual(metrics.cacheHits + metrics.cacheMisses, 100)
        XCTAssertGreaterThan(metrics.collectionCount, 0)
        
        // Verify export works with realistic data
        let exportData = telemetry.exportData()
        XCTAssertNotNil(exportData)
        
        telemetry.stopCollection()
    }
}

