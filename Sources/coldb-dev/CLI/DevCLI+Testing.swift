//
//  DevCLI+Testing.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Testing commands for development CLI.

import Foundation
import ColibriCore

extension DevCLI {
    
    private static var testRunner: TestRunner?
    
    /// Handles testing-related commands
    mutating func handleTestingCommands(_ trimmed: String) {
        if trimmed.hasPrefix("\\test run") {
            handleTestRun(trimmed)
            return
        }
        
        if trimmed.hasPrefix("\\test unit") {
            handleTestUnit(trimmed)
            return
        }
        
        if trimmed.hasPrefix("\\test integration") {
            handleTestIntegration(trimmed)
            return
        }
        
        if trimmed.hasPrefix("\\test performance") {
            handleTestPerformance(trimmed)
            return
        }
        
        if trimmed.hasPrefix("\\test stress") {
            handleTestStress(trimmed)
            return
        }
        
        if trimmed.hasPrefix("\\test auto") {
            handleTestAuto(trimmed)
            return
        }
        
        if trimmed.hasPrefix("\\test regression") {
            handleTestRegression(trimmed)
            return
        }
        
        if trimmed.hasPrefix("\\test memory") {
            handleTestMemory(trimmed)
            return
        }
    }
    
    // MARK: - Test Commands
    
    /// Run all tests
    private func handleTestRun(_ trimmed: String) {
        if Self.testRunner == nil {
            Self.testRunner = TestRunner(database: db)
        }
        
        print("Running all tests...")
        let startTime = Date()
        
        let result = Self.testRunner!.runAllTests()
        
        let endTime = Date()
        let totalDuration = endTime.timeIntervalSince(startTime)
        
        print("=== Test Results ===")
        print("Total Tests: \(result.totalTests)")
        print("Passed: \(result.passedTests)")
        print("Failed: \(result.failedTests)")
        print("Success Rate: \(String(format: "%.1f", result.successRate * 100))%")
        print("Duration: \(String(format: "%.2f", totalDuration))s")
        print("Timestamp: \(result.timestamp)")
        
        if result.failedTests > 0 {
            print("\nFailed Tests:")
            for testResult in result.results where !testResult.success {
                print("  ❌ \(testResult.name): \(testResult.error?.localizedDescription ?? "Unknown error")")
            }
        }
        
        if result.passedTests > 0 {
            print("\nPassed Tests:")
            for testResult in result.results where testResult.success {
                print("  ✅ \(testResult.name) (\(String(format: "%.4f", testResult.duration))s)")
            }
        }
    }
    
    /// Run unit tests
    private func handleTestUnit(_ trimmed: String) {
        if Self.testRunner == nil {
            Self.testRunner = TestRunner(database: db)
        }
        
        print("Running unit tests...")
        let startTime = Date()
        
        let results = Self.testRunner!.runUnitTests()
        
        let endTime = Date()
        let totalDuration = endTime.timeIntervalSince(startTime)
        
        print("=== Unit Test Results ===")
        let passed = results.filter { $0.success }.count
        let failed = results.filter { !$0.success }.count
        
        print("Total Tests: \(results.count)")
        print("Passed: \(passed)")
        print("Failed: \(failed)")
        print("Duration: \(String(format: "%.2f", totalDuration))s")
        
        if failed > 0 {
            print("\nFailed Tests:")
            for result in results where !result.success {
                print("  ❌ \(result.name): \(result.error?.localizedDescription ?? "Unknown error")")
            }
        }
    }
    
    /// Run integration tests
    private func handleTestIntegration(_ trimmed: String) {
        if Self.testRunner == nil {
            Self.testRunner = TestRunner(database: db)
        }
        
        print("Running integration tests...")
        let startTime = Date()
        
        let results = Self.testRunner!.runIntegrationTests()
        
        let endTime = Date()
        let totalDuration = endTime.timeIntervalSince(startTime)
        
        print("=== Integration Test Results ===")
        let passed = results.filter { $0.success }.count
        let failed = results.filter { !$0.success }.count
        
        print("Total Tests: \(results.count)")
        print("Passed: \(passed)")
        print("Failed: \(failed)")
        print("Duration: \(String(format: "%.2f", totalDuration))s")
        
        if failed > 0 {
            print("\nFailed Tests:")
            for result in results where !result.success {
                print("  ❌ \(result.name): \(result.error?.localizedDescription ?? "Unknown error")")
            }
        }
    }
    
    /// Run performance tests
    private func handleTestPerformance(_ trimmed: String) {
        if Self.testRunner == nil {
            Self.testRunner = TestRunner(database: db)
        }
        
        print("Running performance tests...")
        let startTime = Date()
        
        let results = Self.testRunner!.runPerformanceTests()
        
        let endTime = Date()
        let totalDuration = endTime.timeIntervalSince(startTime)
        
        print("=== Performance Test Results ===")
        let passed = results.filter { $0.success }.count
        let failed = results.filter { !$0.success }.count
        
        print("Total Tests: \(results.count)")
        print("Passed: \(passed)")
        print("Failed: \(failed)")
        print("Duration: \(String(format: "%.2f", totalDuration))s")
        
        if failed > 0 {
            print("\nFailed Tests:")
            for result in results where !result.success {
                print("  ❌ \(result.name): \(result.error?.localizedDescription ?? "Unknown error")")
            }
        }
        
        if passed > 0 {
            print("\nPerformance Results:")
            for result in results where result.success {
                print("  ✅ \(result.name): \(String(format: "%.4f", result.duration))s")
            }
        }
    }
    
    /// Run stress tests
    private func handleTestStress(_ trimmed: String) {
        if Self.testRunner == nil {
            Self.testRunner = TestRunner(database: db)
        }
        
        print("Running stress tests...")
        print("Warning: This may take several minutes and use significant resources")
        
        let startTime = Date()
        
        let results = Self.testRunner!.runStressTests()
        
        let endTime = Date()
        let totalDuration = endTime.timeIntervalSince(startTime)
        
        print("=== Stress Test Results ===")
        let passed = results.filter { $0.success }.count
        let failed = results.filter { !$0.success }.count
        
        print("Total Tests: \(results.count)")
        print("Passed: \(passed)")
        print("Failed: \(failed)")
        print("Duration: \(String(format: "%.2f", totalDuration))s")
        
        if failed > 0 {
            print("\nFailed Tests:")
            for result in results where !result.success {
                print("  ❌ \(result.name): \(result.error?.localizedDescription ?? "Unknown error")")
            }
        }
        
        if passed > 0 {
            print("\nStress Test Results:")
            for result in results where result.success {
                print("  ✅ \(result.name): \(String(format: "%.4f", result.duration))s")
            }
        }
    }
    
    /// Run automated tests
    private func handleTestAuto(_ trimmed: String) {
        let parts = trimmed.split(separator: " ")
        let interval = Double(parts.first(where: { $0.hasPrefix("interval=") })?.dropFirst("interval=".count) ?? "300.0") ?? 300.0 // 5 minutes default
        
        print("Starting automated test runner...")
        print("Tests will run every \(interval) seconds")
        print("Press Ctrl+C to stop")
        
        // Start automated testing
        startAutomatedTesting(interval: interval)
    }
    
    /// Run regression tests
    private func handleTestRegression(_ trimmed: String) {
        print("Running regression test suite...")
        
        if Self.testRunner == nil {
            Self.testRunner = TestRunner(database: db)
        }
        
        let startTime = Date()
        
        // Run a subset of tests that are most likely to catch regressions
        let unitResults = Self.testRunner!.runUnitTests()
        let integrationResults = Self.testRunner!.runIntegrationTests()
        
        let endTime = Date()
        let totalDuration = endTime.timeIntervalSince(startTime)
        
        let allResults = unitResults + integrationResults
        let passed = allResults.filter { $0.success }.count
        let failed = allResults.filter { !$0.success }.count
        
        print("=== Regression Test Results ===")
        print("Total Tests: \(allResults.count)")
        print("Passed: \(passed)")
        print("Failed: \(failed)")
        print("Duration: \(String(format: "%.2f", totalDuration))s")
        
        if failed > 0 {
            print("\nRegression Detected!")
            print("Failed Tests:")
            for result in allResults where !result.success {
                print("  ❌ \(result.name): \(result.error?.localizedDescription ?? "Unknown error")")
            }
        } else {
            print("✅ No regressions detected")
        }
    }
    
    /// Run memory leak tests
    private func handleTestMemory(_ trimmed: String) {
        print("Running memory leak tests...")
        
        let debugTools = DebugTools(database: db)
        let initialMemory = debugTools.analyzeMemory()
        
        print("Initial Memory: \(String(format: "%.2f", initialMemory.residentSizeMB)) MB")
        
        // Run memory-intensive operations
        for i in 1...10 {
            print("Iteration \(i)/10...")
            
            // Create and destroy tables
            for j in 1...100 {
                try? db.createTable("memory_test_\(i)_\(j)")
                try? db.dropTable("memory_test_\(i)_\(j)")
            }
            
            // Insert and delete data
            try? db.createTable("memory_data_\(i)")
            for k in 1...1000 {
                let row: Row = ["id": .int(Int64(k)), "value": .string("Value \(k)")]
                _ = try? db.insert(into: "memory_data_\(i)", row: row)
            }
            try? db.dropTable("memory_data_\(i)")
            
            // Check memory usage
            let currentMemory = debugTools.analyzeMemory()
            let memoryIncrease = currentMemory.residentSize - initialMemory.residentSize
            print("  Memory: \(String(format: "%.2f", currentMemory.residentSizeMB)) MB (+\(String(format: "%.2f", Double(memoryIncrease) / 1024.0 / 1024.0)) MB)")
        }
        
        let finalMemory = debugTools.analyzeMemory()
        let totalIncrease = finalMemory.residentSize - initialMemory.residentSize
        
        print("\n=== Memory Test Results ===")
        print("Initial Memory: \(String(format: "%.2f", initialMemory.residentSizeMB)) MB")
        print("Final Memory: \(String(format: "%.2f", finalMemory.residentSizeMB)) MB")
        print("Memory Increase: \(String(format: "%.2f", Double(totalIncrease) / 1024.0 / 1024.0)) MB")
        
        if Double(totalIncrease) / 1024.0 / 1024.0 > 50.0 {
            print("⚠️  Potential memory leak detected (>50MB increase)")
        } else {
            print("✅ No significant memory leak detected")
        }
    }
    
    // MARK: - Helper Methods
    
    private func startAutomatedTesting(interval: TimeInterval) {
        Timer.scheduledTimer(withTimeInterval: interval, repeats: true) { _ in
            print("\n=== Automated Test Run ===")
            print("Timestamp: \(Date())")
            
            let runner = TestRunner(database: self.db)
            let result = runner.runAllTests()
            
            print("Results: \(result.passedTests)/\(result.totalTests) passed")
            
            if result.failedTests > 0 {
                print("❌ Test failures detected!")
                for testResult in result.results where !testResult.success {
                    print("  - \(testResult.name): \(testResult.error?.localizedDescription ?? "Unknown error")")
                }
            } else {
                print("✅ All tests passed")
            }
        }
    }
}
