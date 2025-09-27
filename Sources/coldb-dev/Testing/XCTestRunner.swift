//
//  XCTestRunner.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-27.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: XCTest runner integration for continuous testing system.

import Foundation
import os.log

/// Runner for XCTest tests integration
public final class XCTestRunner {
    private let logger = Logger(subsystem: "com.colibridb.testing", category: "xctest")
    private let testBundlePath: String
    private let outputDirectory: String
    
    public init(testBundlePath: String, outputDirectory: String) {
        self.testBundlePath = testBundlePath
        self.outputDirectory = outputDirectory
    }
    
    /// Runs all XCTest tests
    public func runAllTests() -> XCTestResult {
        logger.info("Starting XCTest execution")
        
        let startTime = Date()
        let result = runXCTest()
        let endTime = Date()
        let duration = endTime.timeIntervalSince(startTime)
        
        logger.info("XCTest completed: \(result.passedTests)/\(result.totalTests) passed in \(String(format: "%.2f", duration))s")
        
        return XCTestResult(
            totalTests: result.totalTests,
            passedTests: result.passedTests,
            failedTests: result.failedTests,
            duration: duration,
            testResults: result.testResults,
            timestamp: endTime
        )
    }
    
    /// Runs specific test classes
    public func runTestClasses(_ classes: [String]) -> XCTestResult {
        logger.info("Running specific test classes: \(classes.joined(separator: ", "))")
        
        let startTime = Date()
        let result = runXCTest(testClasses: classes)
        let endTime = Date()
        let duration = endTime.timeIntervalSince(startTime)
        
        return XCTestResult(
            totalTests: result.totalTests,
            passedTests: result.passedTests,
            failedTests: result.failedTests,
            duration: duration,
            testResults: result.testResults,
            timestamp: endTime
        )
    }
    
    /// Runs tests by category
    public func runTestsByCategory(_ category: TestCategory) -> XCTestResult {
        let testClasses = getTestClasses(for: category)
        return runTestClasses(testClasses)
    }
    
    // MARK: - Private Methods
    
    private func runXCTest(testClasses: [String] = []) -> XCTestExecutionResult {
        let process = Process()
        process.executableURL = URL(fileURLWithPath: "/usr/bin/xcodebuild")
        
        var arguments = [
            "test",
            "-scheme", "ColibriCore",
            "-destination", "platform=macOS",
            "-resultBundlePath", "\(outputDirectory)/xctest-results.xcresult"
        ]
        
        if !testClasses.isEmpty {
            arguments.append("-only-testing:ColibriCoreTests/\(testClasses.joined(separator: ":"))")
        }
        
        process.arguments = arguments
        
        let pipe = Pipe()
        process.standardOutput = pipe
        process.standardError = pipe
        
        do {
            try process.run()
            process.waitUntilExit()
            
            let data = pipe.fileHandleForReading.readDataToEndOfFile()
            let output = String(data: data, encoding: .utf8) ?? ""
            
            return parseXCTestOutput(output)
        } catch {
            logger.error("Failed to run XCTest: \(error.localizedDescription)")
            return XCTestExecutionResult(
                totalTests: 0,
                passedTests: 0,
                failedTests: 0,
                testResults: []
            )
        }
    }
    
    private func parseXCTestOutput(_ output: String) -> XCTestExecutionResult {
        var totalTests = 0
        var passedTests = 0
        var failedTests = 0
        var testResults: [XCTestTestResult] = []
        
        let lines = output.components(separatedBy: .newlines)
        
        for line in lines {
            if line.contains("Test Case") {
                if line.contains("started") {
                    totalTests += 1
                } else if line.contains("passed") {
                    passedTests += 1
                    let testName = extractTestName(from: line)
                    testResults.append(XCTestTestResult(
                        name: testName,
                        success: true,
                        duration: 0.0,
                        error: nil
                    ))
                } else if line.contains("failed") {
                    failedTests += 1
                    let testName = extractTestName(from: line)
                    testResults.append(XCTestTestResult(
                        name: testName,
                        success: false,
                        duration: 0.0,
                        error: "Test failed"
                    ))
                }
            }
        }
        
        return XCTestExecutionResult(
            totalTests: totalTests,
            passedTests: passedTests,
            failedTests: failedTests,
            testResults: testResults
        )
    }
    
    private func extractTestName(from line: String) -> String {
        // Extract test name from XCTest output line
        let components = line.components(separatedBy: " ")
        for component in components {
            if component.contains("Test") && component.contains("(") {
                return component
            }
        }
        return "Unknown Test"
    }
    
    private func getTestClasses(for category: TestCategory) -> [String] {
        switch category {
        case .unit:
            return [
                "LRUBufferPoolTests",
                "LockManagerTests",
                "ARTIndexTests",
                "FileBPlusTreeIndexTests"
            ]
        case .integration:
            return [
                "DatabaseMVCCIntegrationTests",
                "DatabaseTwoPhaseCommitTests",
                "PlannerExecutorTests"
            ]
        case .performance:
            return [
                "FileWALAndHeapTests",
                "PolicyAndMaintenanceTests"
            ]
        case .all:
            return [
                "LRUBufferPoolTests",
                "LockManagerTests",
                "ARTIndexTests",
                "FileBPlusTreeIndexTests",
                "DatabaseMVCCIntegrationTests",
                "DatabaseTwoPhaseCommitTests",
                "PlannerExecutorTests",
                "FileWALAndHeapTests",
                "PolicyAndMaintenanceTests"
            ]
        }
    }
}

// MARK: - Supporting Types

public enum TestCategory {
    case unit
    case integration
    case performance
    case all
}

public struct XCTestResult {
    public let totalTests: Int
    public let passedTests: Int
    public let failedTests: Int
    public let duration: TimeInterval
    public let testResults: [XCTestTestResult]
    public let timestamp: Date
    
    public var successRate: Double {
        guard totalTests > 0 else { return 0.0 }
        return Double(passedTests) / Double(totalTests)
    }
}

public struct XCTestTestResult {
    public let name: String
    public let success: Bool
    public let duration: TimeInterval
    public let error: String?
}

private struct XCTestExecutionResult {
    let totalTests: Int
    let passedTests: Int
    let failedTests: Int
    let testResults: [XCTestTestResult]
}
