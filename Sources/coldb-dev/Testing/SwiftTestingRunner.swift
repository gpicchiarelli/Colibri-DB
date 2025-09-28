//
//  SwiftTestingRunner.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-09-27.
//
// ColibrDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Swift Testing runner integration for continuous testing system.

import Foundation
import os.log

/// Runner for Swift Testing framework integration
public final class SwiftTestingRunner {
    private let logger = Logger(subsystem: "com.colibridb.testing", category: "swift-testing")
    private let testExecutablePath: String
    private let outputDirectory: String
    
    public init(testExecutablePath: String, outputDirectory: String) {
        self.testExecutablePath = testExecutablePath
        self.outputDirectory = outputDirectory
    }
    
    /// Runs all Swift Testing tests
    public func runAllTests() -> SwiftTestingResult {
        logger.info("Starting Swift Testing execution")
        
        let startTime = Date()
        let result = runSwiftTesting()
        let endTime = Date()
        let duration = endTime.timeIntervalSince(startTime)
        
        logger.info("Swift Testing completed: \(result.passedTests)/\(result.totalTests) passed in \(String(format: "%.2f", duration))s")
        
        return SwiftTestingResult(
            totalTests: result.totalTests,
            passedTests: result.passedTests,
            failedTests: result.failedTests,
            duration: duration,
            testResults: result.testResults,
            timestamp: endTime
        )
    }
    
    /// Runs specific test suites
    public func runTestSuites(_ suites: [String]) -> SwiftTestingResult {
        logger.info("Running specific test suites: \(suites.joined(separator: ", "))")
        
        let startTime = Date()
        let result = runSwiftTesting(testSuites: suites)
        let endTime = Date()
        let duration = endTime.timeIntervalSince(startTime)
        
        return SwiftTestingResult(
            totalTests: result.totalTests,
            passedTests: result.passedTests,
            failedTests: result.failedTests,
            duration: duration,
            testResults: result.testResults,
            timestamp: endTime
        )
    }
    
    /// Runs tests by category
    public func runTestsByCategory(_ category: TestCategory) -> SwiftTestingResult {
        let testSuites = getTestSuites(for: category)
        return runTestSuites(testSuites)
    }
    
    // MARK: - Private Methods
    
    private func runSwiftTesting(testSuites: [String] = []) -> SwiftTestingExecutionResult {
        let process = Process()
        process.executableURL = URL(fileURLWithPath: testExecutablePath)
        
        var arguments = ["--output", "json"]
        
        if !testSuites.isEmpty {
            arguments.append(contentsOf: testSuites.flatMap { ["--filter", $0] })
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
            
            return parseSwiftTestingOutput(output)
        } catch {
            logger.error("Failed to run Swift Testing: \(error.localizedDescription)")
            return SwiftTestingExecutionResult(
                totalTests: 0,
                passedTests: 0,
                failedTests: 0,
                testResults: []
            )
        }
    }
    
    private func parseSwiftTestingOutput(_ output: String) -> SwiftTestingExecutionResult {
        var totalTests = 0
        var passedTests = 0
        var failedTests = 0
        var testResults: [SwiftTestingTestResult] = []
        
        // Parse JSON output from Swift Testing
        guard let data = output.data(using: .utf8) else {
            logger.error("Failed to parse Swift Testing output")
            return SwiftTestingExecutionResult(
                totalTests: 0,
                passedTests: 0,
                failedTests: 0,
                testResults: []
            )
        }
        
        do {
            let json = try JSONSerialization.jsonObject(with: data, options: [])
            if let jsonDict = json as? [String: Any] {
                if let tests = jsonDict["tests"] as? [[String: Any]] {
                    for test in tests {
                        totalTests += 1
                        
                        let name = test["name"] as? String ?? "Unknown Test"
                        let status = test["status"] as? String ?? "unknown"
                        let duration = test["duration"] as? Double ?? 0.0
                        
                        let success = (status == "passed")
                        if success {
                            passedTests += 1
                        } else {
                            failedTests += 1
                        }
                        
                        testResults.append(SwiftTestingTestResult(
                            name: name,
                            success: success,
                            duration: duration,
                            error: success ? nil : "Test failed"
                        ))
                    }
                }
            }
        } catch {
            logger.error("Failed to parse Swift Testing JSON: \(error.localizedDescription)")
            // Fallback to line-by-line parsing
            return parseSwiftTestingOutputFallback(output)
        }
        
        return SwiftTestingExecutionResult(
            totalTests: totalTests,
            passedTests: passedTests,
            failedTests: failedTests,
            testResults: testResults
        )
    }
    
    private func parseSwiftTestingOutputFallback(_ output: String) -> SwiftTestingExecutionResult {
        var totalTests = 0
        var passedTests = 0
        var failedTests = 0
        var testResults: [SwiftTestingTestResult] = []
        
        let lines = output.components(separatedBy: .newlines)
        
        for line in lines {
            if line.contains("Test") && (line.contains("passed") || line.contains("failed")) {
                totalTests += 1
                
                let success = line.contains("passed")
                if success {
                    passedTests += 1
                } else {
                    failedTests += 1
                }
                
                let testName = extractTestName(from: line)
                testResults.append(SwiftTestingTestResult(
                    name: testName,
                    success: success,
                    duration: 0.0,
                    error: success ? nil : "Test failed"
                ))
            }
        }
        
        return SwiftTestingExecutionResult(
            totalTests: totalTests,
            passedTests: passedTests,
            failedTests: failedTests,
            testResults: testResults
        )
    }
    
    private func extractTestName(from line: String) -> String {
        // Extract test name from Swift Testing output line
        let components = line.components(separatedBy: " ")
        for component in components {
            if component.contains("Test") {
                return component
            }
        }
        return "Unknown Test"
    }
    
    private func getTestSuites(for category: TestCategory) -> [String] {
        switch category {
        case .unit:
            return [
                "DatabaseMVCCIntegrationTests",
                "DatabaseTwoPhaseCommitTests"
            ]
        case .integration:
            return [
                "PlannerExecutorTests",
                "FileWALAndHeapTests"
            ]
        case .performance:
            return [
                "PolicyAndMaintenanceTests"
            ]
        case .all:
            return [
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

public struct SwiftTestingResult {
    public let totalTests: Int
    public let passedTests: Int
    public let failedTests: Int
    public let duration: TimeInterval
    public let testResults: [SwiftTestingTestResult]
    public let timestamp: Date
    
    public var successRate: Double {
        guard totalTests > 0 else { return 0.0 }
        return Double(passedTests) / Double(totalTests)
    }
}

public struct SwiftTestingTestResult {
    public let name: String
    public let success: Bool
    public let duration: TimeInterval
    public let error: String?
}

private struct SwiftTestingExecutionResult {
    let totalTests: Int
    let passedTests: Int
    let failedTests: Int
    let testResults: [SwiftTestingTestResult]
}
