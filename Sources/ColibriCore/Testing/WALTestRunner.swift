//
//  WALTestRunner.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-27.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: WAL test runner with reporting

import Foundation

/// WAL test runner with comprehensive reporting
public class WALTestRunner {
    
    private let outputPath: String?
    private let verbose: Bool
    
    public init(outputPath: String? = nil, verbose: Bool = false) {
        self.outputPath = outputPath
        self.verbose = verbose
    }
    
    /// Run all WAL tests and generate report
    public func runTests() {
        print("🚀 Starting WAL Acceptance Tests...")
        print("=" * 50)
        
        let testSuite = WALTests()
        let results = testSuite.runAllTests()
        
        // Generate and display summary
        let summary = results.summary()
        print(summary)
        
        // Save detailed report if output path specified
        if let outputPath = outputPath {
            saveDetailedReport(results: results, to: outputPath)
        }
        
        // Generate metrics report
        generateMetricsReport(results: results)
        
        // Exit with appropriate code
        let allPassed = results.allSatisfy { $0.passed }
        if !allPassed {
            exit(1)
        }
    }
    
    private func saveDetailedReport(results: [WALTestResult], to path: String) {
        do {
            let report = generateDetailedReport(results: results)
            try report.write(toFile: path, atomically: true, encoding: .utf8)
            print("📊 Detailed report saved to: \(path)")
        } catch {
            print("⚠️  Failed to save report: \(error)")
        }
    }
    
    private func generateDetailedReport(results: [WALTestResult]) -> String {
        var report = """
        WAL Acceptance Test Report
        ==========================
        Generated: \(Date())
        
        """
        
        for result in results {
            report += """
            
            Test: \(result.testName)
            Status: \(result.passed ? "PASSED" : "FAILED")
            Duration: \(String(format: "%.3f", result.duration))s
            Message: \(result.message)
            
            Metrics:
            - Records Written: \(result.metrics.recordsWritten)
            - Records Read: \(result.metrics.recordsRead)
            - Bytes Written: \(result.metrics.bytesWritten)
            - Group Commit Batches: \(result.metrics.groupCommitBatches)
            - Average Batch Size: \(String(format: "%.2f", result.metrics.averageBatchSize))
            - Fsyncs: \(result.metrics.fsyncs)
            - Recovered Records: \(result.metrics.recoveredRecords)
            - Compression Ratio: \(String(format: "%.2f", result.metrics.compressionRatio))
            
            """
        }
        
        return report
    }
    
    private func generateMetricsReport(results: [WALTestResult]) {
        let totalRecordsWritten = results.reduce(0) { $0 + $1.metrics.recordsWritten }
        let totalBatches = results.reduce(0) { $0 + $1.metrics.groupCommitBatches }
        let averageCompressionRatio = results.filter { $0.metrics.compressionRatio < 1.0 }
                                            .map { $0.metrics.compressionRatio }
                                            .reduce(0, +) / Double(results.count)
        
        print("""
        
        📈 Overall Metrics:
        ==================
        Total WAL Records Written: \(totalRecordsWritten)
        Total Group Commit Batches: \(totalBatches)
        Average Compression Ratio: \(String(format: "%.2f", averageCompressionRatio))
        
        """)
    }
}

// MARK: - String Repetition Helper

extension String {
    static func *(lhs: String, rhs: Int) -> String {
        return String(repeating: lhs, count: rhs)
    }
}
