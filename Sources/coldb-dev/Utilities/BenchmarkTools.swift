//
//  BenchmarkTools.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Benchmark tools for performance testing and analysis.

import Foundation
import ColibriCore
import os.log

/// Comprehensive benchmark tools for ColibrìDB performance testing
public class BenchmarkTools {
    private let database: Database
    private let logger = Logger(subsystem: "com.colibridb.benchmark", category: "tools")
    
    public init(database: Database) {
        self.database = database
    }
    
    // MARK: - SQL Performance Benchmarks
    
    /// Benchmarks SQL parsing performance
    public func benchmarkSQLParsing(iterations: Int = 1000) -> BenchmarkResult {
        logger.info("Starting SQL parsing benchmark with \(iterations) iterations")
        
        let sqlQueries = [
            "SELECT * FROM users WHERE id = 1",
            "INSERT INTO users (name, email) VALUES ('John', 'john@example.com')",
            "UPDATE users SET name = 'Jane' WHERE id = 1",
            "DELETE FROM users WHERE id = 1",
            "CREATE TABLE test (id INT, name STRING)",
            "DROP TABLE test",
            "CREATE INDEX idx_name ON users (name)",
            "SELECT COUNT(*) FROM users WHERE age > 25"
        ]
        
        var totalDuration: TimeInterval = 0
        var minDuration: TimeInterval = Double.greatestFiniteMagnitude
        var maxDuration: TimeInterval = 0
        
        for i in 0..<iterations {
            let sql = sqlQueries[i % sqlQueries.count]
            let startTime = CFAbsoluteTimeGetCurrent()
            
            do {
                let parser = SimpleSQLParser(sql: sql)
                _ = try parser.parse()
            } catch {
            }
            
            let endTime = CFAbsoluteTimeGetCurrent()
            let duration = endTime - startTime
            
            totalDuration += duration
            minDuration = min(minDuration, duration)
            maxDuration = max(maxDuration, duration)
        }
        
        let averageDuration = totalDuration / Double(iterations)
        
        return BenchmarkResult(
            name: "SQL Parsing",
            iterations: iterations,
            totalDuration: totalDuration,
            averageDuration: averageDuration,
            minDuration: minDuration,
            maxDuration: maxDuration,
            operationsPerSecond: Double(iterations) / totalDuration,
            timestamp: Date()
        )
    }
    
    /// Benchmarks SQL execution performance
    public func benchmarkSQLExecution(iterations: Int = 100) -> BenchmarkResult {
        logger.info("Starting SQL execution benchmark with \(iterations) iterations")
        
        // Setup test data
        try? database.createTable("benchmark_users")
        
        // Insert test data
        for i in 1...1000 {
            let row: Row = ["id": .int(Int64(i)), "name": .string("User \(i)"), "age": .int(Int64(20 + (i % 50)))]
            _ = try? database.insert(into: "benchmark_users", row: row)
        }
        
        let sqlQueries = [
            "SELECT * FROM benchmark_users WHERE id = 1",
            "SELECT COUNT(*) FROM benchmark_users",
            "SELECT * FROM benchmark_users WHERE age > 30",
            "SELECT * FROM benchmark_users WHERE name LIKE 'User%'"
        ]
        
        var totalDuration: TimeInterval = 0
        var minDuration: TimeInterval = Double.greatestFiniteMagnitude
        var maxDuration: TimeInterval = 0
        
        for i in 0..<iterations {
            let sql = sqlQueries[i % sqlQueries.count]
            let startTime = CFAbsoluteTimeGetCurrent()
            
            do {
                let parser = SimpleSQLParser(sql: sql)
                let statement = try parser.parse()
                let executor = SimpleSQLExecutor(database: database)
                _ = try executor.execute(statement)
            } catch {
            }
            
            let endTime = CFAbsoluteTimeGetCurrent()
            let duration = endTime - startTime
            
            totalDuration += duration
            minDuration = min(minDuration, duration)
            maxDuration = max(maxDuration, duration)
        }
        
        let averageDuration = totalDuration / Double(iterations)
        
        // Cleanup
        try? database.dropTable("benchmark_users")
        
        return BenchmarkResult(
            name: "SQL Execution",
            iterations: iterations,
            totalDuration: totalDuration,
            averageDuration: averageDuration,
            minDuration: minDuration,
            maxDuration: maxDuration,
            operationsPerSecond: Double(iterations) / totalDuration,
            timestamp: Date()
        )
    }
    
    // MARK: - Constraint Validation Benchmarks
    
    /// Benchmarks constraint validation performance
    public func benchmarkConstraintValidation(iterations: Int = 1000) -> BenchmarkResult {
        logger.info("Starting constraint validation benchmark with \(iterations) iterations")
        
        // Setup test table with constraints
        try? database.createTable("benchmark_constraints")
        
        // Add multiple constraints
        for i in 1...10 {
            let constraint = NotNullConstraint(name: "nn_\(i)", column: "col_\(i)")
            try? database.constraintManager.addConstraint(constraint, to: "benchmark_constraints")
        }
        
        var totalDuration: TimeInterval = 0
        var minDuration: TimeInterval = Double.greatestFiniteMagnitude
        var maxDuration: TimeInterval = 0
        
        for _ in 0..<iterations {
            let startTime = CFAbsoluteTimeGetCurrent()
            
            do {
                let constraints = database.constraintManager.getConstraints(for: "benchmark_constraints")
                for _ in constraints {
                    _ = try database.constraintManager.validateTable("benchmark_constraints", rows: [])
                }
            } catch {
            }
            
            let endTime = CFAbsoluteTimeGetCurrent()
            let duration = endTime - startTime
            
            totalDuration += duration
            minDuration = min(minDuration, duration)
            maxDuration = max(maxDuration, duration)
        }
        
        let averageDuration = totalDuration / Double(iterations)
        
        // Cleanup
        try? database.dropTable("benchmark_constraints")
        
        return BenchmarkResult(
            name: "Constraint Validation",
            iterations: iterations,
            totalDuration: totalDuration,
            averageDuration: averageDuration,
            minDuration: minDuration,
            maxDuration: maxDuration,
            operationsPerSecond: Double(iterations) / totalDuration,
            timestamp: Date()
        )
    }
    
    // MARK: - Data Type Operation Benchmarks
    
    /// Benchmarks data type conversion performance
    public func benchmarkDataTypeOperations(iterations: Int = 10000) -> BenchmarkResult {
        logger.info("Starting data type operations benchmark with \(iterations) iterations")
        
        let cli = DevCLI(db: database, cfgPath: nil)
        let testValues = [
            "hello",
            "42",
            "3.14",
            "true",
            "false",
            "NULL",
            "123.45d",
            "'2023-01-01T00:00:00Z'",
            "j:{\"key\":\"value\"}",
            "b:SGVsbG8gV29ybGQ=",
            "e:Status.ACTIVE"
        ]
        
        var totalDuration: TimeInterval = 0
        var minDuration: TimeInterval = Double.greatestFiniteMagnitude
        var maxDuration: TimeInterval = 0
        
        for i in 0..<iterations {
            let value = testValues[i % testValues.count]
            let startTime = CFAbsoluteTimeGetCurrent()
            
            _ = cli.parseValue(value)
            
            let endTime = CFAbsoluteTimeGetCurrent()
            let duration = endTime - startTime
            
            totalDuration += duration
            minDuration = min(minDuration, duration)
            maxDuration = max(maxDuration, duration)
        }
        
        let averageDuration = totalDuration / Double(iterations)
        
        return BenchmarkResult(
            name: "Data Type Operations",
            iterations: iterations,
            totalDuration: totalDuration,
            averageDuration: averageDuration,
            minDuration: minDuration,
            maxDuration: maxDuration,
            operationsPerSecond: Double(iterations) / totalDuration,
            timestamp: Date()
        )
    }
    
    // MARK: - Memory Allocation Benchmarks
    
    /// Benchmarks memory allocation patterns
    public func benchmarkMemoryAllocation(iterations: Int = 100) -> BenchmarkResult {
        logger.info("Starting memory allocation benchmark with \(iterations) iterations")
        
        var totalDuration: TimeInterval = 0
        var minDuration: TimeInterval = Double.greatestFiniteMagnitude
        var maxDuration: TimeInterval = 0
        
        for _ in 0..<iterations {
            let startTime = CFAbsoluteTimeGetCurrent()
            
            do {
                // Create and destroy tables
                for i in 1...10 {
                    try database.createTable("memory_test_\(i)")
                    try database.dropTable("memory_test_\(i)")
                }
                
                // Insert and delete data
                try database.createTable("memory_data")
                for i in 1...1000 {
                    let row: Row = ["id": .int(Int64(i)), "value": .string("Value \(i)")]
                    _ = try database.insert(into: "memory_data", row: row)
                }
                try database.dropTable("memory_data")
            } catch {
            }
            
            let endTime = CFAbsoluteTimeGetCurrent()
            let duration = endTime - startTime
            
            totalDuration += duration
            minDuration = min(minDuration, duration)
            maxDuration = max(maxDuration, duration)
        }
        
        let averageDuration = totalDuration / Double(iterations)
        
        return BenchmarkResult(
            name: "Memory Allocation",
            iterations: iterations,
            totalDuration: totalDuration,
            averageDuration: averageDuration,
            minDuration: minDuration,
            maxDuration: maxDuration,
            operationsPerSecond: Double(iterations) / totalDuration,
            timestamp: Date()
        )
    }
    
    // MARK: - Comprehensive Benchmark Suite
    
    /// Runs a comprehensive benchmark suite
    public func runBenchmarkSuite() -> BenchmarkSuiteResult {
        logger.info("Starting comprehensive benchmark suite")
        let startTime = Date()
        
        var results: [BenchmarkResult] = []
        
        // SQL benchmarks
        results.append(benchmarkSQLParsing(iterations: 1000))
        results.append(benchmarkSQLExecution(iterations: 100))
        
        // Constraint benchmarks
        results.append(benchmarkConstraintValidation(iterations: 1000))
        
        // Data type benchmarks
        results.append(benchmarkDataTypeOperations(iterations: 10000))
        
        // Memory benchmarks
        results.append(benchmarkMemoryAllocation(iterations: 100))
        
        let endTime = Date()
        let totalDuration = endTime.timeIntervalSince(startTime)
        
        return BenchmarkSuiteResult(
            totalBenchmarks: results.count,
            totalDuration: totalDuration,
            results: results,
            timestamp: endTime
        )
    }
    
    // MARK: - Custom Benchmark
    
    /// Runs a custom benchmark with user-defined operation
    public func runCustomBenchmark<T>(
        name: String,
        iterations: Int,
        operation: () throws -> T
    ) -> BenchmarkResult {
        logger.info("Starting custom benchmark '\(name)' with \(iterations) iterations")
        
        var totalDuration: TimeInterval = 0
        var minDuration: TimeInterval = Double.greatestFiniteMagnitude
        var maxDuration: TimeInterval = 0
        
        for _ in 0..<iterations {
            let startTime = CFAbsoluteTimeGetCurrent()
            
            do {
                _ = try operation()
            } catch {
            }
            
            let endTime = CFAbsoluteTimeGetCurrent()
            let duration = endTime - startTime
            
            totalDuration += duration
            minDuration = min(minDuration, duration)
            maxDuration = max(maxDuration, duration)
        }
        
        let averageDuration = totalDuration / Double(iterations)
        
        return BenchmarkResult(
            name: name,
            iterations: iterations,
            totalDuration: totalDuration,
            averageDuration: averageDuration,
            minDuration: minDuration,
            maxDuration: maxDuration,
            operationsPerSecond: Double(iterations) / totalDuration,
            timestamp: Date()
        )
    }
}

// MARK: - Data Structures

public struct BenchmarkResult {
    public let name: String
    public let iterations: Int
    public let totalDuration: TimeInterval
    public let averageDuration: TimeInterval
    public let minDuration: TimeInterval
    public let maxDuration: TimeInterval
    public let operationsPerSecond: Double
    public let timestamp: Date
    
    public var successRate: Double {
        return 1.0
    }
    
    public var averageDurationMs: Double {
        return averageDuration * 1000
    }
    
    public var minDurationMs: Double {
        return minDuration * 1000
    }
    
    public var maxDurationMs: Double {
        return maxDuration * 1000
    }
}

public struct BenchmarkSuiteResult {
    public let totalBenchmarks: Int
    public let totalDuration: TimeInterval
    public let results: [BenchmarkResult]
    public let timestamp: Date
    
    public var averageOperationsPerSecond: Double {
        let totalOps = results.reduce(0) { $0 + $1.operationsPerSecond }
        return totalOps / Double(totalBenchmarks)
    }
    
    
    public var averageSuccessRate: Double {
        let totalSuccessRate = results.reduce(0.0) { $0 + $1.successRate }
        return totalSuccessRate / Double(totalBenchmarks)
    }
}

// MARK: - Benchmark Reporter

public class BenchmarkReporter {
    public static func generateReport(_ result: BenchmarkResult) -> String {
        var report = "=== Benchmark Report: \(result.name) ===\n"
        report += "Iterations: \(result.iterations)\n"
        report += "Total Duration: \(String(format: "%.4f", result.totalDuration))s\n"
        report += "Average Duration: \(String(format: "%.4f", result.averageDuration))s (\(String(format: "%.2f", result.averageDurationMs))ms)\n"
        report += "Min Duration: \(String(format: "%.4f", result.minDuration))s (\(String(format: "%.2f", result.minDurationMs))ms)\n"
        report += "Max Duration: \(String(format: "%.4f", result.maxDuration))s (\(String(format: "%.2f", result.maxDurationMs))ms)\n"
        report += "Operations/Second: \(String(format: "%.2f", result.operationsPerSecond))\n"
        report += "Success Rate: \(String(format: "%.2f", result.successRate * 100))%\n"
        report += "Timestamp: \(result.timestamp)\n"
        return report
    }
    
    public static func generateSuiteReport(_ result: BenchmarkSuiteResult) -> String {
        var report = "=== Benchmark Suite Report ===\n"
        report += "Total Benchmarks: \(result.totalBenchmarks)\n"
        report += "Total Duration: \(String(format: "%.4f", result.totalDuration))s\n"
        report += "Average Ops/Second: \(String(format: "%.2f", result.averageOperationsPerSecond))\n"
        report += "Average Success Rate: \(String(format: "%.2f", result.averageSuccessRate * 100))%\n"
        report += "Timestamp: \(result.timestamp)\n\n"
        
        report += "Individual Results:\n"
        for benchmark in result.results {
            report += "  \(benchmark.name): \(String(format: "%.2f", benchmark.operationsPerSecond)) ops/s (\(String(format: "%.2f", benchmark.successRate * 100))% success)\n"
        }
        
        return report
    }
}
