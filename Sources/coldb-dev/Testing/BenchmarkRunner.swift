//
//  BenchmarkRunner.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-09-27.
//
// ColibrDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Benchmark runner integration for continuous testing system.

import Foundation
import os.log

/// Runner for benchmark integration
public final class BenchmarkRunner {
    private let logger = Logger(subsystem: "com.colibridb.testing", category: "benchmark")
    private let benchmarkExecutablePath: String
    private let outputDirectory: String
    
    public init(benchmarkExecutablePath: String, outputDirectory: String) {
        self.benchmarkExecutablePath = benchmarkExecutablePath
        self.outputDirectory = outputDirectory
    }
    
    /// Runs all benchmarks
    public func runAllBenchmarks() -> BenchmarkResult {
        logger.info("Starting benchmark execution")
        
        let startTime = Date()
        let result = runBenchmarks()
        let endTime = Date()
        let duration = endTime.timeIntervalSince(startTime)
        
        logger.info("Benchmarks completed: \(result.scenarios.count) scenarios in \(String(format: "%.2f", duration))s")
        
        return BenchmarkResult(
            scenarios: result.scenarios,
            totalDuration: duration,
            timestamp: endTime
        )
    }
    
    /// Runs specific benchmark scenarios
    public func runBenchmarkScenarios(_ scenarios: [String]) -> BenchmarkResult {
        logger.info("Running specific benchmark scenarios: \(scenarios.joined(separator: ", "))")
        
        let startTime = Date()
        let result = runBenchmarks(scenarios: scenarios)
        let endTime = Date()
        let duration = endTime.timeIntervalSince(startTime)
        
        return BenchmarkResult(
            scenarios: result.scenarios,
            totalDuration: duration,
            timestamp: endTime
        )
    }
    
    /// Runs benchmarks by category
    public func runBenchmarksByCategory(_ category: BenchmarkCategory) -> BenchmarkResult {
        let scenarios = getBenchmarkScenarios(for: category)
        return runBenchmarkScenarios(scenarios)
    }
    
    // MARK: - Private Methods
    
    private func runBenchmarks(scenarios: [String] = []) -> BenchmarkExecutionResult {
        let process = Process()
        process.executableURL = URL(fileURLWithPath: benchmarkExecutablePath)
        
        var arguments: [String] = []
        if !scenarios.isEmpty {
            arguments.append(contentsOf: scenarios)
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
            
            return parseBenchmarkOutput(output)
        } catch {
            logger.error("Failed to run benchmarks: \(error.localizedDescription)")
            return BenchmarkExecutionResult(scenarios: [])
        }
    }
    
    private func parseBenchmarkOutput(_ output: String) -> BenchmarkExecutionResult {
        var scenarios: [BenchmarkScenario] = []
        
        let lines = output.components(separatedBy: .newlines)
        
        for line in lines {
            if line.contains("[") && line.contains("]") && line.contains("iterations=") {
                let scenario = parseBenchmarkLine(line)
                if let scenario = scenario {
                    scenarios.append(scenario)
                }
            }
        }
        
        return BenchmarkExecutionResult(scenarios: scenarios)
    }
    
    private func parseBenchmarkLine(_ line: String) -> BenchmarkScenario? {
        // Parse lines like: [heap-insert] iterations=10000 elapsed_ms=123.456 throughput_ops_s=81000.00
        
        let components = line.components(separatedBy: " ")
        guard components.count >= 4 else { return nil }
        
        // Extract name from [name] format
        let nameComponent = components[0]
        let name = String(nameComponent.dropFirst().dropLast())
        
        // Extract iterations
        var iterations = 0
        if let iterComponent = components.first(where: { $0.hasPrefix("iterations=") }) {
            let iterValue = String(iterComponent.dropFirst("iterations=".count))
            iterations = Int(iterValue) ?? 0
        }
        
        // Extract elapsed time
        var elapsedMs = 0.0
        if let elapsedComponent = components.first(where: { $0.hasPrefix("elapsed_ms=") }) {
            let elapsedValue = String(elapsedComponent.dropFirst("elapsed_ms=".count))
            elapsedMs = Double(elapsedValue) ?? 0.0
        }
        
        // Extract throughput
        var throughput = 0.0
        if let throughputComponent = components.first(where: { $0.hasPrefix("throughput_ops_s=") }) {
            let throughputValue = String(throughputComponent.dropFirst("throughput_ops_s=".count))
            throughput = Double(throughputValue) ?? 0.0
        }
        
        return BenchmarkScenario(
            name: name,
            iterations: iterations,
            elapsedMs: elapsedMs,
            throughput: throughput
        )
    }
    
    private func getBenchmarkScenarios(for category: BenchmarkCategory) -> [String] {
        switch category {
        case .storage:
            return ["heap-insert", "heap-scan"]
        case .indexing:
            return ["btree-lookup"]
        case .query:
            return ["planner-join"]
        case .all:
            return ["heap-insert", "heap-scan", "btree-lookup", "planner-join"]
        }
    }
}

// MARK: - Supporting Types

public enum BenchmarkCategory {
    case storage
    case indexing
    case query
    case all
}

public struct BenchmarkResult {
    public let scenarios: [BenchmarkScenario]
    public let totalDuration: TimeInterval
    public let timestamp: Date
    
    public var averageThroughput: Double {
        guard !scenarios.isEmpty else { return 0.0 }
        let totalThroughput = scenarios.reduce(0.0) { $0 + $1.throughput }
        return totalThroughput / Double(scenarios.count)
    }
    
    public var totalIterations: Int {
        return scenarios.reduce(0) { $0 + $1.iterations }
    }
}

public struct BenchmarkScenario {
    public let name: String
    public let iterations: Int
    public let elapsedMs: Double
    public let throughput: Double
    
    public var averageLatencyMs: Double {
        guard iterations > 0 else { return 0.0 }
        return elapsedMs / Double(iterations)
    }
}

private struct BenchmarkExecutionResult {
    let scenarios: [BenchmarkScenario]
}
