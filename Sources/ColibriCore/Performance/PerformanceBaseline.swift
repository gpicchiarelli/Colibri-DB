//
//  PerformanceBaseline.swift
//  ColibrìDB Performance Baseline & Gate
//
//  Exit Criteria: ≥ X kTPS, p95 ≤ Y ms, regressione ≤2%
//

import Foundation
import Logging

/// Performance metrics
public struct PerformanceMetrics: Codable, Sendable {
    public let tps: Double  // Transactions per second
    public let p50Latency: Double  // Median latency (ms)
    public let p95Latency: Double  // 95th percentile latency (ms)
    public let p99Latency: Double  // 99th percentile latency (ms)
    public let allocationsPerOp: Int  // Memory allocations per operation
    
    public init(tps: Double, p50: Double, p95: Double, p99: Double, allocations: Int) {
        self.tps = tps
        self.p50Latency = p50
        self.p95Latency = p95
        self.p99Latency = p99
        self.allocationsPerOp = allocations
    }
}

/// Performance targets (exit criteria)
public struct PerformanceTargets {
    public static let minTPS: Double = 50_000  // 50k TPS minimum
    public static let maxP95Latency: Double = 10.0  // 10ms p95 max
    public static let maxRegressionPercent: Double = 2.0  // 2% regression max
    
    public static func check(_ metrics: PerformanceMetrics) -> PerformanceGateResult {
        var passed = true
        var failures: [String] = []
        
        if metrics.tps < minTPS {
            passed = false
            failures.append("TPS \(Int(metrics.tps)) < target \(Int(minTPS))")
        }
        
        if metrics.p95Latency > maxP95Latency {
            passed = false
            failures.append("P95 latency \(String(format: "%.2f", metrics.p95Latency))ms > target \(maxP95Latency)ms")
        }
        
        return PerformanceGateResult(passed: passed, failures: failures, metrics: metrics)
    }
    
    public static func checkRegression(
        baseline: PerformanceMetrics,
        current: PerformanceMetrics
    ) -> PerformanceGateResult {
        var passed = true
        var failures: [String] = []
        
        // Check TPS regression
        let tpsRegression = ((baseline.tps - current.tps) / baseline.tps) * 100
        if tpsRegression > maxRegressionPercent {
            passed = false
            failures.append("TPS regression: \(String(format: "%.1f", tpsRegression))% > \(maxRegressionPercent)%")
        }
        
        // Check latency regression
        let p95Regression = ((current.p95Latency - baseline.p95Latency) / baseline.p95Latency) * 100
        if p95Regression > maxRegressionPercent {
            passed = false
            failures.append("P95 regression: \(String(format: "%.1f", p95Regression))% > \(maxRegressionPercent)%")
        }
        
        return PerformanceGateResult(passed: passed, failures: failures, metrics: current)
    }
}

/// Performance gate result
public struct PerformanceGateResult {
    public let passed: Bool
    public let failures: [String]
    public let metrics: PerformanceMetrics
    
    public func log(to logger: Logging.Logger) {
        var metadata: Logging.Logger.Metadata = [
            "status": "\(passed ? "PASS" : "FAIL")",
            "tps": "\(Int(metrics.tps))",
            "p50_latency_ms": "\(String(format: "%.2f", metrics.p50Latency))",
            "p95_latency_ms": "\(String(format: "%.2f", metrics.p95Latency))",
            "p99_latency_ms": "\(String(format: "%.2f", metrics.p99Latency))",
            "allocations_per_op": "\(metrics.allocationsPerOp)"
        ]
        if !failures.isEmpty {
            metadata["failures"] = "\(failures.joined(separator: "; "))"
        }
        logger.info("Performance Gate Result", metadata: metadata)
    }
}

/// Performance harness
public actor PerformanceHarness {
    
    public init() {}
    
    /// Run performance benchmark
    public func benchmark(
        name: String,
        warmup: Int = 1000,
        iterations: Int = 10_000,
        operation: () async throws -> Void
    ) async throws -> PerformanceMetrics {
        
        // Warmup
        for _ in 0..<warmup {
            try await operation()
        }
        
        // Measure
        var latencies: [Double] = []
        let startTime = Date()
        
        for _ in 0..<iterations {
            let opStart = Date()
            try await operation()
            let opEnd = Date()
            
            let latencyMs = opEnd.timeIntervalSince(opStart) * 1000
            latencies.append(latencyMs)
        }
        
        let endTime = Date()
        let totalTime = endTime.timeIntervalSince(startTime)
        
        // Calculate metrics
        latencies.sort()
        let tps = Double(iterations) / totalTime
        let p50 = latencies[iterations / 2]
        let p95 = latencies[Int(Double(iterations) * 0.95)]
        let p99 = latencies[Int(Double(iterations) * 0.99)]
        
        // Estimate allocations (simplified)
        let allocations = 10  // Placeholder
        
        return PerformanceMetrics(
            tps: tps,
            p50: p50,
            p95: p95,
            p99: p99,
            allocations: allocations
        )
    }
    
    /// Save baseline
    public func saveBaseline(_ metrics: PerformanceMetrics, to path: String) throws {
        let encoder = JSONEncoder()
        encoder.outputFormatting = .prettyPrinted
        let data = try encoder.encode(metrics)
        try data.write(to: URL(fileURLWithPath: path))
    }
    
    /// Load baseline
    public func loadBaseline(from path: String) throws -> PerformanceMetrics {
        let data = try Data(contentsOf: URL(fileURLWithPath: path))
        let decoder = JSONDecoder()
        return try decoder.decode(PerformanceMetrics.self, from: data)
    }
}

