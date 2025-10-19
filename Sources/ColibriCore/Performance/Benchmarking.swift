//
//  Benchmarking.swift
//

import Foundation

public struct BenchmarkResult {
    public let name: String
    public let iterations: Int
    public let totalDuration: TimeInterval
    public let avgDuration: TimeInterval
    public let minDuration: TimeInterval
    public let maxDuration: TimeInterval
    public let throughput: Double
    
    public init(name: String, iterations: Int, durations: [TimeInterval]) {
        self.name = name
        self.iterations = iterations
        self.totalDuration = durations.reduce(0, +)
        self.avgDuration = totalDuration / Double(iterations)
        self.minDuration = durations.min() ?? 0
        self.maxDuration = durations.max() ?? 0
        self.throughput = Double(iterations) / totalDuration
    }
}

public actor BenchmarkRunner {
    public init() {}
    
    public func benchmark(
        name: String,
        iterations: Int,
        warmup: Int = 10,
        operation: @escaping () async throws -> Void
    ) async throws -> BenchmarkResult {
        for _ in 0..<warmup {
            try await operation()
        }
        
        var durations: [TimeInterval] = []
        
        for _ in 0..<iterations {
            let start = Date()
            try await operation()
            let duration = Date().timeIntervalSince(start)
            durations.append(duration)
        }
        
        return BenchmarkResult(name: name, iterations: iterations, durations: durations)
    }
    
    public func compareBenchmarks(_ results: [BenchmarkResult]) -> String {
        guard let baseline = results.first else {
            return "No benchmarks to compare"
        }
        
        var output = "Benchmark Comparison (baseline: \(baseline.name))\n"
        output += String(repeating: "=", count: 60) + "\n"
        
        for result in results {
            let speedup = baseline.avgDuration / result.avgDuration
            let percent = (speedup - 1.0) * 100.0
            
            output += String(format: "%-30s: %.4f ms (%.2f%%)\n",
                           result.name,
                           result.avgDuration * 1000,
                           percent)
        }
        
        return output
    }
}

