//
//  Benchmarks+GroupCommit.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-10-17.
//
// ColibrDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

import Foundation
import ColibriCore

extension BenchmarkCLI {
    
    /// Benchmarks group commit performance vs individual commits
    static func benchmarkGroupCommit() throws {
        print("\n=== GROUP COMMIT BENCHMARK ===\n")
        
        let testDir = "/tmp/colibri_group_commit_bench_\(UUID().uuidString)"
        defer { try? FileManager.default.removeItem(atPath: testDir) }
        
        let iterations = 1000
        
        // Test 1: Without group commit (individual flushes)
        print("Testing WITHOUT Group Commit...")
        var config1 = DBConfig(dataDir: testDir + "_nogc", storageEngine: "FileHeap")
        config1.walEnabled = true
        config1.walGroupCommitMs = 0.0  // Disable group commit
        config1.defaultIsolationLevel = IsolationLevel.readCommitted
        
        let db1 = Database(config: config1)
        try db1.createTable("test")
        
        let start1 = Date()
        for i in 0..<iterations {
            let tid = try db1.begin()
            try db1.insert(into: "test", row: ["id": .int(Int64(i)), "value": .string("test\(i)")], tid: tid)
            try db1.commit(tid)
        }
        let elapsed1 = Date().timeIntervalSince(start1)
        
        try db1.close()
        
        print("  ✓ \(iterations) commits in \(String(format: "%.3f", elapsed1))s")
        print("  ✓ \(String(format: "%.2f", Double(iterations) / elapsed1)) commits/sec")
        
        // Test 2: With group commit
        print("\nTesting WITH Group Commit...")
        var config2 = DBConfig(dataDir: testDir + "_gc", storageEngine: "FileHeap")
        config2.walEnabled = true
        config2.walGroupCommitMs = 2.0  // Enable group commit
        config2.defaultIsolationLevel = IsolationLevel.readCommitted
        
        let db2 = Database(config: config2)
        try db2.createTable("test")
        
        let start2 = Date()
        for i in 0..<iterations {
            let tid = try db2.begin()
            try db2.insert(into: "test", row: ["id": .int(Int64(i)), "value": .string("test\(i)")], tid: tid)
            try db2.commit(tid)
        }
        let elapsed2 = Date().timeIntervalSince(start2)
        
        // Get metrics
        if let metrics = db2.groupCommitMetrics() {
            print("  ✓ \(iterations) commits in \(String(format: "%.3f", elapsed2))s")
            print("  ✓ \(String(format: "%.2f", Double(iterations) / elapsed2)) commits/sec")
            print("\n  Group Commit Metrics:")
            print("    • Total commits: \(metrics.totalCommits)")
            print("    • Total batches: \(metrics.totalBatches)")
            print("    • Average batch size: \(String(format: "%.1f", metrics.averageBatchSize))")
            print("    • Largest batch: \(metrics.largestBatch)")
            print("    • Sync reduction: \(String(format: "%.1f%%", metrics.syncReduction * 100))")
            print("    • Performance multiplier: \(String(format: "%.1fx", metrics.performanceMultiplier))")
        }
        
        try db2.close()
        
        // Calculate improvement
        let speedup = elapsed1 / elapsed2
        print("\n  📊 Performance Improvement: \(String(format: "%.2fx", speedup)) faster")
        
        if speedup >= 5.0 {
            print("  ✅ Target achieved: 5-10x improvement!")
        } else if speedup >= 2.0 {
            print("  ⚠️  Moderate improvement (target: 5-10x)")
        } else {
            print("  ❌ Below target improvement")
        }
    }
    
    /// Benchmarks concurrent commit throughput with group commit
    static func benchmarkConcurrentGroupCommit() throws {
        print("\n=== CONCURRENT GROUP COMMIT BENCHMARK ===\n")
        
        let testDir = "/tmp/colibri_concurrent_gc_\(UUID().uuidString)"
        defer { try? FileManager.default.removeItem(atPath: testDir) }
        
        let concurrency = 8
        let iterationsPerThread = 125  // 8 * 125 = 1000 total
        
        var config = DBConfig(dataDir: testDir, storageEngine: "FileHeap")
        config.walEnabled = true
        config.walGroupCommitMs = 2.0
        config.defaultIsolationLevel = IsolationLevel.readCommitted
        
        let db = Database(config: config)
        try db.createTable("test")
        
        print("Running \(concurrency) concurrent threads...")
        print("Each thread: \(iterationsPerThread) commits")
        
        let start = Date()
        let queue = DispatchQueue(label: "bench", attributes: .concurrent)
        let group = DispatchGroup()
        
        for threadId in 0..<concurrency {
            group.enter()
            queue.async {
                defer { group.leave() }
                
                for i in 0..<iterationsPerThread {
                    do {
                        let tid = try db.begin()
                        let id = threadId * iterationsPerThread + i
                        try db.insert(into: "test", row: [
                            "id": .int(Int64(id)),
                            "thread": .int(Int64(threadId)),
                            "value": .string("test\(id)")
                        ], tid: tid)
                        try db.commit(tid)
                    } catch {
                        print("Error in thread \(threadId): \(error)")
                    }
                }
            }
        }
        
        group.wait()
        let elapsed = Date().timeIntervalSince(start)
        
        let totalCommits = concurrency * iterationsPerThread
        print("\n  ✓ \(totalCommits) commits in \(String(format: "%.3f", elapsed))s")
        print("  ✓ \(String(format: "%.2f", Double(totalCommits) / elapsed)) commits/sec")
        
        if let metrics = db.groupCommitMetrics() {
            print("\n  Group Commit Metrics:")
            print("    • Total commits: \(metrics.totalCommits)")
            print("    • Total batches: \(metrics.totalBatches)")
            print("    • Average batch size: \(String(format: "%.1f", metrics.averageBatchSize))")
            print("    • Largest batch: \(metrics.largestBatch)")
            print("    • Average wait time: \(String(format: "%.1f", metrics.averageWaitTimeUs))µs")
            print("    • Sync reduction: \(String(format: "%.1f%%", metrics.syncReduction * 100))")
            print("    • Performance multiplier: \(String(format: "%.1fx", metrics.performanceMultiplier))")
        }
        
        try db.close()
    }
    
    /// Benchmarks group commit with varying batch sizes
    static func benchmarkGroupCommitBatchSizes() throws {
        print("\n=== GROUP COMMIT BATCH SIZE BENCHMARK ===\n")
        
        let testDir = "/tmp/colibri_gc_batch_\(UUID().uuidString)"
        defer { try? FileManager.default.removeItem(atPath: testDir) }
        
        let iterations = 500
        let batchSizeTests = [1.0, 2.0, 5.0, 10.0]  // ms
        
        print("Testing different group commit intervals...")
        
        for waitMs in batchSizeTests {
            var config = DBConfig(dataDir: testDir + "_\(Int(waitMs))ms", storageEngine: "FileHeap")
            config.walEnabled = true
            config.walGroupCommitMs = waitMs
            config.defaultIsolationLevel = IsolationLevel.readCommitted
            
            let db = Database(config: config)
            try db.createTable("test")
            
            let start = Date()
            for i in 0..<iterations {
                let tid = try db.begin()
                try db.insert(into: "test", row: ["id": .int(Int64(i)), "value": .string("test\(i)")], tid: tid)
                try db.commit(tid)
            }
            let elapsed = Date().timeIntervalSince(start)
            
            if let metrics = db.groupCommitMetrics() {
                print("\n  Interval: \(String(format: "%.1f", waitMs))ms")
                print("    • Time: \(String(format: "%.3f", elapsed))s")
                print("    • Throughput: \(String(format: "%.2f", Double(iterations) / elapsed)) commits/sec")
                print("    • Avg batch: \(String(format: "%.1f", metrics.averageBatchSize))")
                print("    • Sync reduction: \(String(format: "%.1f%%", metrics.syncReduction * 100))")
            }
            
            try db.close()
        }
    }
    
    /// Stress test for group commit under heavy load
    static func stressTestGroupCommit() throws {
        print("\n=== GROUP COMMIT STRESS TEST ===\n")
        
        let testDir = "/tmp/colibri_gc_stress_\(UUID().uuidString)"
        defer { try? FileManager.default.removeItem(atPath: testDir) }
        
        var config = DBConfig(dataDir: testDir, storageEngine: "FileHeap")
        config.walEnabled = true
        config.walGroupCommitMs = 2.0
        config.defaultIsolationLevel = IsolationLevel.readCommitted
        
        let db = Database(config: config)
        try db.createTable("test")
        
        print("Running 10-second stress test...")
        
        let duration: TimeInterval = 10.0
        let concurrency = 16
        let endTime = Date().addingTimeInterval(duration)
        
        let queue = DispatchQueue(label: "stress", attributes: .concurrent)
        let group = DispatchGroup()
        var commitCounts = [Int](repeating: 0, count: concurrency)
        let lock = NSLock()
        
        for threadId in 0..<concurrency {
            group.enter()
            queue.async {
                defer { group.leave() }
                
                var count = 0
                var id = threadId * 1_000_000
                
                while Date() < endTime {
                    do {
                        let tid = try db.begin()
                        try db.insert(into: "test", row: [
                            "id": .int(Int64(id)),
                            "thread": .int(Int64(threadId)),
                            "value": .string("stress\(id)")
                        ], tid: tid)
                        try db.commit(tid)
                        count += 1
                        id += 1
                    } catch {
                        // Continue on error
                    }
                }
                
                lock.lock()
                commitCounts[threadId] = count
                lock.unlock()
            }
        }
        
        group.wait()
        
        let totalCommits = commitCounts.reduce(0, +)
        print("\n  ✓ \(totalCommits) total commits in \(String(format: "%.1f", duration))s")
        print("  ✓ \(String(format: "%.2f", Double(totalCommits) / duration)) commits/sec")
        print("\n  Per-thread commits:")
        for (threadId, count) in commitCounts.enumerated() {
            print("    Thread \(threadId): \(count)")
        }
        
        if let metrics = db.groupCommitMetrics() {
            print("\n  Final Group Commit Metrics:")
            print("    • Total commits: \(metrics.totalCommits)")
            print("    • Total batches: \(metrics.totalBatches)")
            print("    • Average batch size: \(String(format: "%.1f", metrics.averageBatchSize))")
            print("    • Largest batch: \(metrics.largestBatch)")
            print("    • Sync reduction: \(String(format: "%.1f%%", metrics.syncReduction * 100))")
            print("    • Performance multiplier: \(String(format: "%.1fx", metrics.performanceMultiplier))")
        }
        
        try db.close()
    }
}

