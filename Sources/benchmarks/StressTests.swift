//
//  StressTests.swift
//  ColibrìDB Benchmarks
//
//  Created by Giacomo Picchiarelli on 2025-10-17.
//
// Theme: High-volume stress tests for stability and memory leak detection.

import Foundation
import ColibriCore

extension BenchmarkCLI {
    // MARK: - Stress Test Suite (600k ops each)
    
    /// Stress test: 600k heap inserts in-memory
    static func stressHeapInsert() throws -> InternalBenchmarkResult {
        print("🔥 STRESS TEST: Heap Insert (600k ops)")
        
        var config = DBConfig(storageEngine: "InMemory")
        config.autoCompactionEnabled = false
        let db = Database(config: config)
        try db.createTable("stress")
        
        let monitor = SystemMonitor(database: db)
        let initialMetrics = monitor.getCurrentMetrics()
        
        let iterations = 600_000
        let clock = ContinuousClock()
        let start = clock.now
        
        // Sample latencies every 1000 ops for memory efficiency
        var sampledLatencies: [Double] = []
        sampledLatencies.reserveCapacity(iterations / 1000)
        
        for i in 0..<iterations {
            let t0 = (i % 1000 == 0) ? clock.now : start
            _ = try db.insert(into: "stress", row: [
                "id": .int(Int64(i)),
                "data": .string("stress_test_\(i)_padding_data")
            ])
            
            if i % 1000 == 0 {
                sampledLatencies.append(msDelta(t0, clock.now))
            }
            
            // Progress indicator
            if i > 0 && i % 100_000 == 0 {
                print("   Progress: \(i)/\(iterations) (\(i*100/iterations)%)")
            }
        }
        
        let elapsed = clock.now - start
        let finalMetrics = monitor.getCurrentMetrics()
        
        // Memory usage analysis
        let memoryDelta = Double(finalMetrics.memory.usedBytes - initialMetrics.memory.usedBytes) / 1_048_576.0
        let memoryPerOp = memoryDelta / Double(iterations) * 1000.0 // KB per op
        
        print("   ✅ Completed: \(iterations) ops")
        print("   📊 Memory delta: \(String(format: "%.1f", memoryDelta)) MB")
        print("   📊 Memory per 1k ops: \(String(format: "%.2f", memoryPerOp)) KB")
        
        return InternalBenchmarkResult(
            name: "stress-heap-insert-600k",
            iterations: iterations,
            elapsed: elapsed,
            latenciesMs: sampledLatencies,
            metadata: [
                "total_ops": "\(iterations)",
                "sampled_latencies": "\(sampledLatencies.count)",
                "memory_delta_mb": String(format: "%.1f", memoryDelta),
                "memory_per_1k_ops_kb": String(format: "%.2f", memoryPerOp)
            ],
            systemMetrics: finalMetrics
        )
    }
    
    /// Stress test: 600k B+Tree lookups (persistent)
    static func stressBTreeLookup() throws -> InternalBenchmarkResult {
        print("🔥 STRESS TEST: B+Tree Lookup (600k ops)")
        
        let fm = FileManager.default
        let tempDir = fm.temporaryDirectory.appendingPathComponent(UUID().uuidString, isDirectory: true)
        try fm.createDirectory(at: tempDir, withIntermediateDirectories: true)
        defer { try? fm.removeItem(at: tempDir) }
        
        var config = DBConfig(dataDir: tempDir.path)
        config.autoCompactionEnabled = false
        let db = Database(config: config)
        
        try db.createTable("stress")
        try db.createIndex(name: "idx_stress", on: "stress", columns: ["id"], using: "BTree")
        
        // Pre-populate with 100k unique keys
        let uniqueKeys = 100_000
        print("   📝 Pre-populating \(uniqueKeys) keys...")
        for i in 0..<uniqueKeys {
            _ = try db.insert(into: "stress", row: ["id": .int(Int64(i)), "data": .string("key_\(i)")])
            
            if i > 0 && i % 20_000 == 0 {
                print("   Progress: \(i)/\(uniqueKeys)")
            }
        }
        
        db.flushAll(fullSync: true)
        print("   ✅ Pre-population complete, data flushed")
        
        // Warmup
        for i in 0..<min(10_000, uniqueKeys) {
            _ = try db.indexSearchEqualsTyped(table: "stress", index: "idx_stress", value: .int(Int64(i)))
        }
        print("   ✅ Warmup complete")
        
        // Stress test: 600k lookups (random keys, with repetition)
        let iterations = 600_000
        let monitor = SystemMonitor(database: db)
        let initialMetrics = monitor.getCurrentMetrics()
        
        let clock = ContinuousClock()
        let start = clock.now
        
        var sampledLatencies: [Double] = []
        sampledLatencies.reserveCapacity(iterations / 1000)
        var foundCount = 0
        
        for i in 0..<iterations {
            let keyToFind = BenchmarkCLI.withSeededRNG { rng in
                Int.random(in: 0..<uniqueKeys, using: &rng!)
            }
            
            let t0 = (i % 1000 == 0) ? clock.now : start
            let hits = try db.indexSearchEqualsTyped(table: "stress", index: "idx_stress", value: .int(Int64(keyToFind)))
            
            if !hits.isEmpty { foundCount += 1 }
            
            if i % 1000 == 0 {
                sampledLatencies.append(msDelta(t0, clock.now))
            }
            
            if i > 0 && i % 100_000 == 0 {
                print("   Progress: \(i)/\(iterations) (\(i*100/iterations)%)")
            }
        }
        
        let elapsed = clock.now - start
        let finalMetrics = monitor.getCurrentMetrics()
        
        let hitRate = Double(foundCount) / Double(iterations) * 100.0
        print("   ✅ Completed: \(iterations) lookups")
        print("   📊 Hit rate: \(String(format: "%.2f", hitRate))%")
        
        return InternalBenchmarkResult(
            name: "stress-btree-lookup-600k",
            iterations: iterations,
            elapsed: elapsed,
            latenciesMs: sampledLatencies,
            metadata: [
                "total_ops": "\(iterations)",
                "unique_keys": "\(uniqueKeys)",
                "hit_rate": String(format: "%.2f", hitRate),
                "sampled_latencies": "\(sampledLatencies.count)"
            ],
            systemMetrics: finalMetrics
        )
    }
    
    /// Stress test: 600k transaction commits
    static func stressTransactionCommit() throws -> InternalBenchmarkResult {
        print("🔥 STRESS TEST: Transaction Commit (600k ops)")
        
        let fm = FileManager.default
        let tempDir = fm.temporaryDirectory.appendingPathComponent(UUID().uuidString, isDirectory: true)
        try fm.createDirectory(at: tempDir, withIntermediateDirectories: true)
        defer { try? fm.removeItem(at: tempDir) }
        
        var config = DBConfig(dataDir: tempDir.path, storageEngine: "FileHeap")
        config.walEnabled = true
        config.walFullFSyncEnabled = false
        config.walGroupCommitMs = 2.0
        config.autoCompactionEnabled = false
        
        let db = Database(config: config)
        try db.createTable("stress")
        
        let monitor = SystemMonitor(database: db)
        let initialMetrics = monitor.getCurrentMetrics()
        
        let iterations = 600_000
        let clock = ContinuousClock()
        let start = clock.now
        
        var sampledLatencies: [Double] = []
        sampledLatencies.reserveCapacity(iterations / 1000)
        
        for i in 0..<iterations {
            let t0 = (i % 1000 == 0) ? clock.now : start
            
            let tid = try db.begin()
            _ = try db.insert(into: "stress", row: [
                "id": .int(Int64(i)),
                "data": .string("tx_\(i)")
            ], tid: tid)
            try db.commit(tid)
            
            if i % 1000 == 0 {
                sampledLatencies.append(msDelta(t0, clock.now))
            }
            
            if i > 0 && i % 100_000 == 0 {
                print("   Progress: \(i)/\(iterations) (\(i*100/iterations)%)")
            }
        }
        
        let elapsed = clock.now - start
        let finalMetrics = monitor.getCurrentMetrics()
        
        // Check for memory leaks
        let memoryDelta = Double(finalMetrics.memory.usedBytes - initialMetrics.memory.usedBytes) / 1_048_576.0
        
        print("   ✅ Completed: \(iterations) transactions")
        print("   📊 Memory delta: \(String(format: "%.1f", memoryDelta)) MB")
        
        return InternalBenchmarkResult(
            name: "stress-tx-commit-600k",
            iterations: iterations,
            elapsed: elapsed,
            latenciesMs: sampledLatencies,
            metadata: [
                "total_ops": "\(iterations)",
                "memory_delta_mb": String(format: "%.1f", memoryDelta),
                "sampled_latencies": "\(sampledLatencies.count)"
            ],
            systemMetrics: finalMetrics
        )
    }
    
    /// Stress test: 600k mixed operations (50% insert, 30% update, 20% delete)
    static func stressMixedWorkload() throws -> InternalBenchmarkResult {
        print("🔥 STRESS TEST: Mixed Workload (600k ops)")
        
        var config = DBConfig(storageEngine: "InMemory")
        config.autoCompactionEnabled = false
        let db = Database(config: config)
        try db.createTable("stress")
        
        // Pre-populate with 50k rows
        let initialRows = 50_000
        print("   📝 Pre-populating \(initialRows) rows...")
        for i in 0..<initialRows {
            _ = try db.insert(into: "stress", row: [
                "id": .int(Int64(i)),
                "value": .int(Int64(i * 2))
            ])
        }
        
        let monitor = SystemMonitor(database: db)
        let initialMetrics = monitor.getCurrentMetrics()
        
        let iterations = 600_000
        let clock = ContinuousClock()
        let start = clock.now
        
        var sampledLatencies: [Double] = []
        sampledLatencies.reserveCapacity(iterations / 1000)
        
        var opCounts = ["insert": 0, "update": 0, "delete": 0]
        var nextId = initialRows
        
        for i in 0..<iterations {
            let t0 = (i % 1000 == 0) ? clock.now : start
            
            let roll = BenchmarkCLI.withSeededRNG { rng in
                Double.random(in: 0..<1.0, using: &rng!)
            }
            
            if roll < 0.5 {
                // 50% Insert
                _ = try db.insert(into: "stress", row: [
                    "id": .int(Int64(nextId)),
                    "value": .int(Int64(nextId * 2))
                ])
                nextId += 1
                opCounts["insert"]! += 1
            } else if roll < 0.8 {
                // 30% Update
                let targetId = BenchmarkCLI.withSeededRNG { rng in
                    Int.random(in: 0..<nextId, using: &rng!)
                }
                _ = try? db.updateEquals(
                    table: "stress",
                    matchColumn: "id",
                    matchValue: .int(Int64(targetId)),
                    set: ["value": .int(Int64(targetId * 3))],
                    tid: nil
                )
                opCounts["update"]! += 1
            } else {
                // 20% Delete
                let targetId = BenchmarkCLI.withSeededRNG { rng in
                    Int.random(in: 0..<nextId, using: &rng!)
                }
                _ = try? db.deleteEquals(table: "stress", column: "id", value: .int(Int64(targetId)))
                opCounts["delete"]! += 1
            }
            
            if i % 1000 == 0 {
                sampledLatencies.append(msDelta(t0, clock.now))
            }
            
            if i > 0 && i % 100_000 == 0 {
                print("   Progress: \(i)/\(iterations) (\(i*100/iterations)%) - Inserts:\(opCounts["insert"]!) Updates:\(opCounts["update"]!) Deletes:\(opCounts["delete"]!)")
            }
        }
        
        let elapsed = clock.now - start
        let finalMetrics = monitor.getCurrentMetrics()
        
        // Final row count
        let finalCount = try db.scan("stress").count
        
        print("   ✅ Completed: \(iterations) mixed ops")
        print("   📊 Final row count: \(finalCount)")
        print("   📊 Op distribution: I:\(opCounts["insert"]!) U:\(opCounts["update"]!) D:\(opCounts["delete"]!)")
        
        return InternalBenchmarkResult(
            name: "stress-mixed-600k",
            iterations: iterations,
            elapsed: elapsed,
            latenciesMs: sampledLatencies,
            metadata: [
                "total_ops": "\(iterations)",
                "inserts": "\(opCounts["insert"]!)",
                "updates": "\(opCounts["update"]!)",
                "deletes": "\(opCounts["delete"]!)",
                "final_rows": "\(finalCount)",
                "sampled_latencies": "\(sampledLatencies.count)"
            ],
            systemMetrics: finalMetrics
        )
    }
    
    /// Stress test: 600k index operations (Hash)
    static func stressIndexOperations() throws -> InternalBenchmarkResult {
        print("🔥 STRESS TEST: Index Operations (600k ops)")
        
        var config = DBConfig(storageEngine: "InMemory")
        config.autoCompactionEnabled = false
        let db = Database(config: config)
        try db.createTable("stress")
        try db.createIndex(name: "idx_stress", on: "stress", columns: ["key"], using: "Hash")
        
        let monitor = SystemMonitor(database: db)
        let initialMetrics = monitor.getCurrentMetrics()
        
        let iterations = 600_000
        let clock = ContinuousClock()
        let start = clock.now
        
        var sampledLatencies: [Double] = []
        sampledLatencies.reserveCapacity(iterations / 1000)
        
        // Phase 1: Insert 300k
        print("   📝 Phase 1: Inserting 300k keys...")
        for i in 0..<300_000 {
            let t0 = (i % 1000 == 0) ? clock.now : start
            _ = try db.insert(into: "stress", row: [
                "key": .string("key_\(i)"),
                "value": .int(Int64(i))
            ])
            
            if i % 1000 == 0 {
                sampledLatencies.append(msDelta(t0, clock.now))
            }
            
            if i > 0 && i % 100_000 == 0 {
                print("   Progress: \(i)/300000")
            }
        }
        
        // Phase 2: Lookup 300k (random)
        print("   🔍 Phase 2: Looking up 300k keys...")
        var foundCount = 0
        for i in 0..<300_000 {
            let keyToFind = BenchmarkCLI.withSeededRNG { rng in
                Int.random(in: 0..<300_000, using: &rng!)
            }
            
            let t0 = (i % 1000 == 0) ? clock.now : start
            let hits = try db.indexSearchEqualsTyped(table: "stress", index: "idx_stress", value: .string("key_\(keyToFind)"))
            
            if !hits.isEmpty { foundCount += 1 }
            
            if i % 1000 == 0 {
                sampledLatencies.append(msDelta(t0, clock.now))
            }
            
            if i > 0 && i % 100_000 == 0 {
                print("   Progress: \(i)/300000")
            }
        }
        
        let elapsed = clock.now - start
        let finalMetrics = monitor.getCurrentMetrics()
        
        let hitRate = Double(foundCount) / 300_000.0 * 100.0
        
        print("   ✅ Completed: \(iterations) total ops (300k insert + 300k lookup)")
        print("   📊 Lookup hit rate: \(String(format: "%.2f", hitRate))%")
        
        return InternalBenchmarkResult(
            name: "stress-index-ops-600k",
            iterations: iterations,
            elapsed: elapsed,
            latenciesMs: sampledLatencies,
            metadata: [
                "total_ops": "\(iterations)",
                "insert_ops": "300000",
                "lookup_ops": "300000",
                "hit_rate": String(format: "%.2f", hitRate),
                "sampled_latencies": "\(sampledLatencies.count)"
            ],
            systemMetrics: finalMetrics
        )
    }
    
    /// Stress test: 600k concurrent operations
    static func stressConcurrentOperations(workers: Int = 8) throws -> InternalBenchmarkResult {
        print("🔥 STRESS TEST: Concurrent Operations (600k ops, \(workers) workers)")
        
        var config = DBConfig(storageEngine: "InMemory")
        config.autoCompactionEnabled = false
        config.walEnabled = false
        let db = Database(config: config)
        try db.createTable("stress")
        
        let monitor = SystemMonitor(database: db)
        let initialMetrics = monitor.getCurrentMetrics()
        
        let totalOps = 600_000
        let opsPerWorker = totalOps / workers
        
        let group = DispatchGroup()
        let queue = DispatchQueue.global(qos: .userInitiated)
        let dbBox = NonSendableBox(db)
        let latCollector = LatCollector()
        
        let clock = ContinuousClock()
        let start = clock.now
        
        print("   🚀 Starting \(workers) concurrent workers...")
        
        for w in 0..<workers {
            group.enter()
            let work: @Sendable () -> Void = {
                defer { group.leave() }
                
                for i in 0..<opsPerWorker {
                    let globalId = w * opsPerWorker + i
                    
                    do {
                        let t0 = (i % 1000 == 0) ? clock.now : start
                        
                        let tid = try dbBox.value.begin()
                        _ = try dbBox.value.insert(into: "stress", row: [
                            "id": .int(Int64(globalId)),
                            "worker": .int(Int64(w)),
                            "data": .string("worker_\(w)_op_\(i)")
                        ], tid: tid)
                        try dbBox.value.commit(tid)
                        
                        if i % 1000 == 0 {
                            latCollector.append(msDelta(t0, clock.now))
                        }
                    } catch {
                        // Continue on error for stress test
                    }
                }
            }
            
            queue.async(execute: work)
        }
        
        group.wait()
        let elapsed = clock.now - start
        let finalMetrics = monitor.getCurrentMetrics()
        
        // Verify final count
        let finalCount = try db.scan("stress").count
        
        print("   ✅ Completed: \(totalOps) concurrent ops")
        print("   📊 Final row count: \(finalCount)/\(totalOps)")
        print("   📊 Success rate: \(String(format: "%.2f", Double(finalCount)/Double(totalOps)*100.0))%")
        
        return InternalBenchmarkResult(
            name: "stress-concurrent-600k",
            iterations: totalOps,
            elapsed: elapsed,
            latenciesMs: latCollector.snapshot(),
            metadata: [
                "total_ops": "\(totalOps)",
                "workers": "\(workers)",
                "ops_per_worker": "\(opsPerWorker)",
                "final_rows": "\(finalCount)",
                "success_rate": String(format: "%.2f", Double(finalCount)/Double(totalOps)*100.0)
            ],
            systemMetrics: finalMetrics
        )
    }
    
    /// Stress test: 600k WAL append operations
    static func stressWALAppend() throws -> InternalBenchmarkResult {
        print("🔥 STRESS TEST: WAL Append (600k ops)")
        
        let fm = FileManager.default
        let tempDir = fm.temporaryDirectory.appendingPathComponent(UUID().uuidString, isDirectory: true)
        try fm.createDirectory(at: tempDir, withIntermediateDirectories: true)
        defer { try? fm.removeItem(at: tempDir) }
        
        var config = DBConfig(dataDir: tempDir.path)
        config.walEnabled = true
        config.walFullFSyncEnabled = false
        config.walGroupCommitMs = 1.0
        config.walCompression = .none
        config.autoCompactionEnabled = false
        
        let db = Database(config: config)
        let globalWAL = db.globalWAL!
        
        let monitor = SystemMonitor(database: db)
        let initialMetrics = monitor.getCurrentMetrics()
        
        let iterations = 600_000
        let clock = ContinuousClock()
        let start = clock.now
        
        var sampledLatencies: [Double] = []
        sampledLatencies.reserveCapacity(iterations / 1000)
        
        // Prepare realistic WAL record
        let testRecord = WALHeapInsertRecord(
            dbId: 1,
            txId: 1,
            tableId: "stress_table",
            pageId: 1,
            slotId: 1,
            rowData: Data("wal_stress_test_record_payload".utf8)
        )
        
        for i in 0..<iterations {
            let t0 = (i % 1000 == 0) ? clock.now : start
            
            _ = try globalWAL.append(testRecord)
            
            if i % 1000 == 0 {
                sampledLatencies.append(msDelta(t0, clock.now))
            }
            
            // Periodic flush to prevent unbounded memory growth
            if i % 10_000 == 0 && i > 0 {
                try globalWAL.flush(upTo: UInt64(i))
            }
            
            if i > 0 && i % 100_000 == 0 {
                print("   Progress: \(i)/\(iterations) (\(i*100/iterations)%)")
            }
        }
        
        // Final flush
        try globalWAL.flush(upTo: UInt64(iterations))
        
        let elapsed = clock.now - start
        let finalMetrics = monitor.getCurrentMetrics()
        
        // Get WAL file size
        let walPath = tempDir.appendingPathComponent("global.wal")
        let walSize = (try? FileManager.default.attributesOfItem(atPath: walPath.path)[.size] as? UInt64) ?? 0
        
        print("   ✅ Completed: \(iterations) WAL appends")
        print("   📊 WAL file size: \(walSize / 1_048_576) MB")
        
        return InternalBenchmarkResult(
            name: "stress-wal-append-600k",
            iterations: iterations,
            elapsed: elapsed,
            latenciesMs: sampledLatencies,
            metadata: [
                "total_ops": "\(iterations)",
                "wal_size_mb": "\(walSize / 1_048_576)",
                "compression": "none",
                "sampled_latencies": "\(sampledLatencies.count)"
            ],
            systemMetrics: finalMetrics
        )
    }
    
    /// Stress test: 600k scan operations with growing table
    static func stressScanGrowing() throws -> InternalBenchmarkResult {
        print("🔥 STRESS TEST: Scan on Growing Table (600k ops)")
        
        var config = DBConfig(storageEngine: "InMemory")
        config.autoCompactionEnabled = false
        let db = Database(config: config)
        try db.createTable("stress")
        
        let monitor = SystemMonitor(database: db)
        let initialMetrics = monitor.getCurrentMetrics()
        
        let iterations = 600_000
        let clock = ContinuousClock()
        let start = clock.now
        
        var sampledLatencies: [Double] = []
        sampledLatencies.reserveCapacity(iterations / 100)
        
        var totalRowsScanned: UInt64 = 0
        
        // Interleave inserts and scans
        // Every 100 inserts, do 1 scan
        for batchStart in stride(from: 0, to: iterations, by: 101) {
            // Insert batch of 100
            for i in 0..<100 {
                let globalId = batchStart + i
                if globalId >= iterations { break }
                
                _ = try db.insert(into: "stress", row: [
                    "id": .int(Int64(globalId)),
                    "data": .string("scan_stress_\(globalId)")
                ])
            }
            
            // Scan once
            let t0 = clock.now
            let rows = try db.scan("stress")
            let t1 = clock.now
            
            totalRowsScanned += UInt64(rows.count)
            sampledLatencies.append(msDelta(t0, t1))
            
            if batchStart > 0 && batchStart % 100_000 == 0 {
                print("   Progress: \(batchStart)/\(iterations) (\(batchStart*100/iterations)%) - Table size: \(rows.count) rows")
            }
        }
        
        let elapsed = clock.now - start
        let finalMetrics = monitor.getCurrentMetrics()
        
        let finalCount = try db.scan("stress").count
        
        print("   ✅ Completed: \(iterations) ops (~594k inserts + ~6k scans)")
        print("   📊 Final table size: \(finalCount) rows")
        print("   📊 Total rows scanned: \(totalRowsScanned)")
        
        return InternalBenchmarkResult(
            name: "stress-scan-growing-600k",
            iterations: iterations,
            elapsed: elapsed,
            latenciesMs: sampledLatencies,
            metadata: [
                "total_ops": "\(iterations)",
                "final_table_size": "\(finalCount)",
                "total_rows_scanned": "\(totalRowsScanned)",
                "scan_count": "\(sampledLatencies.count)",
                "sampled_latencies": "\(sampledLatencies.count)"
            ],
            systemMetrics: finalMetrics
        )
    }
    
    /// Stress test: 600k operations with multiple indexes
    static func stressMultipleIndexes() throws -> InternalBenchmarkResult {
        print("🔥 STRESS TEST: Multiple Indexes (600k ops)")
        
        var config = DBConfig(storageEngine: "InMemory")
        config.autoCompactionEnabled = false
        let db = Database(config: config)
        try db.createTable("stress")
        
        // Create 3 different indexes
        try db.createIndex(name: "idx_id", on: "stress", columns: ["id"], using: "Hash")
        try db.createIndex(name: "idx_name", on: "stress", columns: ["name"], using: "SkipList")
        try db.createIndex(name: "idx_category", on: "stress", columns: ["category"], using: "BTree")
        
        let monitor = SystemMonitor(database: db)
        let initialMetrics = monitor.getCurrentMetrics()
        
        let iterations = 600_000
        let clock = ContinuousClock()
        let start = clock.now
        
        var sampledLatencies: [Double] = []
        sampledLatencies.reserveCapacity(iterations / 1000)
        
        let categories = ["A", "B", "C", "D", "E"]
        
        for i in 0..<iterations {
            let t0 = (i % 1000 == 0) ? clock.now : start
            
            _ = try db.insert(into: "stress", row: [
                "id": .int(Int64(i)),
                "name": .string("name_\(i % 1000)"),
                "category": .string(categories[i % categories.count])
            ])
            
            if i % 1000 == 0 {
                sampledLatencies.append(msDelta(t0, clock.now))
            }
            
            if i > 0 && i % 100_000 == 0 {
                print("   Progress: \(i)/\(iterations) (\(i*100/iterations)%)")
            }
        }
        
        let elapsed = clock.now - start
        let finalMetrics = monitor.getCurrentMetrics()
        
        // Verify indexes work
        let testLookups = [
            try db.indexSearchEqualsTyped(table: "stress", index: "idx_id", value: .int(12345)),
            try db.indexSearchEqualsTyped(table: "stress", index: "idx_name", value: .string("name_100")),
            try db.indexSearchEqualsTyped(table: "stress", index: "idx_category", value: .string("A"))
        ]
        
        let indexesWorking = testLookups.allSatisfy { !$0.isEmpty }
        
        print("   ✅ Completed: \(iterations) inserts (3 indexes updated each)")
        print("   📊 All indexes working: \(indexesWorking ? "YES" : "NO")")
        
        return InternalBenchmarkResult(
            name: "stress-multi-index-600k",
            iterations: iterations,
            elapsed: elapsed,
            latenciesMs: sampledLatencies,
            metadata: [
                "total_ops": "\(iterations)",
                "index_count": "3",
                "indexes_working": "\(indexesWorking)",
                "sampled_latencies": "\(sampledLatencies.count)"
            ],
            systemMetrics: finalMetrics
        )
    }
    
    /// Stress test: 600k operations with memory pressure
    static func stressMemoryPressure() throws -> InternalBenchmarkResult {
        print("🔥 STRESS TEST: Memory Pressure (600k ops)")
        
        var config = DBConfig(storageEngine: "InMemory")
        config.autoCompactionEnabled = false
        let db = Database(config: config)
        try db.createTable("stress")
        
        let monitor = SystemMonitor(database: db)
        let initialMetrics = monitor.getCurrentMetrics()
        
        let iterations = 600_000
        let clock = ContinuousClock()
        let start = clock.now
        
        var sampledLatencies: [Double] = []
        sampledLatencies.reserveCapacity(iterations / 1000)
        
        // Use large records to stress memory
        let largeData = String(repeating: "X", count: 500) // 500 bytes per record
        
        for i in 0..<iterations {
            let t0 = (i % 1000 == 0) ? clock.now : start
            
            _ = try db.insert(into: "stress", row: [
                "id": .int(Int64(i)),
                "data": .string("\(largeData)_\(i)"),
                "timestamp": .int(Int64(Date().timeIntervalSince1970 * 1000))
            ])
            
            if i % 1000 == 0 {
                sampledLatencies.append(msDelta(t0, clock.now))
                
                // Sample memory every 1k ops
                let currentMem = monitor.getCurrentMetrics().memory.usedBytes
                if i % 50_000 == 0 && i > 0 {
                    let memMB = Double(currentMem) / 1_048_576.0
                    print("   📊 \(i) ops: Memory = \(String(format: "%.1f", memMB)) MB")
                }
            }
            
            if i > 0 && i % 100_000 == 0 {
                print("   Progress: \(i)/\(iterations) (\(i*100/iterations)%)")
            }
        }
        
        let elapsed = clock.now - start
        let finalMetrics = monitor.getCurrentMetrics()
        
        let memoryUsedMB = Double(finalMetrics.memory.usedBytes) / 1_048_576.0
        let memoryDelta = Double(finalMetrics.memory.usedBytes - initialMetrics.memory.usedBytes) / 1_048_576.0
        
        print("   ✅ Completed: \(iterations) large inserts")
        print("   📊 Total memory: \(String(format: "%.1f", memoryUsedMB)) MB")
        print("   📊 Memory delta: \(String(format: "%.1f", memoryDelta)) MB")
        
        return InternalBenchmarkResult(
            name: "stress-memory-600k",
            iterations: iterations,
            elapsed: elapsed,
            latenciesMs: sampledLatencies,
            metadata: [
                "total_ops": "\(iterations)",
                "record_size": "500",
                "total_memory_mb": String(format: "%.1f", memoryUsedMB),
                "memory_delta_mb": String(format: "%.1f", memoryDelta),
                "sampled_latencies": "\(sampledLatencies.count)"
            ],
            systemMetrics: finalMetrics
        )
    }
    
    /// Stress test: 600k range queries
    static func stressRangeQueries() throws -> InternalBenchmarkResult {
        print("🔥 STRESS TEST: Range Queries (600k ops)")
        
        var config = DBConfig(storageEngine: "InMemory")
        config.autoCompactionEnabled = false
        let db = Database(config: config)
        try db.createTable("stress")
        try db.createIndex(name: "idx_stress", on: "stress", columns: ["key"], using: "SkipList")
        
        // Pre-populate with sorted keys
        let uniqueKeys = 100_000
        print("   📝 Pre-populating \(uniqueKeys) sorted keys...")
        for i in 0..<uniqueKeys {
            _ = try db.insert(into: "stress", row: [
                "key": .string(String(format: "key_%08d", i)),
                "value": .int(Int64(i))
            ])
            
            if i > 0 && i % 20_000 == 0 {
                print("   Progress: \(i)/\(uniqueKeys)")
            }
        }
        
        let monitor = SystemMonitor(database: db)
        let initialMetrics = monitor.getCurrentMetrics()
        
        let iterations = 600_000
        let clock = ContinuousClock()
        let start = clock.now
        
        var sampledLatencies: [Double] = []
        sampledLatencies.reserveCapacity(iterations / 1000)
        
        var totalResultsReturned: UInt64 = 0
        
        for i in 0..<iterations {
            let rangeStart = BenchmarkCLI.withSeededRNG { rng in
                Int.random(in: 0..<(uniqueKeys - 100), using: &rng!)
            }
            let rangeSize = BenchmarkCLI.withSeededRNG { rng in
                Int.random(in: 10...100, using: &rng!)
            }
            
            let lo = Value.string(String(format: "key_%08d", rangeStart))
            let hi = Value.string(String(format: "key_%08d", rangeStart + rangeSize))
            
            let t0 = (i % 1000 == 0) ? clock.now : start
            let hits = try db.indexRangeTyped(table: "stress", index: "idx_stress", lo: lo, hi: hi)
            
            totalResultsReturned += UInt64(hits.count)
            
            if i % 1000 == 0 {
                sampledLatencies.append(msDelta(t0, clock.now))
            }
            
            if i > 0 && i % 100_000 == 0 {
                print("   Progress: \(i)/\(iterations) (\(i*100/iterations)%)")
            }
        }
        
        let elapsed = clock.now - start
        let finalMetrics = monitor.getCurrentMetrics()
        
        let avgResultsPerQuery = Double(totalResultsReturned) / Double(iterations)
        
        print("   ✅ Completed: \(iterations) range queries")
        print("   📊 Total results returned: \(totalResultsReturned)")
        print("   📊 Avg results per query: \(String(format: "%.1f", avgResultsPerQuery))")
        
        return InternalBenchmarkResult(
            name: "stress-range-queries-600k",
            iterations: iterations,
            elapsed: elapsed,
            latenciesMs: sampledLatencies,
            metadata: [
                "total_ops": "\(iterations)",
                "total_results": "\(totalResultsReturned)",
                "avg_results_per_query": String(format: "%.1f", avgResultsPerQuery),
                "sampled_latencies": "\(sampledLatencies.count)"
            ],
            systemMetrics: finalMetrics
        )
    }
}

