import Foundation
import ColibriCore

extension BenchmarkCLI {
    // MARK: - Heap (base)
    static func runHeapInsert(iterations: Int) throws -> BenchmarkResult {
        var config = DBConfig(storageEngine: "InMemory")
        config.autoCompactionEnabled = false
        let db = Database(config: config)
        try db.createTable("bench")
        
        let (latencies, elapsed) = try measureLatenciesVoid(iterations: iterations) {
            let i = Int.random(in: 0..<iterations) // Randomize to avoid cache effects
            _ = try db.insert(into: "bench", row: ["id": .int(Int64(i)), "payload": .string("value-\(i)")])
        }
        
        return BenchmarkResult(name: Scenario.heapInsert.rawValue, iterations: iterations, elapsed: elapsed, latenciesMs: latencies, metadata: ["storage":"InMemory"]) 
    }

    static func runHeapScan(iterations: Int) throws -> BenchmarkResult {
        var config = DBConfig(storageEngine: "InMemory")
        config.autoCompactionEnabled = false
        let db = Database(config: config)
        try db.createTable("bench")
        for i in 0..<iterations {
            _ = try db.insert(into: "bench", row: ["id": .int(Int64(i)), "payload": .string("value-\(i)")])
        }
        
        // Per scan, misuriamo multiple scansioni per avere latenze significative
        let scanIterations = max(1, iterations / 100) // Scan multipli per avere dati significativi
        let (results, latencies, elapsed) = try measureLatencies(iterations: scanIterations) {
            return try db.scan("bench")
        }
        
        let totalRows = results.reduce(0) { $0 + $1.count }
        precondition(totalRows > 0)
        return BenchmarkResult(name: Scenario.heapScan.rawValue, iterations: scanIterations, elapsed: elapsed, latenciesMs: latencies, metadata: ["storage":"InMemory", "total_rows":"\(totalRows)"]) 
    }

    // MARK: - Heap (estesi)
    static func runHeapDelete(iterations: Int, granular: Bool) throws -> BenchmarkResult {
        let fm = FileManager.default
        let tmp = fm.temporaryDirectory.appendingPathComponent("colibridb-bench-\(UUID().uuidString)", isDirectory: true)
        try fm.createDirectory(at: tmp, withIntermediateDirectories: true)
        defer { try? fm.removeItem(at: tmp) }
        var cfg = DBConfig(dataDir: tmp.path, storageEngine: "InMemory")
        cfg.autoCompactionEnabled = false
        let db = Database(config: cfg)
        try db.createTable("t")
        for i in 0..<iterations { _ = try db.insert(into: "t", row: ["id": .int(Int64(i)), "p": .string("v\(i)")]) }
        let clock = ContinuousClock(); let start = clock.now
        var total = 0
        if granular {
            var lat: [Double] = []; lat.reserveCapacity(iterations)
            for i in 0..<iterations {
                let t0 = clock.now
                total &+= try db.deleteEquals(table: "t", column: "id", value: .int(Int64(i)))
                let t1 = clock.now
                lat.append(msDelta(t0, t1))
            }
            let elapsed = clock.now - start
            return BenchmarkResult(name: Scenario.heapDelete.rawValue, iterations: total, elapsed: elapsed, latenciesMs: lat, metadata: ["storage":"InMemory"]) 
        } else {
            for i in 0..<iterations { total &+= try db.deleteEquals(table: "t", column: "id", value: .int(Int64(i))) }
            let elapsed = clock.now - start
            return BenchmarkResult(name: Scenario.heapDelete.rawValue, iterations: total, elapsed: elapsed, metadata: ["storage":"InMemory"]) 
        }
    }

    static func runHeapDeleteBatch(iterations: Int, granular: Bool) throws -> BenchmarkResult {
        let fm = FileManager.default
        let tmp = fm.temporaryDirectory.appendingPathComponent("colibridb-bench-\(UUID().uuidString)", isDirectory: true)
        try fm.createDirectory(at: tmp, withIntermediateDirectories: true)
        defer { try? fm.removeItem(at: tmp) }
        var cfg = DBConfig(dataDir: tmp.path, storageEngine: "InMemory")
        cfg.autoCompactionEnabled = false
        let db = Database(config: cfg)
        try db.createTable("t")
        
        // Insert all rows and collect RIDs
        var rids: [RID] = []
        rids.reserveCapacity(iterations)
        for i in 0..<iterations { 
            let rid = try db.insert(into: "t", row: ["id": .int(Int64(i)), "p": .string("v\(i)")])
            rids.append(rid)
        }
        
        let clock = ContinuousClock(); let start = clock.now
        var total = 0
        if granular {
            var lat: [Double] = []; lat.reserveCapacity(iterations / 100) // Batch every 100 deletes
            for batchStart in stride(from: 0, to: iterations, by: 100) {
                let t0 = clock.now
                let batchEnd = min(batchStart + 100, iterations)
                let batchRids = Array(rids[batchStart..<batchEnd])
                total &+= try db.deleteBatch(table: "t", rids: batchRids)
                let t1 = clock.now
                lat.append(msDelta(t0, t1))
            }
            let elapsed = clock.now - start
            return BenchmarkResult(name: "heap-delete-batch", iterations: total, elapsed: elapsed, latenciesMs: lat, metadata: ["storage":"InMemory", "batch_size":"100"]) 
        } else {
            // Single batch delete
            total = try db.deleteBatch(table: "t", rids: rids)
            let elapsed = clock.now - start
            return BenchmarkResult(name: "heap-delete-batch", iterations: total, elapsed: elapsed, metadata: ["storage":"InMemory", "batch_size":"all"]) 
        }
    }

    static func runHeapReadRID(iterations: Int, granular: Bool) throws -> BenchmarkResult {
        let fm = FileManager.default
        let tmp = fm.temporaryDirectory.appendingPathComponent("colibridb-bench-\(UUID().uuidString)", isDirectory: true)
        try fm.createDirectory(at: tmp, withIntermediateDirectories: true)
        defer { try? fm.removeItem(at: tmp) }
        var cfg = DBConfig(dataDir: tmp.path, storageEngine: "InMemory")
        cfg.autoCompactionEnabled = false
        let db = Database(config: cfg)
        try db.createTable("t")
        var rids: [RID] = []
        rids.reserveCapacity(iterations)
        for i in 0..<iterations {
            let rid = try db.insert(into: "t", row: ["id": .int(Int64(i)), "p": .string("v\(i)")])
            rids.append(rid)
        }
        let clock = ContinuousClock(); let start = clock.now
        var sum = 0
        if granular {
            var lat: [Double] = []; lat.reserveCapacity(rids.count)
            for rid in rids {
                let t0 = clock.now
                let row = try db.readRow(table: "t", rid: rid)
                let t1 = clock.now
                if case .int(let v) = row["id"] { sum &+= Int(v) }
                lat.append(msDelta(t0, t1))
            }
            let elapsed = clock.now - start
            precondition(sum >= 0)
            return BenchmarkResult(name: Scenario.heapReadRID.rawValue, iterations: rids.count, elapsed: elapsed, latenciesMs: lat, metadata: ["storage":"InMemory"]) 
        } else {
            for rid in rids {
                let row = try db.readRow(table: "t", rid: rid)
                if case .int(let v) = row["id"] { sum &+= Int(v) }
            }
            let elapsed = clock.now - start
            precondition(sum >= 0)
            return BenchmarkResult(name: Scenario.heapReadRID.rawValue, iterations: rids.count, elapsed: elapsed, metadata: ["storage":"InMemory"]) 
        }
    }
}

// helpers in Benchmarks+Helpers.swift


