import Foundation
import ColibriCore

extension BenchmarkCLI {
    // MARK: - Heap (base)
    static func runHeapInsert(iterations: Int) throws -> BenchmarkResult {
        var config = DBConfig(storageEngine: "InMemory")
        config.autoCompactionEnabled = false
        let db = Database(config: config)
        try db.createTable("bench")
        let clock = ContinuousClock()
        let start = clock.now
        for i in 0..<iterations {
            _ = try db.insert(into: "bench", row: ["id": .int(Int64(i)), "payload": .string("value-\(i)")])
        }
        let elapsed = clock.now - start
        return BenchmarkResult(name: Scenario.heapInsert.rawValue, iterations: iterations, elapsed: elapsed, metadata: ["storage":"InMemory"]) 
    }

    static func runHeapScan(iterations: Int) throws -> BenchmarkResult {
        var config = DBConfig(storageEngine: "InMemory")
        config.autoCompactionEnabled = false
        let db = Database(config: config)
        try db.createTable("bench")
        for i in 0..<iterations {
            _ = try db.insert(into: "bench", row: ["id": .int(Int64(i)), "payload": .string("value-\(i)")])
        }
        let clock = ContinuousClock()
        let start = clock.now
        let rows = try db.scan("bench")
        precondition(rows.count == iterations)
        let elapsed = clock.now - start
        return BenchmarkResult(name: Scenario.heapScan.rawValue, iterations: rows.count, elapsed: elapsed, metadata: ["storage":"InMemory"]) 
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


