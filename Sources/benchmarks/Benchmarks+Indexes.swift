import Foundation
import ColibriCore

extension BenchmarkCLI {
    // MARK: - Indici in‑memory
    static func runInMemoryIndexLookup(iterations: Int, kind: String, granular: Bool) throws -> BenchmarkResult {
        var cfg = DBConfig(storageEngine: "InMemory")
        cfg.autoCompactionEnabled = false
        let db = Database(config: cfg)
        try db.createTable("t")
        let idxName = "ix_\(UUID().uuidString.prefix(8))"
        try db.createIndex(name: idxName, on: "t", columns: ["k"], using: kind)
        for i in 0..<iterations {
            _ = try db.insert(into: "t", row: ["k": .string("k\(i)"), "v": .int(Int64(i))])
        }
        let clock = ContinuousClock(); let start = clock.now
        var found = 0
        if granular {
            var lat: [Double] = []; lat.reserveCapacity(iterations)
            for i in 0..<iterations {
                let t0 = clock.now
                let hits = try db.indexSearchEqualsTyped(table: "t", index: idxName, value: .string("k\(i)"))
                let t1 = clock.now
                if !hits.isEmpty { found &+= 1 }
                lat.append(msDelta(t0, t1))
            }
            let elapsed = clock.now - start
            precondition(found == iterations)
            return BenchmarkResult(name: "idx-\(kind.lowercased())-lookup", iterations: iterations, elapsed: elapsed, latenciesMs: lat, metadata: ["kind":kind, "storage":"InMemory"]) 
        } else {
            for i in 0..<iterations {
                let hits = try db.indexSearchEqualsTyped(table: "t", index: idxName, value: .string("k\(i)"))
                if !hits.isEmpty { found &+= 1 }
            }
            let elapsed = clock.now - start
            precondition(found == iterations)
            return BenchmarkResult(name: "idx-\(kind.lowercased())-lookup", iterations: iterations, elapsed: elapsed, metadata: ["kind":kind, "storage":"InMemory"]) 
        }
    }

    static func runInMemoryIndexRange(iterations: Int, kind: String, granular: Bool) throws -> BenchmarkResult {
        var cfg = DBConfig(storageEngine: "InMemory")
        cfg.autoCompactionEnabled = false
        let db = Database(config: cfg)
        try db.createTable("t")
        let idxName = "ix_\(UUID().uuidString.prefix(8))"
        try db.createIndex(name: idxName, on: "t", columns: ["k"], using: kind)
        for i in 0..<iterations {
            _ = try db.insert(into: "t", row: ["k": .string(String(format: "k%08d", i)), "v": .int(Int64(i))])
        }
        let lo = Value.string(String(format: "k%08d", 0))
        let hi = Value.string(String(format: "k%08d", iterations - 1))
        let clock = ContinuousClock(); let start = clock.now
        if granular {
            let q = min(iterations, 500)
            var lat: [Double] = []; lat.reserveCapacity(q)
            var total = 0
            for _ in 0..<q {
                let t0 = clock.now
                let hits = try db.indexRangeTyped(table: "t", index: idxName, lo: lo, hi: hi)
                let t1 = clock.now
                total &+= hits.count
                lat.append(msDelta(t0, t1))
            }
            let elapsed = clock.now - start
            precondition(total > 0)
            return BenchmarkResult(name: "idx-\(kind.lowercased())-range", iterations: q, elapsed: elapsed, latenciesMs: lat, metadata: ["kind":kind,"storage":"InMemory","queries":"\(q)"]) 
        } else {
            let hits = try db.indexRangeTyped(table: "t", index: idxName, lo: lo, hi: hi)
            let elapsed = clock.now - start
            precondition(!hits.isEmpty)
            return BenchmarkResult(name: "idx-\(kind.lowercased())-range", iterations: hits.count, elapsed: elapsed, metadata: ["kind":kind, "storage":"InMemory"]) 
        }
    }
}


