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
        // Warm-up: 1k lookups
        let warm = min(iterations, 1_000)
        for i in 0..<warm { _ = try db.indexSearchEqualsTyped(table: "t", index: idxName, value: .string("k\(i)")) }
        let clock = ContinuousClock(); let start = clock.now
        var found = 0
        if granular {
            var lat: [Double] = []; lat.reserveCapacity(iterations)
            for i in 0..<iterations {
                let t0 = clock.now
                let hits = try db.indexSearchEqualsTyped(table: "t", index: idxName, value: .string("k\(i)"))
                let t1 = clock.now
                if !hits.isEmpty { found &+= 1 }
                lat.append(BenchmarkCLI.msDelta(t0, t1))
            }
            let elapsed = clock.now - start
            if found != iterations {
                print("⚠️  Warning: Found \(found) out of \(iterations) expected items for \(kind) index")
            }
            return BenchmarkResult(name: "idx-\(kind.lowercased())-lookup", iterations: iterations, elapsed: elapsed, latenciesMs: lat, metadata: ["kind":kind, "storage":"InMemory", "warmup_done":"true"])
        } else {
            for i in 0..<iterations {
                let hits = try db.indexSearchEqualsTyped(table: "t", index: idxName, value: .string("k\(i)"))
                if !hits.isEmpty { found &+= 1 }
            }
            let elapsed = clock.now - start
            if found != iterations {
                print("⚠️  Warning: Found \(found) out of \(iterations) expected items for \(kind) index")
            }
            return BenchmarkResult(name: "idx-\(kind.lowercased())-lookup", iterations: iterations, elapsed: elapsed, metadata: ["kind":kind, "storage":"InMemory", "warmup_done":"true"])
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
        // Warm-up range full
        let lo = Value.string(String(format: "k%08d", 0))
        let hi = Value.string(String(format: "k%08d", iterations - 1))
        _ = try db.indexRangeTyped(table: "t", index: idxName, lo: lo, hi: hi)
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
                lat.append(BenchmarkCLI.msDelta(t0, t1))
            }
            let elapsed = clock.now - start
            if total <= 0 {
                print("⚠️  Warning: No items found in range query for \(kind) index")
                return BenchmarkResult(name: "idx-\(kind.lowercased())-range", iterations: iterations, elapsed: elapsed, latenciesMs: lat, metadata: ["kind":kind, "storage":"InMemory", "warmup_done":"true"])
            }
            return BenchmarkResult(name: "idx-\(kind.lowercased())-range", iterations: q, elapsed: elapsed, latenciesMs: lat, metadata: ["kind":kind,"storage":"InMemory","queries":"\(q)", "warmup_done":"true"])
        } else {
            let hits = try db.indexRangeTyped(table: "t", index: idxName, lo: lo, hi: hi)
            let elapsed = clock.now - start
            if hits.isEmpty {
                print("⚠️  Warning: No items found in range query for \(kind) index")
                return BenchmarkResult(name: "idx-\(kind.lowercased())-range", iterations: iterations, elapsed: elapsed, metadata: ["kind":kind, "storage":"InMemory", "warmup_done":"true"])
            }
            return BenchmarkResult(name: "idx-\(kind.lowercased())-range", iterations: hits.count, elapsed: elapsed, metadata: ["kind":kind, "storage":"InMemory", "warmup_done":"true"])
        }
    }

    static func runIndexTombstone(iterations: Int, kind: String, granular: Bool) throws -> BenchmarkResult {
        var cfg = DBConfig(storageEngine: "InMemory")
        cfg.autoCompactionEnabled = false
        let db = Database(config: cfg)
        try db.createTable("docs")
        let indexName = "ix_tomb_\(UUID().uuidString.prefix(6))"
        try db.createIndex(name: indexName, on: "docs", columns: ["title"], using: kind)

        for i in 0..<iterations {
            _ = try db.insert(into: "docs", row: ["title": .string("doc-\(i)"), "body": .string("draft")])
        }
        for i in stride(from: 0, to: iterations, by: 2) {
            _ = try db.deleteEquals(table: "docs", column: "title", value: .string("doc-\(i)"))
        }

        let clock = ContinuousClock(); let start = clock.now
        var latencies: [Double] = []
        var invisibleHits = 0
        var visibleHits = 0

        let queries = min(iterations, granular ? iterations : max(1, iterations / 2))
        for i in 0..<queries {
            let t0 = clock.now
            let hits = try db.indexSearchEqualsTyped(table: "docs", index: indexName, value: .string("doc-\(i)"))
            if i % 2 == 0 {
                if hits.isEmpty { invisibleHits += 1 }
            } else {
                if !hits.isEmpty { visibleHits += 1 }
            }
            let t1 = clock.now
            latencies.append(BenchmarkCLI.msDelta(t0, t1))
        }

        let vacuumStart = clock.now
        _ = try db.compactTable(table: "docs", pageId: nil)
        let vacuumEnd = clock.now
        var postVacuumInvisible = 0
        for i in stride(from: 0, to: iterations, by: 2) {
            let hits = try db.indexSearchEqualsTyped(table: "docs", index: indexName, value: .string("doc-\(i)"))
            if hits.isEmpty { postVacuumInvisible += 1 }
        }

        let elapsed = clock.now - start
        let averageLatency = latencies.reduce(0, +) / Double(max(latencies.count, 1))
        let latencySeries = granular ? latencies : Array(repeating: averageLatency, count: max(1, queries))
        return BenchmarkResult(
            name: "idx-\(kind.lowercased())-tombstone",
            iterations: queries,
            elapsed: elapsed,
            latenciesMs: latencySeries,
            metadata: [
                "kind": kind,
                "storage": "InMemory",
                "vacuum_time_ms": String(format: "%.3f", BenchmarkCLI.msDelta(vacuumStart, vacuumEnd)),
                "queries": "\(queries)",
                "invisible_before": "\(invisibleHits)",
                "visible_before": "\(visibleHits)",
                "invisible_after": "\(postVacuumInvisible)"
            ]
        )
    }
}


