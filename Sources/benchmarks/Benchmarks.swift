//
//  Benchmarks.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// Theme: Benchmark harness measuring core engine throughput and latency.

import Foundation
import ColibriCore

struct BenchmarkResult {
    let name: String
    let iterations: Int
    let elapsed: Duration
    let latenciesMs: [Double]
    let metadata: [String: String]

    private var totalMs: Double {
        Double(elapsed.components.seconds) * 1_000 + Double(elapsed.components.attoseconds) / 1_000_000_000_000_000.0
    }

    var opsPerSecond: Double {
        guard elapsed > .zero else { return 0 }
        let seconds = Double(elapsed.components.seconds) + Double(elapsed.components.attoseconds) / 1_000_000_000_000_000_000.0
        return Double(max(1, iterations)) / seconds
    }

    private var sorted: [Double] { latenciesMs.sorted() }
    private func percentile(_ p: Double) -> Double {
        guard !latenciesMs.isEmpty else { return 0 }
        let s = sorted
        let rank = max(0, min(s.count - 1, Int(round((p/100.0) * Double(s.count - 1)))))
        return s[rank]
    }
    private var mean: Double {
        guard !latenciesMs.isEmpty else { return 0 }
        return latenciesMs.reduce(0, +) / Double(latenciesMs.count)
    }
    private var stddev: Double {
        guard !latenciesMs.isEmpty else { return 0 }
        let m = mean
        let v = latenciesMs.reduce(0.0) { $0 + ($1 - m) * ($1 - m) } / Double(latenciesMs.count)
        return v.squareRoot()
    }
    private var minMs: Double { sorted.first ?? 0 }
    private var maxMs: Double { sorted.last ?? 0 }

    func printSummary() {
        let formattedOps = String(format: "%.2f", opsPerSecond)
        print("[\(name)] iterations=\(iterations) elapsed_ms=\(String(format: "%.3f", totalMs)) throughput_ops_s=\(formattedOps)")
    }

    enum OutputFormat { case text, json }

    func printReport(format: OutputFormat) {
        switch format {
        case .text:
            let ts = ISO8601DateFormatter().string(from: Date())
            print("--- Report: \(name) ---")
            print("quando=\(ts)")
            print("operazioni=\(latenciesMs.count) totale_ms=\(String(format: "%.3f", totalMs)) ops_al_sec=\(String(format: "%.2f", opsPerSecond))")
            print("latenza_ms: media=\(String(format: "%.4f", mean)) p50=\(String(format: "%.4f", percentile(50))) p90=\(String(format: "%.4f", percentile(90))) p95=\(String(format: "%.4f", percentile(95))) p99=\(String(format: "%.4f", percentile(99))) min=\(String(format: "%.4f", minMs)) max=\(String(format: "%.4f", maxMs)) stddev=\(String(format: "%.4f", stddev))")
            if !metadata.isEmpty {
                print("metadati:")
                for (k, v) in metadata.sorted(by: { $0.key < $1.key }) {
                    print("  \(k)=\(v)")
                }
            }
        case .json:
            struct Payload: Codable {
                struct Lat: Codable { let count:Int; let total_ms:Double; let mean_ms:Double; let p50_ms:Double; let p90_ms:Double; let p95_ms:Double; let p99_ms:Double; let min_ms:Double; let max_ms:Double; let stddev_ms:Double }
                let scenario: String
                let iterations: Int
                let throughput_ops_s: Double
                let when: String
                let latency_ms: Lat
                let metadata: [String:String]
            }
            let ts = ISO8601DateFormatter().string(from: Date())
            let lat = Payload.Lat(count: latenciesMs.count,
                                   total_ms: totalMs,
                                   mean_ms: mean,
                                   p50_ms: percentile(50),
                                   p90_ms: percentile(90),
                                   p95_ms: percentile(95),
                                   p99_ms: percentile(99),
                                   min_ms: minMs,
                                   max_ms: maxMs,
                                   stddev_ms: stddev)
            let p = Payload(scenario: name, iterations: iterations, throughput_ops_s: opsPerSecond, when: ts, latency_ms: lat, metadata: metadata)
            let enc = JSONEncoder(); enc.outputFormatting = [.prettyPrinted, .sortedKeys]
            if let data = try? enc.encode(p), let s = String(data: data, encoding: .utf8) { print(s) }
        }
    }

    // Convenienze
    init(name: String, iterations: Int, elapsed: Duration) {
        self.name = name
        self.iterations = iterations
        self.elapsed = elapsed
        let ms = Double(elapsed.components.seconds) * 1_000 + Double(elapsed.components.attoseconds) / 1_000_000_000_000_000.0
        let count = max(1, iterations)
        self.latenciesMs = Array(repeating: ms / Double(count), count: count)
        self.metadata = [:]
    }

    init(name: String, iterations: Int, elapsed: Duration, metadata: [String:String]) {
        self.name = name
        self.iterations = iterations
        self.elapsed = elapsed
        let ms = Double(elapsed.components.seconds) * 1_000 + Double(elapsed.components.attoseconds) / 1_000_000_000_000_000.0
        let count = max(1, iterations)
        self.latenciesMs = Array(repeating: ms / Double(count), count: count)
        self.metadata = metadata
    }

    init(name: String, iterations: Int, elapsed: Duration, latenciesMs: [Double]) {
        self.name = name
        self.iterations = iterations
        self.elapsed = elapsed
        self.latenciesMs = latenciesMs
        self.metadata = [:]
    }

    init(name: String, iterations: Int, elapsed: Duration, latenciesMs: [Double], metadata: [String:String]) {
        self.name = name
        self.iterations = iterations
        self.elapsed = elapsed
        self.latenciesMs = latenciesMs
        self.metadata = metadata
    }
}

private enum Scenario: String, CaseIterable {
    // Minimal scenarios supported by this target
    case heapInsert = "heap-insert"
    case heapScan = "heap-scan"
    case btreeLookup = "btree-lookup"
    case plannerJoin = "planner-join"

    static func from(_ string: String) -> Scenario? { Scenario(rawValue: string.lowercased()) }
}

@main
struct BenchmarkCLI {
    static func main() throws {
        let args = Array(CommandLine.arguments.dropFirst())
        if args.contains("--help") || args.contains("-h") {
            printUsage()
            return
        }

        var iterations = 10_000
        var selected: Scenario? = nil
        let workers = ProcessInfo.processInfo.activeProcessorCount
        let userSetWorkers = false
        let granular = false
        let formatJSON = false

        for a in args {
            if let n = Int(a) { iterations = n; continue }
            if let s = Scenario.from(a) { selected = s; continue }
            if a.hasPrefix("--workers=") {
                let parts = a.split(separator: "=")
                if let last = parts.last, let n = Int(last) { workers = max(1, n); userSetWorkers = true }
            }
            if a == "--granular" { granular = true }
            if a == "--json" || a == "--format=json" { formatJSON = true }
        }

        let scenarios = selected.map { [$0] } ?? Scenario.allCases
        for scenario in scenarios {
            let result: BenchmarkResult
            switch scenario {
            case .heapInsert:
                result = try runHeapInsert(iterations: iterations)
            case .heapScan:
                result = try runHeapScan(iterations: iterations)
            case .btreeLookup:
                result = try runBTreeLookup(iterations: iterations)
            case .plannerJoin:
                result = try runPlannerJoin(iterations: iterations)
            }
            result.printSummary()
            result.printReport(format: formatJSON ? .json : .text)
        }
    }

    private static func runHeapInsert(iterations: Int) throws -> BenchmarkResult {
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
        return BenchmarkResult(name: Scenario.heapInsert.rawValue, iterations: iterations, elapsed: elapsed)
    }

    private static func runHeapScan(iterations: Int) throws -> BenchmarkResult {
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
        return BenchmarkResult(name: Scenario.heapScan.rawValue, iterations: rows.count, elapsed: elapsed)
    }

    private static func runBTreeLookup(iterations: Int) throws -> BenchmarkResult {
        let fm = FileManager.default
        let tempDir = fm.temporaryDirectory.appendingPathComponent(UUID().uuidString, isDirectory: true)
        try fm.createDirectory(at: tempDir, withIntermediateDirectories: true)
        defer { try? fm.removeItem(at: tempDir) }

        var config = DBConfig(dataDir: tempDir.path)
        config.autoCompactionEnabled = false
        let db = Database(config: config)
        try db.createTable("bench")
        for i in 0..<iterations {
            _ = try db.insert(into: "bench", row: ["id": .int(Int64(i)), "payload": .string("value-\(i)")])
        }
        try db.createIndex(name: "idx_bench_id", on: "bench", columns: ["id"], using: "BTree")
        try db.rebuildIndexBulk(table: "bench", index: "idx_bench_id")

        let clock = ContinuousClock()
        let start = clock.now
        for i in 0..<iterations {
            let hits = try db.indexSearchEqualsTyped(table: "bench", index: "idx_bench_id", value: .int(Int64(i)))
            precondition(!hits.isEmpty)
        }
        let elapsed = clock.now - start
        return BenchmarkResult(name: Scenario.btreeLookup.rawValue, iterations: iterations, elapsed: elapsed)
    }

    private static func runPlannerJoin(iterations: Int) throws -> BenchmarkResult {
        let fm = FileManager.default
        let tempDir = fm.temporaryDirectory.appendingPathComponent(UUID().uuidString, isDirectory: true)
        try fm.createDirectory(at: tempDir, withIntermediateDirectories: true)
        defer { try? fm.removeItem(at: tempDir) }

        var config = DBConfig(storageEngine: "InMemory")
        config.autoCompactionEnabled = false
        config.walEnabled = false
        config.dataDir = tempDir.path
        let db = Database(config: config)
        try db.createTable("users")
        try db.createTable("orders")
        for u in 0..<iterations {
            _ = try db.insert(into: "users", row: ["id": .int(Int64(u)), "region": .string(u % 2 == 0 ? "EU" : "US")])
            _ = try db.insert(into: "orders", row: ["id": .int(Int64(u)), "user_id": .int(Int64(u)), "total": .double(Double.random(in: 1..<100))])
        }
        try db.createIndex(name: "idx_orders_user", on: "orders", columns: ["user_id"], using: "BTree")
        try db.rebuildIndexBulk(table: "orders", index: "idx_orders_user")

        let predicate = QueryPredicate(column: "region", op: .equals, value: .string("EU"), selectivityHint: 0.5)
        let users = QueryTableRef(name: "users", predicates: [predicate], projection: ["id", "region"])
        let orders = QueryTableRef(name: "orders", alias: "o", projection: ["id", "user_id", "total"], indexHint: "idx_orders_user")
        let join = QueryJoinSpec(table: orders, leftColumns: ["users.id"], rightColumns: ["o.user_id"])
        let request = QueryRequest(root: users, joins: [join], orderBy: [SortKey(column: "o.total", ascending: false)], parallelism: 2)

        let clock = ContinuousClock()
        let start = clock.now
        let rows = try db.executeQuery(request)
        precondition(!rows.isEmpty)
        let elapsed = clock.now - start
        return BenchmarkResult(name: Scenario.plannerJoin.rawValue, iterations: rows.count, elapsed: elapsed)
    }

    private static func printUsage() {
        print("Uso: benchmarks [iterations] [scenario] [--workers=N] [--granular] [--json]")
        print("  iterations: numero di iterazioni (default 10000; alcuni scenari sono limitati)")
        print("  scenario:   uno tra \(Scenario.allCases.map { $0.rawValue }.joined(separator: ", ")) oppure omesso per eseguire tutti")
        print("  --workers:  per scenari concorrenti (es. tx-contention), default = logical cores")
        print("  --granular: misura la latenza per singola operazione dove applicabile")
        print("  --json:     stampa report in formato JSON (oltre al summary)")
        print("Esempi:")
        print("  benchmarks 5000 btree-bulk-build")
        print("  benchmarks 20000 tx-contention --workers=8 --granular --json")
    }
}
