//
//  Benchmarks.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// Theme: Benchmark harness measuring core engine throughput and latency.

import Foundation
import ColibriCore

private struct BenchmarkResult {
    let name: String
    let iterations: Int
    let elapsed: Duration

    var opsPerSecond: Double {
        guard elapsed > .zero else { return 0 }
        let seconds = Double(elapsed.components.seconds) + Double(elapsed.components.attoseconds) / 1_000_000_000_000_000_000.0
        return Double(iterations) / seconds
    }

    func printSummary() {
        let millis = Double(elapsed.components.seconds) * 1_000 + Double(elapsed.components.attoseconds) / 1_000_000_000_000_000.0
        let formattedOps = String(format: "%.2f", opsPerSecond)
        print("[\(name)] iterations=\(iterations) elapsed_ms=\(String(format: "%.3f", millis)) throughput_ops_s=\(formattedOps)")
    }
}

private enum Scenario: String, CaseIterable {
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
        let iterations = args.first.flatMap { Int($0) } ?? 10_000
        let scenarioArg = args.dropFirst().first
        let scenarios: [Scenario]
        if let selected = scenarioArg.flatMap({ Scenario.from($0) }) {
            scenarios = [selected]
        } else {
            scenarios = Scenario.allCases
        }

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
        let request = QueryRequest(root: users, joins: [join], orderBy: [SortOperator.SortKey(column: "o.total", ascending: false)], parallelism: 2)

        let clock = ContinuousClock()
        let start = clock.now
        let rows = try db.executeQuery(request)
        precondition(!rows.isEmpty)
        let elapsed = clock.now - start
        return BenchmarkResult(name: Scenario.plannerJoin.rawValue, iterations: rows.count, elapsed: elapsed)
    }

    private static func printUsage() {
        print("Usage: benchmarks [iterations] [scenario]")
        print("  iterations: numero di iterazioni per scenario (default 10000)")
        print("  scenario:   uno tra \(Scenario.allCases.map { $0.rawValue }.joined(separator: ", ")) oppure omesso per eseguire tutti")
        print("Examples:")
        print("  benchmarks 5000 heap-insert")
        print("  benchmarks 2000")
    }
}
