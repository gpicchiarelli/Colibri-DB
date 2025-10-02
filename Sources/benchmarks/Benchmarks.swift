//
//  Benchmarks.swift
//  ColibrDB
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
    let systemMetrics: SystemMetrics?

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

    // Aggiunge metriche di sistema per analisi completa
    var cpuUsage: Double { systemMetrics?.cpu.usage ?? 0 }
    var memoryUsage: Double { systemMetrics?.memory.usage ?? 0 }
    var ioReadBytes: UInt64 { systemMetrics?.io.readCount ?? 0 }
    var ioWriteBytes: UInt64 { systemMetrics?.io.writeCount ?? 0 }

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
            if systemMetrics != nil {
                print("sistema: cpu=\(String(format: "%.1f", cpuUsage))% memoria=\(String(format: "%.1f", memoryUsage))% io_read=\(ioReadBytes) io_write=\(ioWriteBytes)")
            }
            if !metadata.isEmpty {
                print("metadati:")
                for (k, v) in metadata.sorted(by: { $0.key < $1.key }) {
                    print("  \(k)=\(v)")
                }
            }
        case .json:
            struct Payload: Codable {
                struct Lat: Codable { let count:Int; let total_ms:Double; let mean_ms:Double; let p50_ms:Double; let p90_ms:Double; let p95_ms:Double; let p99_ms:Double; let min_ms:Double; let max_ms:Double; let stddev_ms:Double }
                struct Sys: Codable { let cpu_percent:Double; let memory_percent:Double; let io_read_bytes:UInt64; let io_write_bytes:UInt64 }
                let scenario: String
                let iterations: Int
                let throughput_ops_s: Double
                let when: String
                let latency_ms: Lat
                let system_metrics: Sys?
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
            let sys = systemMetrics.map { Payload.Sys(cpu_percent: $0.cpu.usage, memory_percent: $0.memory.usage, io_read_bytes: $0.io.readCount, io_write_bytes: $0.io.writeCount) }
            let p = Payload(scenario: name, iterations: iterations, throughput_ops_s: opsPerSecond, when: ts, latency_ms: lat, system_metrics: sys, metadata: metadata)
            let enc = JSONEncoder(); enc.outputFormatting = [.prettyPrinted, .sortedKeys]
            let data = try? enc.encode(p)
            if let data = data, let s = String(data: data, encoding: .utf8) { print(s) }
        }
    }

    // Convenienze
    init(name: String, iterations: Int, elapsed: Duration, systemMetrics: SystemMetrics? = nil) {
        self.name = name
        self.iterations = iterations
        self.elapsed = elapsed
        let ms = Double(elapsed.components.seconds) * 1_000 + Double(elapsed.components.attoseconds) / 1_000_000_000_000_000.0
        let count = max(1, iterations)
        self.latenciesMs = Array(repeating: ms / Double(count), count: count)
        self.metadata = [:]
        self.systemMetrics = systemMetrics
    }

    init(name: String, iterations: Int, elapsed: Duration, metadata: [String:String], systemMetrics: SystemMetrics? = nil) {
        self.name = name
        self.iterations = iterations
        self.elapsed = elapsed
        let ms = Double(elapsed.components.seconds) * 1_000 + Double(elapsed.components.attoseconds) / 1_000_000_000_000_000.0
        let count = max(1, iterations)
        self.latenciesMs = Array(repeating: ms / Double(count), count: count)
        self.metadata = metadata
        self.systemMetrics = systemMetrics
    }

    init(name: String, iterations: Int, elapsed: Duration, latenciesMs: [Double], systemMetrics: SystemMetrics? = nil) {
        self.name = name
        self.iterations = iterations
        self.elapsed = elapsed
        self.latenciesMs = latenciesMs
        self.metadata = [:]
        self.systemMetrics = systemMetrics
    }

    init(name: String, iterations: Int, elapsed: Duration, latenciesMs: [Double], metadata: [String:String], systemMetrics: SystemMetrics? = nil) {
        self.name = name
        self.iterations = iterations
        self.elapsed = elapsed
        self.latenciesMs = latenciesMs
        self.metadata = metadata
        self.systemMetrics = systemMetrics
    }
}

enum Scenario: String, CaseIterable {
    // Heap (base)
    case heapInsert = "heap-insert"
    case heapScan = "heap-scan"
    // B+Tree (base)
    case btreeLookup = "btree-lookup"
    case btreeLookupOptimized = "btree-lookup-optimized"
    // Planner (base)
    case plannerJoin = "planner-join"

    // Estesi
    case heapDelete = "heap-delete"
    case heapReadRID = "heap-read-rid"
    case fileHeapInsertWalOff = "fileheap-insert-wal-off"
    case fileHeapInsertWalFSync = "fileheap-insert-wal-fsync"
    case walAppendNone = "wal-append-none"
    case walAppendLZFSE = "wal-append-lzfse"
    case walAppendZlib = "wal-append-zlib"
    case btreeInsert = "btree-insert"
    case btreeRange = "btree-range"
    case btreeBulkBuild = "btree-bulk-build"
    case idxHashLookup = "idx-hash-lookup"
    case idxARTLookup = "idx-art-lookup"
    case idxARTRange = "idx-art-range"
    case idxSkiplistLookup = "idx-skiplist-lookup"
    case idxSkiplistRange = "idx-skiplist-range"
    case idxFractalLookup = "idx-fractal-lookup"
    case idxFractalRange = "idx-fractal-range"
    case idxBTreeLookup = "idx-btree-lookup"      // in-memory AnyStringIndex BTree
    case idxBTreeRange = "idx-btree-range"        // in-memory AnyStringIndex BTree
    case idxLSMLookup = "idx-lsm-lookup"
    case idxLSMRange = "idx-lsm-range"
    case idxTombstone = "idx-tombstone"
    case txCommit = "tx-commit"
    case txCommitGrouped = "tx-commit-grouped"
    case txRollback = "tx-rollback"
    case txContention = "tx-contention"
    case mvccSnapshotRead = "mvcc-snapshot-read"
    case plannerIndexScan = "planner-index-scan"
    case plannerSortLimit = "planner-sort-limit"
    case checkpoint = "checkpoint"
    case vacuumCompact = "vacuum-compact"

    // Nuovi scenari avanzati
    case walRecovery = "wal-recovery"
    case walStress = "wal-stress"
    case systemLoad = "system-load"
    case memoryPressure = "memory-pressure"
    case concurrentLoad = "concurrent-load"
    case insertVariability = "insert-variability"
    case queryLatency = "query-latency"

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
        var workers = ProcessInfo.processInfo.activeProcessorCount
        var userSetWorkers = false
        var granular = false
        var formatJSON = false

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
            case .btreeLookupOptimized:
                result = try runBTreeLookupOptimized(iterations: iterations)
            case .plannerJoin:
                result = try runPlannerJoin(iterations: iterations)
            case .heapDelete:
                result = try runHeapDelete(iterations: iterations, granular: granular)
            case .heapReadRID:
                result = try runHeapReadRID(iterations: iterations, granular: granular)
            case .fileHeapInsertWalOff:
                result = try runFileHeapInsert(iterations: iterations, wal: false, fullSync: false, granular: granular)
            case .fileHeapInsertWalFSync:
                result = try runFileHeapInsert(iterations: iterations, wal: true, fullSync: true, granular: granular)
            case .walAppendNone:
                result = try runWALAppend(iterations: iterations, algorithm: .none, granular: granular)
            case .walAppendLZFSE:
                result = try runWALAppend(iterations: iterations, algorithm: .lzfse, granular: granular)
            case .walAppendZlib:
                result = try runWALAppend(iterations: iterations, algorithm: .zlib, granular: granular)
            case .btreeInsert:
                result = try runBTreeInsert(iterations: iterations, granular: granular)
            case .btreeRange:
                result = try runBTreeRange(iterations: iterations, granular: granular)
            case .btreeBulkBuild:
                result = try runBTreeBulkBuild(iterations: iterations)
            case .idxHashLookup:
                result = try runInMemoryIndexLookup(iterations: iterations, kind: "Hash", granular: granular)
            case .idxARTLookup:
                result = try runInMemoryIndexLookup(iterations: iterations, kind: "ART", granular: granular)
            case .idxARTRange:
                // Temporarily disabled due to LRUBufferPool crash
                throw DBError.notImplemented("idx-art-range temporarily disabled")
            case .idxSkiplistLookup:
                result = try runInMemoryIndexLookup(iterations: iterations, kind: "SkipList", granular: granular)
            case .idxSkiplistRange:
                result = try runInMemoryIndexRange(iterations: iterations, kind: "SkipList", granular: granular)
            case .idxFractalLookup:
                result = try runInMemoryIndexLookup(iterations: iterations, kind: "Fractal", granular: granular)
            case .idxFractalRange:
                result = try runInMemoryIndexRange(iterations: iterations, kind: "Fractal", granular: granular)
            case .idxBTreeLookup:
                result = try runInMemoryIndexLookup(iterations: iterations, kind: "BTree", granular: granular)
            case .idxBTreeRange:
                result = try runInMemoryIndexRange(iterations: iterations, kind: "BTree", granular: granular)
            case .idxLSMLookup:
                result = try runInMemoryIndexLookup(iterations: iterations, kind: "LSM", granular: granular)
            case .idxLSMRange:
                result = try runInMemoryIndexRange(iterations: iterations, kind: "LSM", granular: granular)
            case .idxTombstone:
                result = try runIndexTombstone(iterations: iterations, kind: "Hash", granular: granular)
            case .txCommit:
                result = try runTxCommit(iterations: iterations, granular: granular)
            case .txCommitGrouped:
                result = try runTxCommitGrouped(iterations: iterations, granular: granular)
            case .txRollback:
                result = try runTxRollback(iterations: iterations, granular: granular)
            case .txContention:
                let effWorkers = userSetWorkers ? workers : 1
                result = try runTxContention(iterations: iterations, workers: effWorkers, granular: granular)
            case .mvccSnapshotRead:
                result = try runMVCCSnapshotRead(iterations: iterations)
            case .plannerIndexScan:
                result = try runPlannerIndexScan(iterations: iterations, granular: granular)
            case .plannerSortLimit:
                result = try runPlannerSortLimit(iterations: iterations, granular: granular)
            case .checkpoint:
                result = try runCheckpoint(iterations: iterations)
            case .vacuumCompact:
                result = try runVacuumCompact(iterations: iterations)
            case .walRecovery:
                result = try runWALRecovery(iterations: iterations)
            case .walStress:
                result = try runWALStress(iterations: iterations, granular: granular)
            case .systemLoad:
                result = try runSystemLoad(iterations: iterations, granular: granular)
            case .memoryPressure:
                result = try runMemoryPressure(iterations: iterations)
            case .concurrentLoad:
                let effWorkers = userSetWorkers ? workers : max(2, ProcessInfo.processInfo.activeProcessorCount / 2)
                result = try runConcurrentLoad(iterations: iterations, workers: effWorkers, granular: granular)
            case .insertVariability:
                result = try runInsertVariability(iterations: iterations, granular: granular)
            case .queryLatency:
                result = try runQueryLatency(iterations: iterations, granular: granular)
            }
            let enriched = attachConfigMetadata(result: result)
            enriched.printSummary()
            enriched.printReport(format: formatJSON ? .json : .text)
        }
    }

    // NOTE: Helper implementations for heap/btree/planner are provided in extension files:
    // - Benchmarks+Heap.swift
    // - Benchmarks+BTree.swift
    // Keep this file focused on the CLI harness only.

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

    // MARK: - Metadata enrichment
    private static func attachConfigMetadata(result: BenchmarkResult) -> BenchmarkResult {
        var meta = result.metadata
        // In assenza di un DB dedicato per scenario, logghiamo i default globali
        let cfg = DBConfig()
        meta["durability_mode"] = cfg.walEnabled ? (cfg.walFullFSyncEnabled ? "full_fsync" : "fsync") : "none"
        meta["wal_group_commit_ms"] = String(format: "%.2f", cfg.walGroupCommitMs)
        meta["page_size"] = String(cfg.pageSizeBytes)
        meta["fill_factor"] = meta["fill_factor"] ?? "n/a"
        meta["split_ratio"] = meta["split_ratio"] ?? "0.60/0.40"
        meta["metrics_sampling"] = meta["metrics_sampling"] ?? String(cfg.optimizerStatsSampleRows)
        if meta["warmup_done"] == nil { meta["warmup_done"] = "false" }
        return BenchmarkResult(name: result.name, iterations: result.iterations, elapsed: result.elapsed, latenciesMs: result.latenciesMs, metadata: meta, systemMetrics: result.systemMetrics)
    }
}
