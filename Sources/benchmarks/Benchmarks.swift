//
//  Benchmarks.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// Theme: Benchmark harness measuring core engine throughput and latency.

import Foundation
import ColibriCore

// Precomputed statistics for performance optimization
struct LatencyStats {
    let sorted: [Double]
    let mean: Double
    let stddev: Double
    let minMs: Double
    let maxMs: Double
    let p50: Double
    let p90: Double
    let p95: Double
    let p99: Double
    let p999: Double
    
    init(latenciesMs: [Double]) {
        if latenciesMs.isEmpty {
            self.sorted = []
            self.mean = 0
            self.stddev = 0
            self.minMs = 0
            self.maxMs = 0
            self.p50 = 0
            self.p90 = 0
            self.p95 = 0
            self.p99 = 0
            self.p999 = 0
        } else {
            let sorted = latenciesMs.sorted()
            let mean = latenciesMs.reduce(0, +) / Double(latenciesMs.count)
            
            let stddev: Double
            if latenciesMs.count > 1 {
                let variance = latenciesMs.reduce(0.0) { $0 + ($1 - mean) * ($1 - mean) } / Double(latenciesMs.count - 1)
                stddev = variance.squareRoot()
            } else {
                stddev = 0
            }
            
            let minMs = sorted.first ?? 0
            let maxMs = sorted.last ?? 0
            
            // Precompute percentiles using linear interpolation
            func percentile(_ p: Double, in sorted: [Double]) -> Double {
                let n = sorted.count
                let index = (p / 100.0) * Double(n - 1)
                let lowerIndex = Int(index)
                let upperIndex = min(lowerIndex + 1, n - 1)
                
                if lowerIndex == upperIndex {
                    return sorted[lowerIndex]
                }
                
                let weight = index - Double(lowerIndex)
                return sorted[lowerIndex] * (1.0 - weight) + sorted[upperIndex] * weight
            }
            
            let p50 = percentile(50, in: sorted)
            let p90 = percentile(90, in: sorted)
            let p95 = percentile(95, in: sorted)
            let p99 = percentile(99, in: sorted)
            let p999 = percentile(99.9, in: sorted)
            
            self.sorted = sorted
            self.mean = mean
            self.stddev = stddev
            self.minMs = minMs
            self.maxMs = maxMs
            self.p50 = p50
            self.p90 = p90
            self.p95 = p95
            self.p99 = p99
            self.p999 = p999
        }
    }
    
    // Generate a compact log2 histogram for latency distribution analysis
    public func generateHistogram(buckets: Int = 8) -> String {
        guard !sorted.isEmpty else { return "No data" }
        
        let minVal = minMs
        let maxVal = maxMs
        
        // Use log2 scale for better distribution visualization
        let logMin = minVal > 0 ? log2(minVal) : -10.0
        let logMax = maxVal > 0 ? log2(maxVal) : 10.0
        let bucketSize = (logMax - logMin) / Double(buckets)
        
        // Handle case where all values are very small or identical
        if logMax - logMin < 1.0 || minVal == maxVal {
            // Use linear scale for very small ranges
            let linearMin = minVal
            let linearMax = maxVal == minVal ? minVal + max(minVal * 0.1, 0.001) : maxVal  // Ensure meaningful range
            let linearBucketSize = (linearMax - linearMin) / Double(buckets)
            
            var bucketCounts = Array(repeating: 0, count: buckets)
            var bucketLabels: [String] = []
            
            for i in 0..<buckets {
                let start = linearMin + Double(i) * linearBucketSize
                let end = linearMin + Double(i + 1) * linearBucketSize
                if i == buckets - 1 {
                    bucketLabels.append(String(format: "[%.4f,+∞)", start))
                } else {
                    bucketLabels.append(String(format: "[%.4f,%.4f)", start, end))
                }
            }
            
            for value in sorted {
                let bucketIndex = min(buckets - 1, max(0, Int((value - linearMin) / linearBucketSize)))
                bucketCounts[bucketIndex] += 1
            }
            
            var result = ""
            let maxCount = bucketCounts.max() ?? 1
            
            for i in 0..<buckets {
                let count = bucketCounts[i]
                let percentage = Double(count) / Double(sorted.count) * 100.0
                let barLength = max(1, (count * 20) / maxCount)
                let bar = String(repeating: "█", count: barLength)
                
                result += "\(bucketLabels[i]): \(bar) \(String(format: "%.0f", percentage))%\n"
            }
            
            return result.trimmingCharacters(in: .whitespacesAndNewlines)
        }
        
        var bucketCounts = Array(repeating: 0, count: buckets)
        var bucketLabels: [String] = []
        
        // Create bucket labels
        for i in 0..<buckets {
            let start = pow(2.0, logMin + Double(i) * bucketSize)
            let end = pow(2.0, logMin + Double(i + 1) * bucketSize)
            if i == buckets - 1 {
                bucketLabels.append(String(format: "[%.1f,+∞)", start))
            } else {
                bucketLabels.append(String(format: "[%.1f,%.1f)", start, end))
            }
        }
        
        // Count values in each bucket
        for value in sorted {
            let logVal = value > 0 ? log2(value) : -10.0
            let bucketIndex = min(buckets - 1, max(0, Int((logVal - logMin) / bucketSize)))
            bucketCounts[bucketIndex] += 1
        }
        
        // Generate histogram string
        var result = ""
        let maxCount = bucketCounts.max() ?? 1
        
        for i in 0..<buckets {
            let count = bucketCounts[i]
            let percentage = Double(count) / Double(sorted.count) * 100.0
            let barLength = max(1, (count * 20) / maxCount)
            let bar = String(repeating: "█", count: barLength)
            
            result += "\(bucketLabels[i]): \(bar) \(String(format: "%.0f", percentage))%\n"
        }
        
        return result.trimmingCharacters(in: .whitespacesAndNewlines)
    }
}

struct BenchmarkResult {
    let name: String
    let iterations: Int
    let elapsed: Duration
    let latenciesMs: [Double]
    let metadata: [String: String]
    let systemMetrics: SystemMetrics?
    
    // Precomputed statistics for O(1) access
    private let stats: LatencyStats

    private var totalMs: Double {
        BenchmarkCLI.durationToMs(elapsed)
    }

    var opsPerSecond: Double {
        guard elapsed > .zero && iterations > 0 else { return 0 }
        let seconds = BenchmarkCLI.durationToSeconds(elapsed)
        return Double(iterations) / seconds
    }
    
    // O(1) access to precomputed statistics - exposed publicly for reuse
    public var mean: Double { stats.mean }
    public var stddev: Double { stats.stddev }
    public var minMs: Double { stats.minMs }
    public var maxMs: Double { stats.maxMs }
    public var p50: Double { stats.p50 }
    public var p90: Double { stats.p90 }
    public var p95: Double { stats.p95 }
    public var p99: Double { stats.p99 }
    public var p999: Double { stats.p999 }
    
    // Access to the underlying stats for advanced analysis
    public var latencyStats: LatencyStats { stats }

    // Aggiunge metriche di sistema per analisi completa
    var cpuUsage: Double { systemMetrics?.cpu.usage ?? 0 }
    var memoryUsage: Double { systemMetrics?.memory.usage ?? 0 }
    var ioReadCount: UInt64 { systemMetrics?.io.readCount ?? 0 }
    var ioWriteCount: UInt64 { systemMetrics?.io.writeCount ?? 0 }

    func printSummary() {
        let formattedOps = String(format: "%.2f", opsPerSecond)
        print("[\(name)] iterations=\(iterations) elapsed_ms=\(String(format: "%.3f", totalMs)) throughput_ops_s=\(formattedOps)")
    }

    enum OutputFormat { case text, json }

    func printReport(format: OutputFormat) {
        switch format {
        case .text:
            let ts = BenchmarkCLI.formatTimestamp(Date())
            print("--- Report: \(name) ---")
            print("quando=\(ts)")
            print("operazioni=\(latenciesMs.count) totale_ms=\(String(format: "%.3f", totalMs)) ops_al_sec=\(String(format: "%.2f", opsPerSecond))")
            print("latenza_ms: media=\(String(format: "%.4f", mean)) p50=\(String(format: "%.4f", p50)) p90=\(String(format: "%.4f", p90)) p95=\(String(format: "%.4f", p95)) p99=\(String(format: "%.4f", p99)) p99.9=\(String(format: "%.4f", p999)) min=\(String(format: "%.4f", minMs)) max=\(String(format: "%.4f", maxMs)) stddev=\(String(format: "%.4f", stddev))")
            print("distribuzione:")
            print(stats.generateHistogram())
            if systemMetrics != nil {
                print("sistema: cpu=\(String(format: "%.1f", cpuUsage))% memoria=\(String(format: "%.1f", memoryUsage))% io_read=\(ioReadCount) io_write=\(ioWriteCount)")
            }
            if !metadata.isEmpty {
                print("metadati:")
                for (k, v) in metadata.sorted(by: { $0.key < $1.key }) {
                    print("  \(k)=\(v)")
                }
            }
        case .json:
            struct Payload: Codable {
                struct Lat: Codable { let count:Int; let total_ms:Double; let mean_ms:Double; let p50_ms:Double; let p90_ms:Double; let p95_ms:Double; let p99_ms:Double; let p999_ms:Double; let min_ms:Double; let max_ms:Double; let stddev_ms:Double }
                struct Sys: Codable { let cpu_percent:Double; let memory_percent:Double; let io_read_count:UInt64; let io_write_count:UInt64 }
                let scenario: String
                let iterations: Int
                let throughput_ops_s: Double
                let when: String
                let latency_ms: Lat
                let system_metrics: Sys?
                let metadata: [String:String]
            }
            let ts = BenchmarkCLI.formatTimestamp(Date())
            let lat = Payload.Lat(count: latenciesMs.count,
                                   total_ms: totalMs,
                                   mean_ms: mean,
                                   p50_ms: p50,
                                   p90_ms: p90,
                                   p95_ms: p95,
                                   p99_ms: p99,
                                   p999_ms: p999,
                                   min_ms: minMs,
                                   max_ms: maxMs,
                                   stddev_ms: stddev)
            let sys = systemMetrics.map { Payload.Sys(cpu_percent: $0.cpu.usage, memory_percent: $0.memory.usage, io_read_count: $0.io.readCount, io_write_count: $0.io.writeCount) }
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
        let ms = BenchmarkCLI.durationToMs(elapsed)
        let count = max(1, iterations)
        self.latenciesMs = Array(repeating: ms / Double(count), count: count)
        self.metadata = [:]
        self.systemMetrics = systemMetrics
        self.stats = LatencyStats(latenciesMs: self.latenciesMs)
    }

    init(name: String, iterations: Int, elapsed: Duration, metadata: [String:String], systemMetrics: SystemMetrics? = nil) {
        self.name = name
        self.iterations = iterations
        self.elapsed = elapsed
        let ms = BenchmarkCLI.durationToMs(elapsed)
        let count = max(1, iterations)
        self.latenciesMs = Array(repeating: ms / Double(count), count: count)
        self.metadata = metadata
        self.systemMetrics = systemMetrics
        self.stats = LatencyStats(latenciesMs: self.latenciesMs)
    }

    init(name: String, iterations: Int, elapsed: Duration, latenciesMs: [Double], systemMetrics: SystemMetrics? = nil) {
        self.name = name
        self.iterations = iterations
        self.elapsed = elapsed
        self.latenciesMs = latenciesMs
        self.metadata = [:]
        self.systemMetrics = systemMetrics
        self.stats = LatencyStats(latenciesMs: latenciesMs)
    }

    init(name: String, iterations: Int, elapsed: Duration, latenciesMs: [Double], metadata: [String:String], systemMetrics: SystemMetrics? = nil) {
        self.name = name
        self.iterations = iterations
        self.elapsed = elapsed
        self.latenciesMs = latenciesMs
        self.metadata = metadata
        self.systemMetrics = systemMetrics
        self.stats = LatencyStats(latenciesMs: latenciesMs)
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
    // ISO8601 formatter helper
    static func formatTimestamp(_ date: Date) -> String {
        let formatter = ISO8601DateFormatter()
        return formatter.string(from: date)
    }
    
    // Centralized time conversion helpers
    static func durationToMs(_ duration: Duration) -> Double {
        return Double(duration.components.seconds) * 1_000 + Double(duration.components.attoseconds) / 1_000_000_000_000_000.0
    }
    
    static func durationToSeconds(_ duration: Duration) -> Double {
        return Double(duration.components.seconds) + Double(duration.components.attoseconds) / 1_000_000_000_000_000_000.0
    }
    
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
        var enableSysMetrics = false
        var warmup = true
        var seed: UInt64? = nil
        var outputFile: String? = nil
        var csvFormat = false

        for a in args {
            if let n = Int(a) { iterations = n; continue }
            if let s = Scenario.from(a) { selected = s; continue }
            if a.hasPrefix("--workers=") {
                let parts = a.split(separator: "=")
                if let last = parts.last, let n = Int(last) { workers = max(1, n); userSetWorkers = true }
            }
            if a == "--granular" { granular = true }
            if a == "--json" || a == "--format=json" { formatJSON = true }
            if a == "--sysmetrics" { enableSysMetrics = true }
            if a == "--no-warmup" { warmup = false }
            if a == "--csv" { csvFormat = true }
            if a.hasPrefix("--seed=") {
                let parts = a.split(separator: "=")
                if let last = parts.last, let s = UInt64(last) { seed = s }
            }
            if a.hasPrefix("--out=") {
                let parts = a.split(separator: "=")
                if let last = parts.last { outputFile = String(last) }
            }
        }

        let scenarios = selected.map { [$0] } ?? Scenario.allCases
        for scenario in scenarios {
            do {
                let baseResult: BenchmarkResult
                switch scenario {
            case .heapInsert:
                baseResult = try runHeapInsert(iterations: iterations)
            case .heapScan:
                baseResult = try runHeapScan(iterations: iterations)
            case .btreeLookup:
                baseResult = try runBTreeLookup(iterations: iterations)
            case .btreeLookupOptimized:
                baseResult = try runBTreeLookupOptimized(iterations: iterations)
            case .plannerJoin:
                baseResult = try runPlannerJoin(iterations: iterations)
            case .heapDelete:
                baseResult = try runHeapDelete(iterations: iterations, granular: granular)
            case .heapReadRID:
                baseResult = try runHeapReadRID(iterations: iterations, granular: granular)
            case .fileHeapInsertWalOff:
                baseResult = try runFileHeapInsert(iterations: iterations, wal: false, fullSync: false, granular: granular)
            case .fileHeapInsertWalFSync:
                baseResult = try runFileHeapInsert(iterations: iterations, wal: true, fullSync: true, granular: granular)
            case .walAppendNone:
                baseResult = try runWALAppend(iterations: iterations, algorithm: .none, granular: granular)
            case .walAppendLZFSE:
                baseResult = try runWALAppend(iterations: iterations, algorithm: .lzfse, granular: granular)
            case .walAppendZlib:
                baseResult = try runWALAppend(iterations: iterations, algorithm: .zlib, granular: granular)
            case .btreeInsert:
                baseResult = try runBTreeInsert(iterations: iterations, granular: granular)
            case .btreeRange:
                baseResult = try runBTreeRange(iterations: iterations, granular: granular)
            case .btreeBulkBuild:
                baseResult = try runBTreeBulkBuild(iterations: iterations)
            case .idxHashLookup:
                baseResult = try runInMemoryIndexLookup(iterations: iterations, kind: "Hash", granular: granular)
            case .idxARTLookup:
                baseResult = try runInMemoryIndexLookup(iterations: iterations, kind: "ART", granular: granular)
            case .idxARTRange:
                // Temporarily disabled due to LRUBufferPool crash
                throw DBError.notImplemented("idx-art-range temporarily disabled")
            case .idxSkiplistLookup:
                baseResult = try runInMemoryIndexLookup(iterations: iterations, kind: "SkipList", granular: granular)
            case .idxSkiplistRange:
                baseResult = try runInMemoryIndexRange(iterations: iterations, kind: "SkipList", granular: granular)
            case .idxFractalLookup:
                baseResult = try runInMemoryIndexLookup(iterations: iterations, kind: "Fractal", granular: granular)
            case .idxFractalRange:
                baseResult = try runInMemoryIndexRange(iterations: iterations, kind: "Fractal", granular: granular)
            case .idxBTreeLookup:
                baseResult = try runInMemoryIndexLookup(iterations: iterations, kind: "BTree", granular: granular)
            case .idxBTreeRange:
                baseResult = try runInMemoryIndexRange(iterations: iterations, kind: "BTree", granular: granular)
            case .idxLSMLookup:
                baseResult = try runInMemoryIndexLookup(iterations: iterations, kind: "LSM", granular: granular)
            case .idxLSMRange:
                baseResult = try runInMemoryIndexRange(iterations: iterations, kind: "LSM", granular: granular)
            case .idxTombstone:
                baseResult = try runIndexTombstone(iterations: iterations, kind: "Hash", granular: granular)
            case .txCommit:
                baseResult = try runTxCommit(iterations: iterations, granular: granular)
            case .txCommitGrouped:
                baseResult = try runTxCommitGrouped(iterations: iterations, granular: granular)
            case .txRollback:
                baseResult = try runTxRollback(iterations: iterations, granular: granular)
            case .txContention:
                let effWorkers = userSetWorkers ? workers : 1
                baseResult = try runTxContention(iterations: iterations, workers: effWorkers, granular: granular)
            case .mvccSnapshotRead:
                baseResult = try runMVCCSnapshotRead(iterations: iterations)
            case .plannerIndexScan:
                baseResult = try runPlannerIndexScan(iterations: iterations, granular: granular)
            case .plannerSortLimit:
                baseResult = try runPlannerSortLimit(iterations: iterations, granular: granular)
            case .checkpoint:
                baseResult = try runCheckpoint(iterations: iterations)
            case .vacuumCompact:
                baseResult = try runVacuumCompact(iterations: iterations)
            case .walRecovery:
                baseResult = try runWALRecovery(iterations: iterations)
            case .walStress:
                baseResult = try runWALStress(iterations: iterations, granular: granular)
            case .systemLoad:
                baseResult = try runSystemLoad(iterations: iterations, granular: granular)
            case .memoryPressure:
                baseResult = try runMemoryPressure(iterations: iterations)
            case .concurrentLoad:
                let effWorkers = userSetWorkers ? workers : max(2, ProcessInfo.processInfo.activeProcessorCount / 2)
                baseResult = try runConcurrentLoad(iterations: iterations, workers: effWorkers, granular: granular)
            case .insertVariability:
                baseResult = try runInsertVariability(iterations: iterations, granular: granular)
            case .queryLatency:
                baseResult = try runQueryLatency(iterations: iterations, granular: granular)
                }
                
                // Use system metrics from the scenario result (if any)
                let result = baseResult
                
                let enriched = attachConfigMetadata(result: result)
                enriched.printSummary()
                enriched.printReport(format: formatJSON ? .json : .text)
            } catch {
                print("⚠️  Scenario '\(scenario.rawValue)' failed: \(error)")
                print("Continuing with remaining scenarios...")
            }
        }
    }

    // NOTE: Helper implementations for heap/btree/planner are provided in extension files:
    // - Benchmarks+Heap.swift
    // - Benchmarks+BTree.swift
    // Keep this file focused on the CLI harness only.

    private static func printUsage() {
        print("Uso: benchmarks [iterations] [scenario] [opzioni]")
        print("  iterations: numero di iterazioni (default 10000; alcuni scenari sono limitati)")
        print("  scenario:   uno tra \(Scenario.allCases.map { $0.rawValue }.joined(separator: ", ")) oppure omesso per eseguire tutti")
        print("")
        print("Opzioni:")
        print("  --workers=N     per scenari concorrenti (es. tx-contention), default = logical cores")
        print("  --granular      misura la latenza per singola operazione dove applicabile")
        print("  --json          stampa report in formato JSON (oltre al summary)")
        print("  --csv           stampa report in formato CSV")
        print("  --sysmetrics    abilita raccolta metriche di sistema (CPU, memoria, I/O)")
        print("  --no-warmup     disabilita warm-up pre-benchmark")
        print("  --seed=N        imposta seed per randomizzazione (per riproducibilità)")
        print("  --out=file      scrivi output su file invece che su stdout")
        print("")
        print("Esempi:")
        print("  benchmarks 5000 btree-bulk-build")
        print("  benchmarks 20000 tx-contention --workers=8 --granular --json --sysmetrics")
        print("  benchmarks 1000 heap-insert --csv --out=results.csv")
        print("  benchmarks 5000 btree-lookup --seed=42 --no-warmup")
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
