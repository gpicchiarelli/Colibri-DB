//
//  BenchmarksExtra.swift
//  ColibrìDB
//
//  Additional micro/macro benchmarks to broaden coverage across
//  heap storage, indexes, WAL, transactions, planner and maintenance.
//

@preconcurrency import Foundation
import ColibriCore

private struct BenchmarkResult {
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
            print("when=\(ts)")
            print("ops=\(latenciesMs.count) total_ms=\(String(format: "%.3f", totalMs)) ops_per_s=\(String(format: "%.2f", opsPerSecond))")
            print("latency_ms: mean=\(String(format: "%.4f", mean)) p50=\(String(format: "%.4f", percentile(50))) p90=\(String(format: "%.4f", percentile(90))) p95=\(String(format: "%.4f", percentile(95))) p99=\(String(format: "%.4f", percentile(99))) min=\(String(format: "%.4f", minMs)) max=\(String(format: "%.4f", maxMs)) stddev=\(String(format: "%.4f", stddev))")
            if !metadata.isEmpty {
                print("metadata:")
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

    // Convenience initializers to keep existing call sites simple
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
    // Heap
    case heapDelete = "heap-delete"
    case heapReadRID = "heap-read-rid"
    // File heap + WAL
    case fileHeapInsertWalOff = "fileheap-insert-wal-off"
    case fileHeapInsertWalFSync = "fileheap-insert-wal-fsync"
    // WAL micro
    case walAppendNone = "wal-append-none"
    case walAppendLZFSE = "wal-append-lzfse"
    case walAppendZlib = "wal-append-zlib"
    // Persistent B+Tree
    case btreeInsert = "btree-insert"
    case btreeRange = "btree-range"
    case btreeBulkBuild = "btree-bulk-build"
    // In-memory index kinds
    case idxHashLookup = "idx-hash-lookup"
    case idxARTLookup = "idx-art-lookup"
    case idxSkiplistRange = "idx-skiplist-range"
    case idxLSMLookup = "idx-lsm-lookup"
    // Transactions
    case txCommit = "tx-commit"
    case txRollback = "tx-rollback"
    case txContention = "tx-contention"
    case mvccSnapshotRead = "mvcc-snapshot-read"
    // Planner
    case plannerIndexScan = "planner-index-scan"
    case plannerSortLimit = "planner-sort-limit"
    // Maintenance
    case checkpoint = "checkpoint"
    case vacuumCompact = "vacuum-compact"

    static func from(_ string: String) -> Scenario? { Scenario(rawValue: string.lowercased()) }
}

@main
struct BenchmarksExtraCLI {
    static func main() throws {
        // CLI: benchmarks-extra [iterations] [scenario] [--workers=N]
        let args = Array(CommandLine.arguments.dropFirst())
        if args.contains("--help") || args.contains("-h") {
            printUsage()
            return
        }
        var iterations = 10_000
        var selectedScenario: Scenario? = nil
        var workers = ProcessInfo.processInfo.activeProcessorCount
        var userSetWorkers = false
        var outFormat: BenchmarkResult.OutputFormat = .text
        var granular = false
        for a in args {
            if let n = Int(a) { iterations = n; continue }
            if let s = Scenario.from(a) { selectedScenario = s; continue }
            if a.hasPrefix("--workers=") {
                let parts = a.split(separator: "=")
                if let last = parts.last, let n = Int(last) { workers = max(1, n); userSetWorkers = true }
            }
            if a == "--json" || a == "--format=json" { outFormat = .json }
            if a == "--granular" { granular = true }
        }

        let scenarios: [Scenario] = selectedScenario.map { [$0] } ?? Scenario.allCases
        for scenario in scenarios {
            let result: BenchmarkResult
            switch scenario {
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
            case .idxSkiplistRange:
                result = try runInMemoryIndexRange(iterations: iterations, kind: "SkipList", granular: granular)
            case .idxLSMLookup:
                result = try runInMemoryIndexLookup(iterations: iterations, kind: "LSM", granular: granular)
            case .txCommit:
                result = try runTxCommit(iterations: iterations, granular: granular)
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
            }
            result.printSummary()
            result.printReport(format: outFormat)
        }
    }

    // MARK: - Helpers
    private static func msDelta(_ start: ContinuousClock.Instant, _ end: ContinuousClock.Instant) -> Double {
        let d = end - start
        return Double(d.components.seconds) * 1_000 + Double(d.components.attoseconds) / 1_000_000_000_000_000.0
    }

    // Utility boxes to appease Swift concurrency checks for benchmarking code
    private final class NonSendableBox<T>: @unchecked Sendable { var value: T; init(_ v: T) { self.value = v } }
    private final class LatCollector: @unchecked Sendable {
        private var items: [Double] = []
        private let lock = NSLock()
        func append(_ v: Double) { lock.lock(); items.append(v); lock.unlock() }
        func snapshot() -> [Double] { lock.lock(); let out = items; lock.unlock(); return out }
    }
    private static func makeTempDir() throws -> URL {
        let fm = FileManager.default
        let dir = fm.temporaryDirectory.appendingPathComponent("colibridb-bench-\(UUID().uuidString)", isDirectory: true)
        try fm.createDirectory(at: dir, withIntermediateDirectories: true)
        return dir
    }

    private static func cappedDiskIterations(_ n: Int) -> Int {
        // Cap for disk-heavy scenarios to reduce test time
        return min(n, 5_000)
    }

    // MARK: - Heap
    private static func runHeapDelete(iterations: Int, granular: Bool) throws -> BenchmarkResult {
        let tmp = try makeTempDir(); defer { try? FileManager.default.removeItem(at: tmp) }
        var cfg = DBConfig(dataDir: tmp.path, storageEngine: "InMemory")
        cfg.autoCompactionEnabled = false
        let db = Database(config: cfg)
        try db.createTable("t")
        for i in 0..<iterations { _ = try db.insert(into: "t", row: ["id": .int(Int64(i)), "p": .string("v\(i)")]) }
        let clock = ContinuousClock(); let start = clock.now
        let deleted = try db.deleteEquals(table: "t", column: "id", value: .int(0))
        _ = deleted // warmup single delete
        var total = 0
        for i in 1..<iterations { total += try db.deleteEquals(table: "t", column: "id", value: .int(Int64(i))) }
        let elapsed = clock.now - start
        return BenchmarkResult(name: Scenario.heapDelete.rawValue, iterations: total + deleted, elapsed: elapsed)
    }

    private static func runHeapReadRID(iterations: Int, granular: Bool) throws -> BenchmarkResult {
        let tmp = try makeTempDir(); defer { try? FileManager.default.removeItem(at: tmp) }
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
        for rid in rids {
            let row = try db.readRow(table: "t", rid: rid)
            if case .int(let v) = row["id"] { sum &+= Int(v) }
        }
        let elapsed = clock.now - start
        precondition(sum >= 0)
        return BenchmarkResult(name: Scenario.heapReadRID.rawValue, iterations: rids.count, elapsed: elapsed)
    }

    // MARK: - File heap and WAL
    private static func runFileHeapInsert(iterations: Int, wal: Bool, fullSync: Bool, granular: Bool) throws -> BenchmarkResult {
        let fm = FileManager.default
        let tmp = try makeTempDir()
        var cfg = DBConfig(dataDir: tmp.path)
        cfg.storageEngine = "FileHeap"
        cfg.walEnabled = wal
        cfg.walFullFSyncEnabled = fullSync
        cfg.autoCompactionEnabled = false
        let result: BenchmarkResult
        do {
            let db = Database(config: cfg)
            try db.createTable("t")
            let n0 = cappedDiskIterations(iterations)
            let n = granular ? n0 : min(n0, 200)
            let clock = ContinuousClock(); let start = clock.now
            for i in 0..<n { _ = try db.insert(into: "t", row: ["id": .int(Int64(i)), "p": .string("v\(i)")]) }
            let elapsed = clock.now - start
            result = BenchmarkResult(name: wal ? (fullSync ? Scenario.fileHeapInsertWalFSync.rawValue : Scenario.fileHeapInsertWalOff.rawValue) : Scenario.fileHeapInsertWalOff.rawValue, iterations: n, elapsed: elapsed)
        }
        try? fm.removeItem(at: tmp)
        return result
    }

    private static func runWALAppend(iterations: Int, algorithm: CompressionAlgorithm, granular: Bool) throws -> BenchmarkResult {
        let fm = FileManager.default
        let tmp = try makeTempDir()
        let walPath = tmp.appendingPathComponent("wal.log").path
        let wal = try FileWAL(path: walPath)
        wal.setFullFSync(enabled: false)
        wal.setCompression(algorithm)
        var payload = Data(count: 64)
        payload.withUnsafeMutableBytes { buf in
            guard let p = buf.baseAddress?.assumingMemoryBound(to: UInt8.self) else { return }
            for i in 0..<buf.count { p[i] = UInt8(truncatingIfNeeded: i &* 31) }
        }
        let clock = ContinuousClock(); let start = clock.now
        if granular {
            var lat: [Double] = []; lat.reserveCapacity(iterations)
            for _ in 0..<iterations {
                let t0 = clock.now
                _ = try wal.append(record: payload)
                let t1 = clock.now
                lat.append(msDelta(t0, t1))
            }
            let elapsed = clock.now - start
            return BenchmarkResult(name: "wal-append-\(algorithm.rawValue)", iterations: iterations, elapsed: elapsed, latenciesMs: lat, metadata: ["compression":"\(algorithm.rawValue)"])
        } else {
            for _ in 0..<iterations { _ = try wal.append(record: payload) }
            let elapsed = clock.now - start
            return BenchmarkResult(name: "wal-append-\(algorithm.rawValue)", iterations: iterations, elapsed: elapsed)
        }
    }

    // MARK: - Persistent B+Tree
    private static func runBTreeInsert(iterations: Int, granular: Bool) throws -> BenchmarkResult {
        let fm = FileManager.default
        let tmp = try makeTempDir(); defer { try? fm.removeItem(at: tmp) }
        var cfg = DBConfig(dataDir: tmp.path)
        cfg.storageEngine = "FileHeap"
        cfg.autoCompactionEnabled = false
        let result: BenchmarkResult
        do {
            let db = Database(config: cfg)
            try db.createTable("t")
            try db.createIndex(name: "idx", on: "t", columns: ["id"], using: "BTree")
            let n0 = cappedDiskIterations(iterations)
            let n = granular ? n0 : min(n0, 200)
            let clock = ContinuousClock(); let start = clock.now
            if granular {
            var lat: [Double] = []; lat.reserveCapacity(n)
            for i in 0..<n {
                let t0 = clock.now
                _ = try db.insert(into: "t", row: ["id": .int(Int64(i)), "p": .string("v\(i)")])
                let t1 = clock.now
                lat.append(msDelta(t0, t1))
            }
            let elapsed = clock.now - start
                result = BenchmarkResult(name: Scenario.btreeInsert.rawValue, iterations: n, elapsed: elapsed, latenciesMs: lat, metadata: ["index":"BTree","columns":"id"])
            } else {
                for i in 0..<n { _ = try db.insert(into: "t", row: ["id": .int(Int64(i)), "p": .string("v\(i)")]) }
                let elapsed = clock.now - start
                result = BenchmarkResult(name: Scenario.btreeInsert.rawValue, iterations: n, elapsed: elapsed)
            }
        }
        try? fm.removeItem(at: tmp)
        return result
    }

    private static func runBTreeRange(iterations: Int, granular: Bool) throws -> BenchmarkResult {
        let fm = FileManager.default
        let tmp = try makeTempDir()
        var cfg = DBConfig(dataDir: tmp.path)
        cfg.storageEngine = "FileHeap"
        cfg.autoCompactionEnabled = false
        let result: BenchmarkResult
        do {
            let db = Database(config: cfg)
            try db.createTable("t")
            let n0 = cappedDiskIterations(iterations)
            let n = granular ? n0 : min(n0, 200)
            for i in 0..<n { _ = try db.insert(into: "t", row: ["id": .int(Int64(i)), "p": .string("v\(i)")]) }
            try db.createIndex(name: "idx", on: "t", columns: ["id"], using: "BTree")
            try db.rebuildIndexBulk(table: "t", index: "idx")
            let clock = ContinuousClock(); let start = clock.now
            if granular {
            let q = min(n, 500)
            var lat: [Double] = []; lat.reserveCapacity(q)
            var total = 0
            for _ in 0..<q {
                let base = Int.random(in: 0..<(max(1, n - 10)))
                let lo = Value.int(Int64(base))
                let hi = Value.int(Int64(base + Int.random(in: 0..<10)))
                let t0 = clock.now
                let hits = try db.indexRangeTyped(table: "t", index: "idx", lo: lo, hi: hi)
                let t1 = clock.now
                total &+= hits.count
                lat.append(msDelta(t0, t1))
            }
            let elapsed = clock.now - start
            precondition(total > 0)
                result = BenchmarkResult(name: Scenario.btreeRange.rawValue, iterations: q, elapsed: elapsed, latenciesMs: lat, metadata: ["index":"BTree","columns":"id","queries":"\(q)"])
            } else {
                let lo = Value.int(0)
                let hi = Value.int(Int64(n - 1))
                let hits = try db.indexRangeTyped(table: "t", index: "idx", lo: lo, hi: hi)
                precondition(hits.count == n)
                let elapsed = clock.now - start
                result = BenchmarkResult(name: Scenario.btreeRange.rawValue, iterations: hits.count, elapsed: elapsed)
            }
        }
        try? fm.removeItem(at: tmp)
        return result
    }

    private static func runBTreeBulkBuild(iterations: Int) throws -> BenchmarkResult {
        let fm = FileManager.default
        let tmp = try makeTempDir()
        var cfg = DBConfig(dataDir: tmp.path)
        cfg.storageEngine = "FileHeap"
        cfg.autoCompactionEnabled = false
        let result: BenchmarkResult
        do {
            let db = Database(config: cfg)
            try db.createTable("t")
            let n = cappedDiskIterations(iterations)
            for i in 0..<n { _ = try db.insert(into: "t", row: ["id": .int(Int64(i)), "p": .string("v\(i)")]) }
            try db.createIndex(name: "idx", on: "t", columns: ["id"], using: "BTree")
            let clock = ContinuousClock(); let start = clock.now
            try db.rebuildIndexBulk(table: "t", index: "idx")
            let elapsed = clock.now - start
            result = BenchmarkResult(name: Scenario.btreeBulkBuild.rawValue, iterations: n, elapsed: elapsed)
        }
        try? fm.removeItem(at: tmp)
        return result
    }

    // MARK: - In-memory AnyStringIndex kinds
    private static func runInMemoryIndexLookup(iterations: Int, kind: String, granular: Bool) throws -> BenchmarkResult {
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
            return BenchmarkResult(name: "idx-\(kind.lowercased())-lookup", iterations: iterations, elapsed: elapsed, latenciesMs: lat, metadata: ["kind":kind])
        } else {
            for i in 0..<iterations {
                let hits = try db.indexSearchEqualsTyped(table: "t", index: idxName, value: .string("k\(i)"))
                if !hits.isEmpty { found &+= 1 }
            }
            let elapsed = clock.now - start
            precondition(found == iterations)
            return BenchmarkResult(name: "idx-\(kind.lowercased())-lookup", iterations: iterations, elapsed: elapsed)
        }
    }

    private static func runInMemoryIndexRange(iterations: Int, kind: String, granular: Bool) throws -> BenchmarkResult {
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
            return BenchmarkResult(name: "idx-\(kind.lowercased())-range", iterations: q, elapsed: elapsed, latenciesMs: lat, metadata: ["kind":kind,"queries":"\(q)"])
        } else {
            let hits = try db.indexRangeTyped(table: "t", index: idxName, lo: lo, hi: hi)
            let elapsed = clock.now - start
            precondition(!hits.isEmpty)
            return BenchmarkResult(name: "idx-\(kind.lowercased())-range", iterations: hits.count, elapsed: elapsed)
        }
    }

    // MARK: - Transactions
    private static func runTxCommit(iterations: Int, granular: Bool) throws -> BenchmarkResult {
        var cfg = DBConfig(storageEngine: "InMemory")
        cfg.autoCompactionEnabled = false
        cfg.walEnabled = false
        let db = Database(config: cfg)
        try db.createTable("t")
        let clock = ContinuousClock(); let start = clock.now
        if granular {
            var lat: [Double] = []; lat.reserveCapacity(iterations)
            for i in 0..<iterations {
                let t0 = clock.now
                let tid = try db.begin()
                _ = try db.insert(into: "t", row: ["id": .int(Int64(i))], tid: tid)
                try db.commit(tid)
                let t1 = clock.now
                lat.append(msDelta(t0, t1))
            }
            let elapsed = clock.now - start
            return BenchmarkResult(name: Scenario.txCommit.rawValue, iterations: iterations, elapsed: elapsed, latenciesMs: lat, metadata: [:])
        } else {
            for i in 0..<iterations {
                let tid = try db.begin()
                _ = try db.insert(into: "t", row: ["id": .int(Int64(i))], tid: tid)
                try db.commit(tid)
            }
            let elapsed = clock.now - start
            return BenchmarkResult(name: Scenario.txCommit.rawValue, iterations: iterations, elapsed: elapsed)
        }
    }

    private static func runTxRollback(iterations: Int, granular: Bool) throws -> BenchmarkResult {
        var cfg = DBConfig(storageEngine: "InMemory")
        cfg.autoCompactionEnabled = false
        cfg.walEnabled = false
        let db = Database(config: cfg)
        try db.createTable("t")
        let clock = ContinuousClock(); let start = clock.now
        if granular {
            var lat: [Double] = []; lat.reserveCapacity(iterations)
            for i in 0..<iterations {
                let t0 = clock.now
                let tid = try db.begin()
                _ = try db.insert(into: "t", row: ["id": .int(Int64(i))], tid: tid)
                try db.rollback(tid)
                let t1 = clock.now
                lat.append(msDelta(t0, t1))
            }
            let elapsed = clock.now - start
            return BenchmarkResult(name: Scenario.txRollback.rawValue, iterations: iterations, elapsed: elapsed, latenciesMs: lat, metadata: [:])
        } else {
            for i in 0..<iterations {
                let tid = try db.begin()
                _ = try db.insert(into: "t", row: ["id": .int(Int64(i))], tid: tid)
                try db.rollback(tid)
            }
            let elapsed = clock.now - start
            return BenchmarkResult(name: Scenario.txRollback.rawValue, iterations: iterations, elapsed: elapsed)
        }
    }

    private static func runTxContention(iterations: Int, workers: Int, granular: Bool) throws -> BenchmarkResult {
        var cfg = DBConfig(storageEngine: "InMemory")
        cfg.autoCompactionEnabled = false
        cfg.walEnabled = false
        let db = Database(config: cfg)
        try db.createTable("t")
        let perWorker = max(1, iterations / max(1, workers))
        let group = DispatchGroup()
        let q = DispatchQueue.global(qos: .userInitiated)
        let clock = ContinuousClock(); let start = clock.now
        let lat = LatCollector()
        let dbBox = NonSendableBox(db)
        for w in 0..<workers {
            group.enter()
            let work: @Sendable () -> Void = {
                defer { group.leave() }
                for i in 0..<perWorker {
                    do {
                        let t0 = granular ? clock.now : start
                        let tid = try dbBox.value.begin()
                        _ = try dbBox.value.insert(into: "t", row: ["id": .int(Int64(w * perWorker + i))], tid: tid)
                        try dbBox.value.commit(tid)
                        if granular {
                            let t1 = clock.now
                            let ms = msDelta(t0, t1)
                            lat.append(ms)
                        }
                    } catch {
                        // ignore errors for the sake of contention stress
                    }
                }
            }
            q.async(execute: work)
        }
        group.wait()
        let elapsed = clock.now - start
        if granular {
            return BenchmarkResult(name: "tx-contention-w\(workers)", iterations: perWorker * workers, elapsed: elapsed, latenciesMs: lat.snapshot(), metadata: ["workers":"\(workers)"])
        } else {
            return BenchmarkResult(name: "tx-contention-w\(workers)", iterations: perWorker * workers, elapsed: elapsed)
        }
    }

    private static func runMVCCSnapshotRead(iterations: Int) throws -> BenchmarkResult {
        var cfg = DBConfig(storageEngine: "InMemory")
        cfg.autoCompactionEnabled = false
        cfg.walEnabled = false
        let db = Database(config: cfg)
        try db.createTable("t")
        for i in 0..<iterations { _ = try db.insert(into: "t", row: ["id": .int(Int64(i))]) }
        let writerQ = DispatchQueue.global(qos: .utility)
        let keepWriting = UnsafeMutablePointer<Bool>.allocate(capacity: 1)
        keepWriting.initialize(to: true)
        defer { keepWriting.deinitialize(count: 1); keepWriting.deallocate() }
        writerQ.async {
            var toggler = false
            while keepWriting.pointee {
                do {
                    if toggler {
                        _ = try db.deleteEquals(table: "t", column: "id", value: .int(Int64(Int.random(in: 0..<max(1, iterations)))))
                    } else {
                        _ = try db.insert(into: "t", row: ["id": .int(Int64(Int.random(in: 0..<Int.max>>20)))])
                    }
                    toggler.toggle()
                } catch { /* ignore */ }
            }
        }
        let tid = try db.begin(isolation: .repeatableRead)
        let clock = ContinuousClock(); let start = clock.now
        let rows = try db.scan("t", tid: tid)
        let elapsed = clock.now - start
        try db.commit(tid)
        keepWriting.pointee = false
        precondition(!rows.isEmpty)
        return BenchmarkResult(name: Scenario.mvccSnapshotRead.rawValue, iterations: rows.count, elapsed: elapsed)
    }

    // MARK: - Planner
    private static func runPlannerIndexScan(iterations: Int, granular: Bool) throws -> BenchmarkResult {
        let fm = FileManager.default
        let tmp = try makeTempDir()
        var cfg = DBConfig(dataDir: tmp.path)
        cfg.storageEngine = "FileHeap"
        cfg.autoCompactionEnabled = false
        let db = Database(config: cfg)
        try db.createTable("users")
        for i in 0..<iterations {
            _ = try db.insert(into: "users", row: ["id": .int(Int64(i)), "name": .string("u\(i)")])
        }
        try db.createIndex(name: "idx_users_id", on: "users", columns: ["id"], using: "BTree")
        try db.rebuildIndexBulk(table: "users", index: "idx_users_id")
        let pred = QueryPredicate(column: "id", op: .equals, value: .int(Int64(iterations / 2)))
        let users = QueryTableRef(name: "users", predicates: [pred], projection: ["id", "name"], indexHint: "idx_users_id")
        let req = QueryRequest(root: users, joins: [], limit: nil, parallelism: 1)
        let clock = ContinuousClock(); let start = clock.now
        if granular {
            let qn = min(1_000, max(1, iterations))
            var lat: [Double] = []; lat.reserveCapacity(qn)
            var rowsFetched = 0
            for _ in 0..<qn {
                let t0 = clock.now
                let out = try db.executeQuery(req)
                let t1 = clock.now
                rowsFetched &+= out.count
                lat.append(msDelta(t0, t1))
            }
            let elapsed = clock.now - start
            precondition(rowsFetched > 0)
            return BenchmarkResult(name: Scenario.plannerIndexScan.rawValue, iterations: qn, elapsed: elapsed, latenciesMs: lat, metadata: ["rows_fetched":"\(rowsFetched)"])
        } else {
            let out = try db.executeQuery(req)
            let elapsed = clock.now - start
            precondition(!out.isEmpty)
            return BenchmarkResult(name: Scenario.plannerIndexScan.rawValue, iterations: out.count, elapsed: elapsed)
        }
    }

    private static func runPlannerSortLimit(iterations: Int, granular: Bool) throws -> BenchmarkResult {
        var cfg = DBConfig(storageEngine: "InMemory")
        cfg.autoCompactionEnabled = false
        let db = Database(config: cfg)
        try db.createTable("orders")
        for i in 0..<iterations { _ = try db.insert(into: "orders", row: ["id": .int(Int64(i)), "total": .double(Double.random(in: 1..<1000))]) }
        let orders = QueryTableRef(name: "orders", projection: ["id", "total"])
        let req = QueryRequest(root: orders,
                               joins: [],
                               orderBy: [SortOperator.SortKey(column: "orders.total", ascending: false)],
                               limit: max(1, iterations / 10),
                               parallelism: 2)
        let clock = ContinuousClock(); let start = clock.now
        if granular {
            let qn = min(1_000, max(1, iterations / 10))
            var lat: [Double] = []; lat.reserveCapacity(qn)
            var total = 0
            for _ in 0..<qn {
                let t0 = clock.now
                let out = try db.executeQuery(req)
                let t1 = clock.now
                total &+= out.count
                lat.append(msDelta(t0, t1))
            }
            let elapsed = clock.now - start
            precondition(total > 0)
            return BenchmarkResult(name: Scenario.plannerSortLimit.rawValue, iterations: qn, elapsed: elapsed, latenciesMs: lat, metadata: ["rows_total":"\(total)"])
        } else {
            let out = try db.executeQuery(req)
            let elapsed = clock.now - start
            precondition(!out.isEmpty)
            return BenchmarkResult(name: Scenario.plannerSortLimit.rawValue, iterations: out.count, elapsed: elapsed)
        }
    }

    // MARK: - Maintenance
    private static func runCheckpoint(iterations: Int) throws -> BenchmarkResult {
        let fm = FileManager.default
        let tmp = try makeTempDir(); defer { try? fm.removeItem(at: tmp) }
        var cfg = DBConfig(dataDir: tmp.path)
        cfg.storageEngine = "FileHeap"
        cfg.walEnabled = true
        cfg.autoCompactionEnabled = false
        let result: BenchmarkResult
        do {
            let db = Database(config: cfg)
            try db.createTable("t")
            let n = cappedDiskIterations(iterations)
            for i in 0..<n { _ = try db.insert(into: "t", row: ["id": .int(Int64(i))]) }
            let clock = ContinuousClock(); let start = clock.now
            try db.checkpoint()
            let elapsed = clock.now - start
            result = BenchmarkResult(name: Scenario.checkpoint.rawValue, iterations: 1, elapsed: elapsed)
        }
        try? fm.removeItem(at: tmp)
        return result
    }

    private static func runVacuumCompact(iterations: Int) throws -> BenchmarkResult {
        let fm = FileManager.default
        let tmp = try makeTempDir()
        var cfg = DBConfig(dataDir: tmp.path)
        cfg.storageEngine = "FileHeap"
        cfg.autoCompactionEnabled = false
        let result: BenchmarkResult
        do {
            let db = Database(config: cfg)
            try db.createTable("t")
            let n = cappedDiskIterations(iterations)
            for i in 0..<n { _ = try db.insert(into: "t", row: ["id": .int(Int64(i))]) }
            // Delete half to create fragmentation
            for i in stride(from: 0, to: n, by: 2) { _ = try db.deleteEquals(table: "t", column: "id", value: .int(Int64(i))) }
            let clock = ContinuousClock(); let start = clock.now
            _ = try db.compactTable(table: "t", pageId: nil)
            let elapsed = clock.now - start
            result = BenchmarkResult(name: Scenario.vacuumCompact.rawValue, iterations: n, elapsed: elapsed)
        }
        try? fm.removeItem(at: tmp)
        return result
    }

    private static func printUsage() {
        print("Usage: benchmarks-extra [iterations] [scenario] [--workers=N] [--granular] [--json]")
        print("  iterations: numero di iterazioni (default 10000; alcuni scenari sono limitati)")
        print("  scenario:   uno tra \(Scenario.allCases.map { $0.rawValue }.joined(separator: ", ")) oppure omesso per eseguire tutti")
        print("  --workers:  per scenari concorrenti (es. tx-contention), default = logical cores")
        print("  --granular: misura la latenza per singola operazione dove applicabile")
        print("  --json:     stampa report in formato JSON (oltre al summary)")
        print("Examples:")
        print("  benchmarks-extra 5000 btree-bulk-build")
        print("  benchmarks-extra 20000 tx-contention --workers=8 --granular --json")
    }
}
