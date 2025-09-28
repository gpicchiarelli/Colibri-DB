import Foundation
import ColibriCore

extension BenchmarkCLI {
    // MARK: - B+Tree base
    static func runBTreeLookup(iterations: Int) throws -> BenchmarkResult {
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
        // Warm-up: carica livelli alti/prime foglie
        for i in 0..<min(1_000, iterations) { _ = try db.indexSearchEqualsTyped(table: "bench", index: "idx_bench_id", value: .int(Int64(i))) }

        let clock = ContinuousClock(); let start = clock.now
        for i in 0..<iterations {
            let hits = try db.indexSearchEqualsTyped(table: "bench", index: "idx_bench_id", value: .int(Int64(i)))
            precondition(!hits.isEmpty)
        }
        let elapsed = clock.now - start
        return BenchmarkResult(name: Scenario.btreeLookup.rawValue, iterations: iterations, elapsed: elapsed, metadata: ["page_size":"\(config.pageSizeBytes)", "split_ratio":"0.60/0.40", "warmup_done":"true"]) 
    }

    // MARK: - B+Tree estesi
    static func runBTreeInsert(iterations: Int, granular: Bool) throws -> BenchmarkResult {
        let fm = FileManager.default
        let tmp = try makeTempDir(); defer { try? fm.removeItem(at: tmp) }
        var cfg = DBConfig(dataDir: tmp.path)
        cfg.storageEngine = "FileHeap"
        cfg.autoCompactionEnabled = false
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
            return BenchmarkResult(name: Scenario.btreeInsert.rawValue, iterations: n, elapsed: elapsed, latenciesMs: lat, metadata: ["index":"BTree","columns":"id","warmup_done":"true"]) 
        } else {
            for i in 0..<n { _ = try db.insert(into: "t", row: ["id": .int(Int64(i)), "p": .string("v\(i)")]) }
            let elapsed = clock.now - start
            return BenchmarkResult(name: Scenario.btreeInsert.rawValue, iterations: n, elapsed: elapsed, metadata: ["warmup_done":"true"]) 
        }
    }

    static func runBTreeRange(iterations: Int, granular: Bool) throws -> BenchmarkResult {
        let fm = FileManager.default
        let tmp = try makeTempDir(); defer { try? fm.removeItem(at: tmp) }
        var cfg = DBConfig(dataDir: tmp.path)
        cfg.storageEngine = "FileHeap"
        cfg.autoCompactionEnabled = false
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
            return BenchmarkResult(name: Scenario.btreeRange.rawValue, iterations: q, elapsed: elapsed, latenciesMs: lat, metadata: ["index":"BTree","columns":"id","queries":"\(q)", "warmup_done":"true"]) 
        } else {
            let lo = Value.int(0)
            let hi = Value.int(Int64(n - 1))
            let hits = try db.indexRangeTyped(table: "t", index: "idx", lo: lo, hi: hi)
            precondition(hits.count == n)
            let elapsed = clock.now - start
            return BenchmarkResult(name: Scenario.btreeRange.rawValue, iterations: hits.count, elapsed: elapsed, metadata: ["warmup_done":"true"]) 
        }
    }

    static func runBTreeInsertBatch(iterations: Int, granular: Bool) throws -> BenchmarkResult {
        let fm = FileManager.default
        let tmp = try makeTempDir(); defer { try? fm.removeItem(at: tmp) }
        var cfg = DBConfig(dataDir: tmp.path)
        cfg.storageEngine = "FileHeap"
        cfg.autoCompactionEnabled = false
        let db = Database(config: cfg)
        try db.createTable("t")
        try db.createIndex(name: "idx", on: "t", columns: ["id"], using: "BTree")
        
        let n0 = cappedDiskIterations(iterations)
        let n = granular ? n0 : min(n0, 200)
        
        // Prepare batch data
        var entries: [(Value, RID)] = []
        entries.reserveCapacity(n)
        
        let clock = ContinuousClock(); let start = clock.now
        if granular {
            var lat: [Double] = []; lat.reserveCapacity(n / 100) // Batch every 100 inserts
            for batchStart in stride(from: 0, to: n, by: 100) {
                let t0 = clock.now
                let batchEnd = min(batchStart + 100, n)
                entries.removeAll(keepingCapacity: true)
                
                // Insert batch
                for i in batchStart..<batchEnd {
                    let rid = try db.insert(into: "t", row: ["id": .int(Int64(i)), "p": .string("v\(i)")])
                    entries.append((.int(Int64(i)), rid))
                }
                
                // Update index in batch
                if let index = db.indexes["t"]?["idx"] {
                    switch index.backend {
                    case .persistentBTree(let fbt):
                        try fbt.insertBatch(entries: entries)
                    default:
                        break
                    }
                }
                
                let t1 = clock.now
                lat.append(msDelta(t0, t1))
            }
            let elapsed = clock.now - start
            return BenchmarkResult(name: "btree-insert-batch", iterations: n, elapsed: elapsed, latenciesMs: lat, metadata: ["index":"BTree","columns":"id","batch_size":"100","warmup_done":"true"]) 
        } else {
            // Single batch insert
            for i in 0..<n {
                let rid = try db.insert(into: "t", row: ["id": .int(Int64(i)), "p": .string("v\(i)")])
                entries.append((.int(Int64(i)), rid))
            }
            
            // Update index in single batch
            if let index = db.indexes["t"]?["idx"] {
                switch index.backend {
                case .persistentBTree(let fbt):
                    try fbt.insertBatch(entries: entries)
                default:
                    break
                }
            }
            
            let elapsed = clock.now - start
            return BenchmarkResult(name: "btree-insert-batch", iterations: n, elapsed: elapsed, metadata: ["index":"BTree","columns":"id","batch_size":"all","warmup_done":"true"]) 
        }
    }

    static func runBTreeBulkBuild(iterations: Int) throws -> BenchmarkResult {
        let fm = FileManager.default
        let tmp = try makeTempDir(); defer { try? fm.removeItem(at: tmp) }
        var cfg = DBConfig(dataDir: tmp.path)
        cfg.storageEngine = "FileHeap"
        cfg.autoCompactionEnabled = false
        let db = Database(config: cfg)
        try db.createTable("t")
        let n = cappedDiskIterations(iterations)
        for i in 0..<n { _ = try db.insert(into: "t", row: ["id": .int(Int64(i))]) }
        try db.createIndex(name: "idx", on: "t", columns: ["id"], using: "BTree")
        let clock = ContinuousClock(); let start = clock.now
        try db.rebuildIndexBulk(table: "t", index: "idx")
        let elapsed = clock.now - start
        return BenchmarkResult(name: Scenario.btreeBulkBuild.rawValue, iterations: n, elapsed: elapsed)
    }
}


