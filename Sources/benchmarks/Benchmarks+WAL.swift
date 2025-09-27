import Foundation
import ColibriCore

extension BenchmarkCLI {
    // MARK: - File heap e WAL
    static func runFileHeapInsert(iterations: Int, wal: Bool, fullSync: Bool, granular: Bool) throws -> BenchmarkResult {
        let fm = FileManager.default
        let tmp = try makeTempDir()
        var cfg = DBConfig(dataDir: tmp.path)
        cfg.storageEngine = "FileHeap"
        cfg.walEnabled = wal
        cfg.walFullFSyncEnabled = fullSync
        cfg.autoCompactionEnabled = false
        let db = Database(config: cfg)
        try db.createTable("t")
        let n0 = cappedDiskIterations(iterations)
        _ = warmupInserts(db: db, table: "t", count: min(2_000, n0))
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
            if let w = db.wal {
                let m = w.recentFlushMetrics()
                print("[wal-metrics] last_batch=\(m.lastBatch) last_sync_ns=\(m.lastSyncNs) flushes=\(m.flushes) total_batch=\(m.totalBatch) total_sync_ns=\(m.totalSyncNs)")
            }
            try? fm.removeItem(at: tmp)
            let scenarioName = wal ? (fullSync ? Scenario.fileHeapInsertWalFSync.rawValue : Scenario.fileHeapInsertWalOff.rawValue) : Scenario.fileHeapInsertWalOff.rawValue
            return BenchmarkResult(name: scenarioName, iterations: n, elapsed: elapsed, latenciesMs: lat, metadata: ["wal_enabled": String(wal), "wal_fullsync": String(fullSync), "warmup_done":"true"]) 
        } else {
            for i in 0..<n { _ = try db.insert(into: "t", row: ["id": .int(Int64(i)), "p": .string("v\(i)")]) }
            let elapsed = clock.now - start
            if let w = db.wal {
                let m = w.recentFlushMetrics()
                print("[wal-metrics] last_batch=\(m.lastBatch) last_sync_ns=\(m.lastSyncNs) flushes=\(m.flushes) total_batch=\(m.totalBatch) total_sync_ns=\(m.totalSyncNs)")
            }
            try? fm.removeItem(at: tmp)
            let scenarioName = wal ? (fullSync ? Scenario.fileHeapInsertWalFSync.rawValue : Scenario.fileHeapInsertWalOff.rawValue) : Scenario.fileHeapInsertWalOff.rawValue
            return BenchmarkResult(name: scenarioName, iterations: n, elapsed: elapsed, metadata: ["wal_enabled": String(wal), "wal_fullsync": String(fullSync), "warmup_done":"true"]) 
        }
    }

    static func runWALAppend(iterations: Int, algorithm: CompressionAlgorithm, granular: Bool) throws -> BenchmarkResult {
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
}


