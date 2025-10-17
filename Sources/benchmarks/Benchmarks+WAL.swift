import Foundation
import ColibriCore

extension BenchmarkCLI {
    // MARK: - File heap e WAL
    static func runFileHeapInsert(iterations: Int, wal: Bool, fullSync: Bool, granular: Bool) throws -> InternalBenchmarkResult {
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
            if let m = db.walRecentFlushMetrics() {
                print("[wal-metrics] last_batch=\(m.lastBatch) last_sync_ns=\(m.lastSyncNs) flushes=\(m.flushes) total_batch=\(m.totalBatch) total_sync_ns=\(m.totalSyncNs)")
            }
            try? fm.removeItem(at: tmp)
            let scenarioName = wal ? (fullSync ? Scenario.fileHeapInsertWalFSync.rawValue : Scenario.fileHeapInsertWalOff.rawValue) : Scenario.fileHeapInsertWalOff.rawValue
            return InternalBenchmarkResult(name: scenarioName, iterations: n, elapsed: elapsed, latenciesMs: lat, metadata: ["wal_enabled": String(wal), "wal_fullsync": String(fullSync), "warmup_done":"true"]) 
        } else {
            for i in 0..<n { _ = try db.insert(into: "t", row: ["id": .int(Int64(i)), "p": .string("v\(i)")]) }
            let elapsed = clock.now - start
            if let m = db.walRecentFlushMetrics() {
                print("[wal-metrics] last_batch=\(m.lastBatch) last_sync_ns=\(m.lastSyncNs) flushes=\(m.flushes) total_batch=\(m.totalBatch) total_sync_ns=\(m.totalSyncNs)")
            }
            try? fm.removeItem(at: tmp)
            let scenarioName = wal ? (fullSync ? Scenario.fileHeapInsertWalFSync.rawValue : Scenario.fileHeapInsertWalOff.rawValue) : Scenario.fileHeapInsertWalOff.rawValue
            return InternalBenchmarkResult(name: scenarioName, iterations: n, elapsed: elapsed, metadata: ["wal_enabled": String(wal), "wal_fullsync": String(fullSync), "warmup_done":"true"]) 
        }
    }

    static func runWALAppend(iterations: Int, algorithm: CompressionAlgorithm, granular: Bool) throws -> InternalBenchmarkResult {
        let fm = FileManager.default
        let tmp = try makeTempDir()
        _ = tmp.appendingPathComponent("wal.log").path

        // Crea configurazione per WAL globale
        var cfg = DBConfig(dataDir: tmp.path)
        cfg.walEnabled = true
        cfg.walFullFSyncEnabled = false
        cfg.walGroupCommitMs = 5.0
        cfg.walCompression = algorithm
        cfg.autoCompactionEnabled = false

        let db = Database(config: cfg)
        let globalWAL = db.globalWAL!

        // Prepara payload realistico (simula record WAL)
        let testRecord = WALHeapInsertRecord(
            dbId: 1,
            txId: 1,
            tableId: "test_table",
            pageId: 1,
            slotId: 1,
            rowData: Data("test_data_12345678901234567890".utf8)
        )

        let clock = ContinuousClock(); let start = clock.now
        if granular {
            var lat: [Double] = []; lat.reserveCapacity(iterations)
            for _ in 0..<iterations {
                let t0 = clock.now
                _ = try globalWAL.append(testRecord)
                let t1 = clock.now
                lat.append(msDelta(t0, t1))
            }
            let elapsed = clock.now - start
            try? fm.removeItem(at: tmp)
            return InternalBenchmarkResult(name: "wal-append-\(algorithm.rawValue)", iterations: iterations, elapsed: elapsed, latenciesMs: lat, metadata: ["compression":"\(algorithm.rawValue)", "wal_type":"global"])
        } else {
            for _ in 0..<iterations { _ = try globalWAL.append(testRecord) }
            let elapsed = clock.now - start
            try? fm.removeItem(at: tmp)
            return InternalBenchmarkResult(name: "wal-append-\(algorithm.rawValue)", iterations: iterations, elapsed: elapsed, metadata: ["compression":"\(algorithm.rawValue)", "wal_type":"global"])
        }
    }
}


