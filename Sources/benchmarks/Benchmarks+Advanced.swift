import Foundation
import ColibriCore

extension BenchmarkCLI {
    // MARK: - Benchmark avanzati

    static func runWALRecovery(iterations: Int) throws -> BenchmarkResult {
        let fm = FileManager.default
        let tmp = try makeTempDir()

        // Configurazione con WAL attivo
        var cfg = DBConfig(dataDir: tmp.path, storageEngine: "FileHeap")
        cfg.walEnabled = true
        cfg.walFullFSyncEnabled = false
        cfg.walGroupCommitMs = 2.0

        // 1. Prima esecuzione: generiamo mutazioni e forziamo WAL
        do {
            let db = Database(config: cfg)
            if (try? db.createTable("t")) == nil {
                // tabella già esistente
            }
            for i in 0..<iterations {
                let tid = try db.begin()
                _ = try db.insert(into: "t", row: ["id": .int(Int64(i)), "data": .string("recovery_test_\(i)")], tid: tid)
                if i % 2 == 0 {
                    try db.commit(tid)
                } else {
                    try db.rollback(tid)
                }
            }
            try db.close()
        }

        // 2. Seconda esecuzione: creiamo un nuovo Database che esegue il recovery
        let start = ContinuousClock().now
        let recoveredDB = Database(config: cfg) // `replayGlobalWAL()` avviene nel costruttore
        let elapsed = ContinuousClock().now - start

        // Verifica dati recuperati (non rigida, giusto per mostrare output)
        let recoveredRows = (try? recoveredDB.scan("t")) ?? []
        let metrics = SystemMonitor(database: recoveredDB).getCurrentMetrics()

        try? fm.removeItem(at: tmp)

        return BenchmarkResult(
            name: Scenario.walRecovery.rawValue,
            iterations: recoveredRows.count,
            elapsed: elapsed,
            metadata: [
                "recovered_rows": String(recoveredRows.count),
                "recovery_latency_ms": String(format: "%.3f", Double(elapsed.components.seconds) * 1000.0),
                "wal_path": tmp.appendingPathComponent("global.wal").path
            ],
            systemMetrics: metrics
        )
    }

    static func runWALStress(iterations: Int, granular: Bool) throws -> BenchmarkResult {
        let fm = FileManager.default
        let tmp = try makeTempDir()

        var cfg = DBConfig(dataDir: tmp.path, storageEngine: "FileHeap")
        cfg.walEnabled = true
        cfg.walFullFSyncEnabled = false
        cfg.walGroupCommitMs = 0.1  // Group commit molto aggressivo
        cfg.walCompression = .lzfse

        let db = Database(config: cfg)
        try db.createTable("t")

        // Prepara dati di stress (record molto grandi)
        let largeData = String(repeating: "A", count: 1024) // 1KB di dati

        let clock = ContinuousClock(); let start = clock.now

        if granular {
            var lat: [Double] = []; lat.reserveCapacity(iterations)
            for i in 0..<iterations {
                let t0 = clock.now
                let tid = try db.begin()
                _ = try db.insert(into: "t", row: ["id": .int(Int64(i)), "data": .string("\(largeData)_\(i)")], tid: tid)
                try db.commit(tid)
                let t1 = clock.now
                lat.append(msDelta(t0, t1))
            }
            let elapsed = clock.now - start
            let systemMetrics = SystemMonitor(database: db).getCurrentMetrics()
            try? fm.removeItem(at: tmp)
            return BenchmarkResult(name: Scenario.walStress.rawValue, iterations: iterations, elapsed: elapsed, latenciesMs: lat, metadata: ["wal_stress":"high", "data_size":"1KB"], systemMetrics: systemMetrics)
        } else {
            for i in 0..<iterations {
                let tid = try db.begin()
                _ = try db.insert(into: "t", row: ["id": .int(Int64(i)), "data": .string("\(largeData)_\(i)")], tid: tid)
                try db.commit(tid)
            }
            let elapsed = clock.now - start
            let systemMetrics = SystemMonitor(database: db).getCurrentMetrics()
            try? fm.removeItem(at: tmp)
            return BenchmarkResult(name: Scenario.walStress.rawValue, iterations: iterations, elapsed: elapsed, metadata: ["wal_stress":"high", "data_size":"1KB"], systemMetrics: systemMetrics)
        }
    }

    static func runSystemLoad(iterations: Int, granular: Bool) throws -> BenchmarkResult {
        let fm = FileManager.default
        let tmp = try makeTempDir()

        var cfg = DBConfig(dataDir: tmp.path, storageEngine: "FileHeap")
        cfg.walEnabled = true
        cfg.walFullFSyncEnabled = true  // Full fsync per stress I/O
        cfg.walGroupCommitMs = 10.0  // Group commit lungo per accumulare molti record

        let db = Database(config: cfg)
        try db.createTable("t")

        // Crea SystemMonitor per metriche continue
        let monitor = SystemMonitor(database: db)
        monitor.startMonitoring(interval: 0.1)

        let clock = ContinuousClock(); let start = clock.now

        if granular {
            var lat: [Double] = []; lat.reserveCapacity(iterations)
            for i in 0..<iterations {
                let t0 = clock.now
                let tid = try db.begin()
                _ = try db.insert(into: "t", row: ["id": .int(Int64(i)), "data": .string("system_load_test_\(i)")], tid: tid)
                try db.commit(tid)
                let t1 = clock.now
                lat.append(msDelta(t0, t1))
            }
            let elapsed = clock.now - start
            let systemMetrics = monitor.getCurrentMetrics()
            monitor.stopMonitoring()
            try? fm.removeItem(at: tmp)
            return BenchmarkResult(name: Scenario.systemLoad.rawValue, iterations: iterations, elapsed: elapsed, latenciesMs: lat, metadata: ["fsync_enabled":"true", "group_commit":"10ms"], systemMetrics: systemMetrics)
        } else {
            for i in 0..<iterations {
                let tid = try db.begin()
                _ = try db.insert(into: "t", row: ["id": .int(Int64(i)), "data": .string("system_load_test_\(i)")], tid: tid)
                try db.commit(tid)
            }
            let elapsed = clock.now - start
            let systemMetrics = monitor.getCurrentMetrics()
            monitor.stopMonitoring()
            try? fm.removeItem(at: tmp)
            return BenchmarkResult(name: Scenario.systemLoad.rawValue, iterations: iterations, elapsed: elapsed, metadata: ["fsync_enabled":"true", "group_commit":"10ms"], systemMetrics: systemMetrics)
        }
    }

    static func runMemoryPressure(iterations: Int) throws -> BenchmarkResult {
        var cfg = DBConfig(storageEngine: "InMemory")
        cfg.walEnabled = false  // No WAL per focus su memoria

        let db = Database(config: cfg)
        try db.createTable("t")

        // Monitor memoria
        let monitor = SystemMonitor(database: db)
        let initialMetrics = monitor.getCurrentMetrics()

        let clock = ContinuousClock(); let start = clock.now

        // Inserisci molti dati per stressare memoria
        for i in 0..<iterations {
            _ = try db.insert(into: "t", row: ["id": .int(Int64(i)), "data": .string(String(repeating: "X", count: 1000))])
        }

        let elapsed = clock.now - start
        let finalMetrics = monitor.getCurrentMetrics()

        return BenchmarkResult(
            name: Scenario.memoryPressure.rawValue,
            iterations: iterations,
            elapsed: elapsed,
            metadata: [
                "initial_memory_mb": String(format: "%.1f", Double(initialMetrics.memory.usedBytes) / 1_048_576.0),
                "final_memory_mb": String(format: "%.1f", Double(finalMetrics.memory.usedBytes) / 1_048_576.0),
                "memory_increase_mb": String(format: "%.1f", (Double(finalMetrics.memory.usedBytes) - Double(initialMetrics.memory.usedBytes)) / 1_048_576.0)
            ],
            systemMetrics: finalMetrics
        )
    }

    static func runConcurrentLoad(iterations: Int, workers: Int, granular: Bool) throws -> BenchmarkResult {
        let fm = FileManager.default
        let tmp = try makeTempDir()

        var cfg = DBConfig(dataDir: tmp.path, storageEngine: "FileHeap")
        cfg.walEnabled = true
        cfg.walFullFSyncEnabled = false
        cfg.walGroupCommitMs = 1.0  // Group commit veloce per concorrenti

        let db = Database(config: cfg)
        try db.createTable("t")

        let perWorker = max(1, iterations / workers)
        let group = DispatchGroup()
        let queue = DispatchQueue.global(qos: .userInitiated)
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
                        _ = try dbBox.value.insert(into: "t", row: ["id": .int(Int64(w * perWorker + i)), "worker": .int(Int64(w)), "data": .string("concurrent_\(w)_\(i)")], tid: tid)
                        try dbBox.value.commit(tid)
                        if granular {
                            let t1 = clock.now
                            lat.append(msDelta(t0, t1))
                        }
                    } catch {
                        // Ignora errori per stress test
                    }
                }
            }
            queue.async(execute: work)
        }

        group.wait()
        let elapsed = clock.now - start
        let systemMetrics = SystemMonitor(database: db).getCurrentMetrics()

        if granular {
            try? fm.removeItem(at: tmp)
            return BenchmarkResult(name: "concurrent-load-w\(workers)", iterations: perWorker * workers, elapsed: elapsed, latenciesMs: lat.snapshot(), metadata: ["workers":"\(workers)", "concurrent":"true"], systemMetrics: systemMetrics)
        } else {
            try? fm.removeItem(at: tmp)
            return BenchmarkResult(name: "concurrent-load-w\(workers)", iterations: perWorker * workers, elapsed: elapsed, metadata: ["workers":"\(workers)", "concurrent":"true"], systemMetrics: systemMetrics)
        }
    }

    static func runInsertVariability(iterations: Int, granular: Bool) throws -> BenchmarkResult {
        let fm = FileManager.default
        let tmp = try makeTempDir()

        var cfg = DBConfig(dataDir: tmp.path, storageEngine: "FileHeap")
        cfg.walEnabled = false  // Disabilita WAL per evitare crash
        cfg.walFullFSyncEnabled = false
        cfg.walGroupCommitMs = 5.0

        let db = Database(config: cfg)
        try db.createTable("t")

        // Test vari tipi di dati per misurare variabilità
        let dataPatterns = [
            "short": "x",
            "medium": String(repeating: "a", count: 100),
            "long": String(repeating: "b", count: 1000),
            "json": "{\"key\": \"value\", \"array\": [1,2,3], \"nested\": {\"inner\": \"data\"}}",
            "binary": Data((0..<512).map { _ in UInt8.random(in: 0...255) }).base64EncodedString()
        ]

        let clock = ContinuousClock(); let start = clock.now

        if granular {
            var lat: [Double] = []; lat.reserveCapacity(iterations)
            for i in 0..<iterations {
                let pattern = dataPatterns.keys.randomElement()!
                let data = dataPatterns[pattern]!
                let t0 = clock.now
                let tid = try db.begin()
                _ = try db.insert(into: "t", row: ["id": .int(Int64(i)), "pattern": .string(pattern), "data": .string(data)], tid: tid)
                try db.commit(tid)
                let t1 = clock.now
                lat.append(msDelta(t0, t1))
            }
            let elapsed = clock.now - start
            let systemMetrics = SystemMonitor(database: db).getCurrentMetrics()
            try? fm.removeItem(at: tmp)
            return BenchmarkResult(name: Scenario.insertVariability.rawValue, iterations: iterations, elapsed: elapsed, latenciesMs: lat, metadata: ["data_variability": "true", "patterns": String(dataPatterns.count)], systemMetrics: systemMetrics)
        } else {
            for i in 0..<iterations {
                let pattern = dataPatterns.keys.randomElement()!
                let data = dataPatterns[pattern]!
                let tid = try db.begin()
                _ = try db.insert(into: "t", row: ["id": .int(Int64(i)), "pattern": .string(pattern), "data": .string(data)], tid: tid)
                try db.commit(tid)
            }
            let elapsed = clock.now - start
            let systemMetrics = SystemMonitor(database: db).getCurrentMetrics()
            try? fm.removeItem(at: tmp)
            return BenchmarkResult(name: Scenario.insertVariability.rawValue, iterations: iterations, elapsed: elapsed, metadata: ["data_variability": "true", "patterns": String(dataPatterns.count)], systemMetrics: systemMetrics)
        }
    }

    static func runQueryLatency(iterations: Int, granular: Bool) throws -> BenchmarkResult {
        let fm = FileManager.default
        let tmp = try makeTempDir()

        var cfg = DBConfig(dataDir: tmp.path, storageEngine: "FileHeap")
        cfg.walEnabled = true
        cfg.walFullFSyncEnabled = false

        let db = Database(config: cfg)
        try db.createTable("t")

        // Pre-popola con dati vari
        for i in 0..<max(iterations, 1000) {
            let tid = try db.begin()
            _ = try db.insert(into: "t", row: ["id": .int(Int64(i)), "data": .string("query_test_\(i % 100)")], tid: tid)
            try db.commit(tid)
        }

        let clock = ContinuousClock(); let start = clock.now

        if granular {
            var lat: [Double] = []; lat.reserveCapacity(iterations)
            for i in 0..<iterations {
                let t0 = clock.now
                let tid = try db.begin(isolation: .readCommitted)
                let queryId = Int64(i % 100)  // Query per ID esistenti
                _ = try db.scan("t", tid: tid)
                try db.commit(tid)
                let t1 = clock.now
                lat.append(msDelta(t0, t1))
            }
            let elapsed = clock.now - start
            let systemMetrics = SystemMonitor(database: db).getCurrentMetrics()
            try? fm.removeItem(at: tmp)
            return BenchmarkResult(name: Scenario.queryLatency.rawValue, iterations: iterations, elapsed: elapsed, latenciesMs: lat, metadata: ["query_type": "scan", "isolation": "read_committed"], systemMetrics: systemMetrics)
        } else {
            for i in 0..<iterations {
                let tid = try db.begin(isolation: .readCommitted)
                let queryId = Int64(i % 100)
                _ = try db.scan("t", tid: tid)
                try db.commit(tid)
            }
            let elapsed = clock.now - start
            let systemMetrics = SystemMonitor(database: db).getCurrentMetrics()
            try? fm.removeItem(at: tmp)
            return BenchmarkResult(name: Scenario.queryLatency.rawValue, iterations: iterations, elapsed: elapsed, metadata: ["query_type": "scan", "isolation": "read_committed"], systemMetrics: systemMetrics)
        }
    }
}
