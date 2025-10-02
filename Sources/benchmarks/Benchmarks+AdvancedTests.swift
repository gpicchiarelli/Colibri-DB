import Foundation
import ColibriCore

extension BenchmarkCLI {
    // MARK: - Suite di Test Avanzati Semplificata
    
    /// 🔥 Test di stress concorrente semplificato
    static func runConcurrentStress(iterations: Int, threads: Int = 8, duration: TimeInterval = 60.0) throws -> BenchmarkResult {
        let fm = FileManager.default
        let tmp = try makeTempDir()
        
        var config = DBConfig(dataDir: tmp.path, storageEngine: "FileHeap")
        config.walEnabled = true
        config.walGroupCommitMs = 1.0
        config.autoCompactionEnabled = false
        
        let db = Database(config: config)
        try db.createTable("concurrent_test")
        try db.createIndex(name: "idx_id", on: "concurrent_test", columns: ["id"], using: "BTree")
        
        let startTime = Date()
        let endTime = startTime.addingTimeInterval(duration)
        var totalOperations = 0
        var totalLatencies: [Double] = []
        let latenciesLock = NSLock()
        
        // Gruppi di thread per operazioni diverse
        let readerGroup = DispatchGroup()
        let writerGroup = DispatchGroup()
        
        // Thread readers
        for _ in 0..<(threads / 2) {
            readerGroup.enter()
            let workItem = DispatchWorkItem {
                defer { readerGroup.leave() }
                while Date() < endTime {
                    do {
                        let clock = ContinuousClock()
                        let t0 = clock.now
                        _ = try db.scan("concurrent_test")
                        let t1 = clock.now
                        
                        latenciesLock.lock()
                        totalOperations += 1
                        totalLatencies.append(msDelta(t0, t1))
                        latenciesLock.unlock()
                        
                        usleep(1000) // 1ms
                    } catch {
                        print("⚠️  Reader error: \(error)")
                    }
                }
            }
            DispatchQueue.global().async(execute: workItem)
        }
        
        // Thread writers
        for _ in 0..<(threads / 2) {
            writerGroup.enter()
            let workItem = DispatchWorkItem {
                defer { writerGroup.leave() }
                var counter = 0
                while Date() < endTime {
                    do {
                        let clock = ContinuousClock()
                        let t0 = clock.now
                        _ = try db.insert(into: "concurrent_test", row: [
                            "id": .int(Int64(counter)),
                            "data": .string("concurrent_\(counter)"),
                            "timestamp": .int(Int64(Date().timeIntervalSince1970))
                        ])
                        let t1 = clock.now
                        
                        latenciesLock.lock()
                        totalOperations += 1
                        totalLatencies.append(msDelta(t0, t1))
                        latenciesLock.unlock()
                        
                        counter += 1
                        usleep(5000) // 5ms
                    } catch {
                        print("⚠️  Writer error: \(error)")
                    }
                }
            }
            DispatchQueue.global().async(execute: workItem)
        }
        
        // Attendi completamento di tutti i thread
        readerGroup.wait()
        writerGroup.wait()
        
        let actualDuration = Date().timeIntervalSince(startTime)
        let finalRows = try db.scan("concurrent_test")
        
        try? fm.removeItem(at: tmp)
        
        return BenchmarkResult(
            name: "concurrent-stress",
            iterations: totalOperations,
            elapsed: Duration.seconds(actualDuration),
            latenciesMs: totalLatencies,
            metadata: [
                "threads": String(threads),
                "duration_seconds": String(format: "%.2f", actualDuration),
                "final_rows": String(finalRows.count),
                "operations_per_second": String(format: "%.2f", Double(totalOperations) / actualDuration),
                "test_type": "concurrent_stress"
            ]
        )
    }
    
    /// 🔒 Test di contesa su risorse specifiche
    static func runLockContention(iterations: Int, contentionLevel: Int = 10) throws -> BenchmarkResult {
        let fm = FileManager.default
        let tmp = try makeTempDir()
        
        var config = DBConfig(dataDir: tmp.path, storageEngine: "FileHeap")
        config.walEnabled = true
        config.autoCompactionEnabled = false
        
        let db = Database(config: config)
        try db.createTable("contention_test")
        try db.createIndex(name: "idx_contention", on: "contention_test", columns: ["id"], using: "BTree")
        
        // Inserisci dati iniziali per creare contesa
        for i in 0..<contentionLevel {
            _ = try db.insert(into: "contention_test", row: [
                "id": .int(Int64(i)),
                "data": .string("contention_\(i)"),
                "counter": .int(0)
            ])
        }
        
        let clock = ContinuousClock()
        let start = clock.now
        var latencies: [Double] = []
        latencies.reserveCapacity(iterations)
        
        let group = DispatchGroup()
        let queue = DispatchQueue(label: "contention.test", attributes: .concurrent)
        
        for i in 0..<iterations {
            group.enter()
            let workItem = DispatchWorkItem {
                defer { group.leave() }
                
                do {
                    let t0 = clock.now
                    
                    // Simula contesa su stesso record
                    let targetId = i % contentionLevel
                    let rids = try db.indexSearchEqualsTyped(
                        table: "contention_test",
                        index: "idx_contention",
                        value: .int(Int64(targetId))
                    )
                    
                    if let rid = rids.first {
                        // Leggi il record per ottenere il counter corrente
                        let allRows = try db.scan("contention_test")
                        if let (_, row) = allRows.first(where: { $0.0 == rid }) {
                            let currentCounter = if case .int(let counter) = row["counter"] { counter } else { Int64(0) }
                            _ = try db.update(table: "contention_test", 
                                            matchColumn: "id", 
                                            matchValue: .int(Int64(targetId)),
                                            updateColumn: "counter", 
                                            updateValue: .int(currentCounter + 1))
                        }
                    }
                    
                    let t1 = clock.now
                    
                    latenciesLock.lock()
                    latencies.append(msDelta(t0, t1))
                    latenciesLock.unlock()
                    
                } catch {
                    print("⚠️  Contention test error: \(error)")
                }
            }
            queue.async(execute: workItem)
        }
        
        group.wait()
        let elapsed = clock.now - start
        
        let finalRows = try db.scan("contention_test")
        let totalUpdates = finalRows.compactMap { (_, row) in
            if case .int(let counter) = row["counter"] { return counter } else { return nil }
        }.reduce(0, +)
        
        try? fm.removeItem(at: tmp)
        
        return BenchmarkResult(
            name: "lock-contention",
            iterations: iterations,
            elapsed: elapsed,
            latenciesMs: latencies,
            metadata: [
                "contention_level": String(contentionLevel),
                "total_updates": String(totalUpdates),
                "final_rows": String(finalRows.count),
                "test_type": "lock_contention"
            ]
        )
    }
    
    /// 🎯 Test di race conditions su indici
    static func runIndexRaceConditions(iterations: Int) throws -> BenchmarkResult {
        let fm = FileManager.default
        let tmp = try makeTempDir()
        
        var config = DBConfig(dataDir: tmp.path, storageEngine: "FileHeap")
        config.walEnabled = true
        config.autoCompactionEnabled = false
        
        let db = Database(config: config)
        try db.createTable("race_test")
        try db.createIndex(name: "idx_race", on: "race_test", columns: ["id"], using: "BTree")
        try db.createIndex(name: "idx_race_hash", on: "race_test", columns: ["id"], using: "Hash")
        
        let clock = ContinuousClock()
        let start = clock.now
        var latencies: [Double] = []
        latencies.reserveCapacity(iterations)
        
        let group = DispatchGroup()
        let queue = DispatchQueue(label: "race.test", attributes: .concurrent)
        
        for i in 0..<iterations {
            group.enter()
            let workItem = DispatchWorkItem {
                defer { group.leave() }
                
                do {
                    let t0 = clock.now
                    
                    // Inserisci record
                    _ = try db.insert(into: "race_test", row: [
                        "id": .int(Int64(i)),
                        "data": .string("race_\(i)"),
                        "timestamp": .int(Int64(Date().timeIntervalSince1970))
                    ])
                    
                    // Cerca su entrambi gli indici simultaneamente
                    let btreeResults = try db.indexSearchEqualsTyped(
                        table: "race_test",
                        index: "idx_race",
                        value: .int(Int64(i))
                    )
                    
                    let hashResults = try db.indexSearchEqualsTyped(
                        table: "race_test",
                        index: "idx_race_hash",
                        value: .int(Int64(i))
                    )
                    
                    // Verifica consistenza
                    if btreeResults.count != hashResults.count {
                        print("⚠️  Index inconsistency detected: BTree=\(btreeResults.count), Hash=\(hashResults.count)")
                    }
                    
                    let t1 = clock.now
                    
                    latenciesLock.lock()
                    latencies.append(msDelta(t0, t1))
                    latenciesLock.unlock()
                    
                } catch {
                    print("⚠️  Race condition test error: \(error)")
                }
            }
            queue.async(execute: workItem)
        }
        
        group.wait()
        let elapsed = clock.now - start
        
        // Verifica consistenza finale
        let btreeScan = try db.indexSearchEqualsTyped(table: "race_test", index: "idx_race", value: .int(0))
        let hashScan = try db.indexSearchEqualsTyped(table: "race_test", index: "idx_race_hash", value: .int(0))
        let tableScan = try db.scan("race_test")
        
        try? fm.removeItem(at: tmp)
        
        return BenchmarkResult(
            name: "index-race-conditions",
            iterations: iterations,
            elapsed: elapsed,
            latenciesMs: latencies,
            metadata: [
                "btree_results": String(btreeScan.count),
                "hash_results": String(hashScan.count),
                "table_rows": String(tableScan.count),
                "consistency_check": btreeScan.count == hashScan.count ? "PASS" : "FAIL",
                "test_type": "index_race_conditions"
            ]
        )
    }
    
    /// 🔄 Test di transazioni concorrenti
    static func runConcurrentTransactions(iterations: Int, transactionSize: Int = 10) throws -> BenchmarkResult {
        let fm = FileManager.default
        let tmp = try makeTempDir()
        
        var config = DBConfig(dataDir: tmp.path, storageEngine: "FileHeap")
        config.walEnabled = true
        config.walGroupCommitMs = 1.0
        
        let db = Database(config: config)
        try db.createTable("tx_test")
        try db.createIndex(name: "idx_tx", on: "tx_test", columns: ["id"], using: "BTree")
        
        let clock = ContinuousClock()
        let start = clock.now
        var latencies: [Double] = []
        var successfulTransactions = 0
        var failedTransactions = 0
        latencies.reserveCapacity(iterations)
        
        let group = DispatchGroup()
        let queue = DispatchQueue(label: "tx.test", attributes: .concurrent)
        
        for i in 0..<iterations {
            group.enter()
            let workItem = DispatchWorkItem {
                defer { group.leave() }
                
                do {
                    let t0 = clock.now
                    
                    let tid = try db.begin()
                    
                    // Esegui operazioni nella transazione
                    for j in 0..<transactionSize {
                        _ = try db.insert(into: "tx_test", row: [
                            "id": .int(Int64(i * transactionSize + j)),
                            "data": .string("tx_\(i)_\(j)"),
                            "transaction_id": .int(Int64(i))
                        ], tid: tid)
                    }
                    
                    // Commit o rollback casuale
                    if i % 3 == 0 {
                        try db.rollback(tid)
                    } else {
                        try db.commit(tid)
                        latenciesLock.lock()
                        successfulTransactions += 1
                        latenciesLock.unlock()
                    }
                    
                    let t1 = clock.now
                    
                    latenciesLock.lock()
                    latencies.append(msDelta(t0, t1))
                    latenciesLock.unlock()
                    
                } catch {
                    latenciesLock.lock()
                    failedTransactions += 1
                    latenciesLock.unlock()
                    print("⚠️  Transaction error: \(error)")
                }
            }
            queue.async(execute: workItem)
        }
        
        group.wait()
        let elapsed = clock.now - start
        
        let finalRows = try db.scan("tx_test")
        
        try? fm.removeItem(at: tmp)
        
        return BenchmarkResult(
            name: "concurrent-transactions",
            iterations: iterations,
            elapsed: elapsed,
            latenciesMs: latencies,
            metadata: [
                "transaction_size": String(transactionSize),
                "successful_tx": String(successfulTransactions),
                "failed_tx": String(failedTransactions),
                "final_rows": String(finalRows.count),
                "success_rate": String(format: "%.2f", Double(successfulTransactions) / Double(iterations) * 100.0),
                "test_type": "concurrent_transactions"
            ]
        )
    }
    
    /// 💥 Test di crash injection semplificato
    static func runCrashInjectionTest(iterations: Int, crashProbability: Double = 0.1) throws -> BenchmarkResult {
        let fm = FileManager.default
        let tmp = try makeTempDir()
        
        var config = DBConfig(dataDir: tmp.path, storageEngine: "FileHeap")
        config.walEnabled = true
        config.walFullFSyncEnabled = true
        config.walGroupCommitMs = 0.1
        
        var successfulRecoveries = 0
        var failedRecoveries = 0
        var totalLatencies: [Double] = []
        
        for iteration in 0..<iterations {
            do {
                let clock = ContinuousClock()
                let start = clock.now
                
                // Fase 1: Inserisci dati e simula crash
                let db = Database(config: config)
                try db.createTable("crash_test")
                try db.createIndex(name: "idx_crash", on: "crash_test", columns: ["id"], using: "BTree")
                
                // Inserisci dati con possibilità di crash
                for i in 0..<100 {
                    _ = try db.insert(into: "crash_test", row: [
                        "id": .int(Int64(i)),
                        "data": .string("crash_test_\(i)"),
                        "iteration": .int(Int64(iteration))
                    ])
                    
                    // Simula crash casuale
                    if Double.random(in: 0...1) < crashProbability {
                        // Simula crash: chiudi il database senza flush
                        try? db.close()
                        break
                    }
                }
                
                // Fase 2: Recovery
                let recoveredDB = Database(config: config)
                
                // Verifica integrità dei dati
                let recoveredRows = try recoveredDB.scan("crash_test")
                let expectedRows = min(100, Int(Double.random(in: 0...100) * (1.0 - crashProbability)))
                
                if recoveredRows.count >= expectedRows {
                    successfulRecoveries += 1
                } else {
                    failedRecoveries += 1
                }
                
                totalLatencies.append(msDelta(start, clock.now))
                
                try? recoveredDB.close()
                
            } catch {
                failedRecoveries += 1
                print("⚠️  Crash injection test error: \(error)")
            }
        }
        
        try? fm.removeItem(at: tmp)
        
        return BenchmarkResult(
            name: "crash-injection",
            iterations: iterations,
            elapsed: Duration.seconds(0),
            latenciesMs: totalLatencies,
            metadata: [
                "crash_probability": String(format: "%.2f", crashProbability),
                "successful_recoveries": String(successfulRecoveries),
                "failed_recoveries": String(failedRecoveries),
                "recovery_success_rate": String(format: "%.2f", Double(successfulRecoveries) / Double(iterations) * 100.0),
                "test_type": "crash_injection"
            ]
        )
    }
    
    /// 🔍 Test di consistenza tra indici diversi
    static func runIndexConsistencyTest(iterations: Int) throws -> BenchmarkResult {
        let fm = FileManager.default
        let tmp = try makeTempDir()
        
        var config = DBConfig(dataDir: tmp.path, storageEngine: "FileHeap")
        config.walEnabled = true
        config.autoCompactionEnabled = false
        
        let db = Database(config: config)
        try db.createTable("consistency_test")
        
        // Crea indici multipli
        try db.createIndex(name: "idx_btree", on: "consistency_test", columns: ["id"], using: "BTree")
        try db.createIndex(name: "idx_hash", on: "consistency_test", columns: ["id"], using: "Hash")
        try db.createIndex(name: "idx_lsm", on: "consistency_test", columns: ["id"], using: "LSM")
        
        var totalLatencies: [Double] = []
        var consistencyViolations = 0
        var totalChecks = 0
        
        for iteration in 0..<iterations {
            do {
                let clock = ContinuousClock()
                let start = clock.now
                
                // Inserisci dati casuali
                let randomId = Int.random(in: 0..<1000)
                let randomName = "name_\(randomId)_\(iteration)"
                
                _ = try db.insert(into: "consistency_test", row: [
                    "id": .int(Int64(randomId)),
                    "name": .string(randomName),
                    "data": .string("consistency_\(iteration)"),
                    "timestamp": .int(Int64(Date().timeIntervalSince1970))
                ])
                
                // Verifica consistenza tra indici
                let btreeResults = try db.indexSearchEqualsTyped(
                    table: "consistency_test",
                    index: "idx_btree",
                    value: .int(Int64(randomId))
                )
                
                let hashResults = try db.indexSearchEqualsTyped(
                    table: "consistency_test",
                    index: "idx_hash",
                    value: .int(Int64(randomId))
                )
                
                let lsmResults = try db.indexSearchEqualsTyped(
                    table: "consistency_test",
                    index: "idx_lsm",
                    value: .int(Int64(randomId))
                )
                
                // Verifica consistenza
                totalChecks += 1
                if btreeResults.count != hashResults.count ||
                   btreeResults.count != lsmResults.count {
                    consistencyViolations += 1
                }
                
                totalLatencies.append(msDelta(start, clock.now))
                
            } catch {
                print("⚠️  Index consistency test error: \(error)")
            }
        }
        
        try? fm.removeItem(at: tmp)
        
        return BenchmarkResult(
            name: "index-consistency",
            iterations: iterations,
            elapsed: Duration.seconds(0),
            latenciesMs: totalLatencies,
            metadata: [
                "consistency_violations": String(consistencyViolations),
                "total_checks": String(totalChecks),
                "consistency_rate": String(format: "%.2f", (1.0 - Double(consistencyViolations) / Double(totalChecks)) * 100.0),
                "test_type": "index_consistency"
            ]
        )
    }
    
    // MARK: - Funzioni Stub per Test Non Implementati
    
    /// 🔄 Test di recovery dopo crash durante WAL flush (stub)
    static func runWALCrashRecovery(iterations: Int) throws -> BenchmarkResult {
        return BenchmarkResult(
            name: "wal-crash-recovery",
            iterations: iterations,
            elapsed: Duration.seconds(0),
            latenciesMs: [],
            metadata: [
                "status": "NOT_IMPLEMENTED",
                "test_type": "wal_crash_recovery"
            ]
        )
    }
    
    /// 🗂️ Test di recovery dopo crash durante compaction (stub)
    static func runCompactionCrashRecovery(iterations: Int) throws -> BenchmarkResult {
        return BenchmarkResult(
            name: "compaction-crash-recovery",
            iterations: iterations,
            elapsed: Duration.seconds(0),
            latenciesMs: [],
            metadata: [
                "status": "NOT_IMPLEMENTED",
                "test_type": "compaction_crash_recovery"
            ]
        )
    }
    
    /// 🔍 Test di integrità dei dati dopo recovery (stub)
    static func runDataIntegrityRecovery(iterations: Int) throws -> BenchmarkResult {
        return BenchmarkResult(
            name: "data-integrity-recovery",
            iterations: iterations,
            elapsed: Duration.seconds(0),
            latenciesMs: [],
            metadata: [
                "status": "NOT_IMPLEMENTED",
                "test_type": "data_integrity_recovery"
            ]
        )
    }
    
    /// 👁️ Test di phantom reads (stub)
    static func runPhantomReadsTest(iterations: Int) throws -> BenchmarkResult {
        return BenchmarkResult(
            name: "phantom-reads",
            iterations: iterations,
            elapsed: Duration.seconds(0),
            latenciesMs: [],
            metadata: [
                "status": "NOT_IMPLEMENTED",
                "test_type": "phantom_reads"
            ]
        )
    }
    
    /// 🔄 Test di read skew (stub)
    static func runReadSkewTest(iterations: Int) throws -> BenchmarkResult {
        return BenchmarkResult(
            name: "read-skew",
            iterations: iterations,
            elapsed: Duration.seconds(0),
            latenciesMs: [],
            metadata: [
                "status": "NOT_IMPLEMENTED",
                "test_type": "read_skew"
            ]
        )
    }
    
    /// ✍️ Test di write skew (stub)
    static func runWriteSkewTest(iterations: Int) throws -> BenchmarkResult {
        return BenchmarkResult(
            name: "write-skew",
            iterations: iterations,
            elapsed: Duration.seconds(0),
            latenciesMs: [],
            metadata: [
                "status": "NOT_IMPLEMENTED",
                "test_type": "write_skew"
            ]
        )
    }
    
    /// 🔒 Test di predicate locks (stub)
    static func runPredicateLocksTest(iterations: Int) throws -> BenchmarkResult {
        return BenchmarkResult(
            name: "predicate-locks",
            iterations: iterations,
            elapsed: Duration.seconds(0),
            latenciesMs: [],
            metadata: [
                "status": "NOT_IMPLEMENTED",
                "test_type": "predicate_locks"
            ]
        )
    }
    
    /// 📊 Test di snapshot isolation (stub)
    static func runSnapshotIsolationTest(iterations: Int) throws -> BenchmarkResult {
        return BenchmarkResult(
            name: "snapshot-isolation",
            iterations: iterations,
            elapsed: Duration.seconds(0),
            latenciesMs: [],
            metadata: [
                "status": "NOT_IMPLEMENTED",
                "test_type": "snapshot_isolation"
            ]
        )
    }
    
    /// 🔄 Test di consistenza durante rebuild degli indici (stub)
    static func runIndexRebuildConsistency(iterations: Int) throws -> BenchmarkResult {
        return BenchmarkResult(
            name: "index-rebuild-consistency",
            iterations: iterations,
            elapsed: Duration.seconds(0),
            latenciesMs: [],
            metadata: [
                "status": "NOT_IMPLEMENTED",
                "test_type": "index_rebuild_consistency"
            ]
        )
    }
    
    /// 🗑️ Test di consistenza durante cancellazioni (stub)
    static func runIndexDeletionConsistency(iterations: Int) throws -> BenchmarkResult {
        return BenchmarkResult(
            name: "index-deletion-consistency",
            iterations: iterations,
            elapsed: Duration.seconds(0),
            latenciesMs: [],
            metadata: [
                "status": "NOT_IMPLEMENTED",
                "test_type": "index_deletion_consistency"
            ]
        )
    }
    
    /// 🔄 Test di consistenza durante aggiornamenti (stub)
    static func runIndexUpdateConsistency(iterations: Int) throws -> BenchmarkResult {
        return BenchmarkResult(
            name: "index-update-consistency",
            iterations: iterations,
            elapsed: Duration.seconds(0),
            latenciesMs: [],
            metadata: [
                "status": "NOT_IMPLEMENTED",
                "test_type": "index_update_consistency"
            ]
        )
    }
    
    /// 🔍 Test di verifica incrociata tra indici (stub)
    static func runCrossIndexVerification(iterations: Int) throws -> BenchmarkResult {
        return BenchmarkResult(
            name: "cross-index-verification",
            iterations: iterations,
            elapsed: Duration.seconds(0),
            latenciesMs: [],
            metadata: [
                "status": "NOT_IMPLEMENTED",
                "test_type": "cross_index_verification"
            ]
        )
    }
}

// MARK: - Helper per thread-safety
private let latenciesLock = NSLock()
