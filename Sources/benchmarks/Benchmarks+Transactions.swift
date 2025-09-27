import Foundation
import ColibriCore

extension BenchmarkCLI {
    // MARK: - Transazioni
    static func runTxCommit(iterations: Int, granular: Bool) throws -> BenchmarkResult {
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
            return BenchmarkResult(name: Scenario.txCommit.rawValue, iterations: iterations, elapsed: elapsed, latenciesMs: lat, metadata: ["wal_enabled":"false"]) 
        } else {
            for i in 0..<iterations {
                let tid = try db.begin()
                _ = try db.insert(into: "t", row: ["id": .int(Int64(i))], tid: tid)
                try db.commit(tid)
            }
            let elapsed = clock.now - start
            return BenchmarkResult(name: Scenario.txCommit.rawValue, iterations: iterations, elapsed: elapsed, metadata: ["wal_enabled":"false"]) 
        }
    }

    static func runTxRollback(iterations: Int, granular: Bool) throws -> BenchmarkResult {
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
            return BenchmarkResult(name: Scenario.txRollback.rawValue, iterations: iterations, elapsed: elapsed, latenciesMs: lat, metadata: ["wal_enabled":"false"]) 
        } else {
            for i in 0..<iterations {
                let tid = try db.begin()
                _ = try db.insert(into: "t", row: ["id": .int(Int64(i))], tid: tid)
                try db.rollback(tid)
            }
            let elapsed = clock.now - start
            return BenchmarkResult(name: Scenario.txRollback.rawValue, iterations: iterations, elapsed: elapsed, metadata: ["wal_enabled":"false"]) 
        }
    }

    static func runTxContention(iterations: Int, workers: Int, granular: Bool) throws -> BenchmarkResult {
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
                            lat.append(msDelta(t0, t1))
                        }
                    } catch {
                        // ignoriamo errori, vogliamo stressare la contesa
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

    static func runMVCCSnapshotRead(iterations: Int) throws -> BenchmarkResult {
        var cfg = DBConfig(storageEngine: "InMemory")
        cfg.autoCompactionEnabled = false
        cfg.walEnabled = false
        let db = Database(config: cfg)
        try db.createTable("t")
        for i in 0..<iterations { _ = try db.insert(into: "t", row: ["id": .int(Int64(i))]) }
        let writerQ = DispatchQueue.global(qos: .utility)
        let keepWriting = ManagedAtomic<Bool>(true)
        writerQ.async {
            var toggler = false
            while keepWriting.load(ordering: .relaxed) {
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
        keepWriting.store(false, ordering: .relaxed)
        precondition(!rows.isEmpty)
        return BenchmarkResult(name: Scenario.mvccSnapshotRead.rawValue, iterations: rows.count, elapsed: elapsed)
    }
}


