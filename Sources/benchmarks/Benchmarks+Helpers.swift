import Foundation
import ColibriCore

extension BenchmarkCLI {
    // Misura differenza in millisecondi tra due istanti
    static func msDelta(_ start: ContinuousClock.Instant, _ end: ContinuousClock.Instant) -> Double {
        let d = end - start
        return Double(d.components.seconds) * 1_000 + Double(d.components.attoseconds) / 1_000_000_000_000_000.0
    }

    // Crea directory temporanea per benchmark on‑disk
    static func makeTempDir() throws -> URL {
        let fm = FileManager.default
        let dir = fm.temporaryDirectory.appendingPathComponent("colibridb-bench-\(UUID().uuidString)", isDirectory: true)
        try fm.createDirectory(at: dir, withIntermediateDirectories: true)
        return dir
    }

    // Riduce la durata di scenari pesanti su disco in esecuzioni rapide/CI
    static func cappedDiskIterations(_ n: Int) -> Int {
        return min(n, 5_000)
    }

    // Esegue un warm-up di N operazioni prima della misura principale.
    @discardableResult
    static func warmupInserts(db: Database, table: String, count: Int) -> Int {
        guard count > 0 else { return 0 }
        var done = 0
        for i in 0..<count {
            do {
                _ = try db.insert(into: table, row: ["id": .int(Int64(-1 - i)), "p": .string("warmup")])
                done &+= 1
            } catch { break }
        }
        return done
    }

    // Utility per contenere tipi non sendable usati nei benchmark concorrenti
    final class NonSendableBox<T>: @unchecked Sendable { var value: T; init(_ v: T) { self.value = v } }

    // Colleziona latenze in modo thread‑safe
    final class LatCollector: @unchecked Sendable {
        private var items: [Double] = []
        private let lock = NSLock()
        func append(_ v: Double) { lock.lock(); items.append(v); lock.unlock() }
        func snapshot() -> [Double] { lock.lock(); let out = items; lock.unlock(); return out }
    }
    
    /// 🚀 OPTIMIZATION: Helper per raccogliere latenze individuali nei benchmark
    static func measureLatencies<T>(
        iterations: Int,
        operation: () throws -> T
    ) throws -> (results: [T], latencies: [Double], totalElapsed: Duration) {
        let clock = ContinuousClock()
        let start = clock.now
        
        var results: [T] = []
        var latencies: [Double] = []
        results.reserveCapacity(iterations)
        latencies.reserveCapacity(iterations)
        
        for _ in 0..<iterations {
            let t0 = clock.now
            let result = try operation()
            let t1 = clock.now
            
            results.append(result)
            latencies.append(msDelta(t0, t1))
        }
        
        let totalElapsed = clock.now - start
        return (results: results, latencies: latencies, totalElapsed: totalElapsed)
    }
    
    /// 🚀 OPTIMIZATION: Helper per benchmark senza valore di ritorno
    static func measureLatenciesVoid(
        iterations: Int,
        operation: () throws -> Void
    ) throws -> (latencies: [Double], totalElapsed: Duration) {
        let clock = ContinuousClock()
        let start = clock.now
        
        var latencies: [Double] = []
        latencies.reserveCapacity(iterations)
        
        for _ in 0..<iterations {
            let t0 = clock.now
            try operation()
            let t1 = clock.now
            
            latencies.append(msDelta(t0, t1))
        }
        
        let totalElapsed = clock.now - start
        return (latencies: latencies, totalElapsed: totalElapsed)
    }
}


