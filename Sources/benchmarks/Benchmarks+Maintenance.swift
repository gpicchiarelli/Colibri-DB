import Foundation
import ColibriCore

extension BenchmarkCLI {
    // MARK: - Manutenzione
    static func runCheckpoint(iterations: Int) throws -> InternalBenchmarkResult {
        let fm = FileManager.default
        let tmp = try makeTempDir(); defer { try? fm.removeItem(at: tmp) }
        var cfg = DBConfig(dataDir: tmp.path)
        cfg.storageEngine = "FileHeap"
        cfg.walEnabled = true
        cfg.autoCompactionEnabled = false
        let db = Database(config: cfg)
        try db.createTable("t")
        let n = cappedDiskIterations(iterations)
        for i in 0..<n { _ = try db.insert(into: "t", row: ["id": .int(Int64(i))]) }
        let clock = ContinuousClock(); let start = clock.now
        try db.checkpoint()
        let elapsed = clock.now - start
        return BenchmarkResult(name: Scenario.checkpoint.rawValue, iterations: 1, elapsed: elapsed)
    }

    static func runVacuumCompact(iterations: Int) throws -> InternalBenchmarkResult {
        let fm = FileManager.default
        let tmp = try makeTempDir(); defer { try? fm.removeItem(at: tmp) }
        var cfg = DBConfig(dataDir: tmp.path)
        cfg.storageEngine = "FileHeap"
        cfg.autoCompactionEnabled = false
        let db = Database(config: cfg)
        try db.createTable("t")
        let n = cappedDiskIterations(iterations)
        for i in 0..<n { _ = try db.insert(into: "t", row: ["id": .int(Int64(i))]) }
        for i in stride(from: 0, to: n, by: 2) { _ = try db.deleteEquals(table: "t", column: "id", value: .int(Int64(i))) }
        let clock = ContinuousClock(); let start = clock.now
        _ = try db.compactTable(table: "t", pageId: nil)
        let elapsed = clock.now - start
        return BenchmarkResult(name: Scenario.vacuumCompact.rawValue, iterations: n, elapsed: elapsed)
    }
}


