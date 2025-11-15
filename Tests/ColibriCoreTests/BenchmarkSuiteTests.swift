//
//  BenchmarkSuiteTests.swift
//  ColibrìDB Performance Benchmarks
//
//  This suite complements the functional tests by producing concrete,
//  machine-readable metrics about how much data viene realmente salvata
//  e quanto tempo impiegano le principali operazioni (insert, read,
//  indici). I risultati vengono allegati al log test come JSON per poterli
//  tracciare nelle pipeline CI.
//

import XCTest
@testable import ColibriCore

final class BenchmarkSuiteTests: XCTestCase {
    
    // MARK: - Benchmark Result Model
    
    struct BenchmarkResult: Codable {
        let name: String
        let iterations: Int
        let bytesWritten: UInt64
        let durationSeconds: TimeInterval
        let throughputOpsPerSec: Double
        let bandwidthMBPerSec: Double
        let notes: String
    }
    
    // MARK: - Public Benchmarks
    
    /// Misura quante tuple vengono salvate, i byte prodotti su disco (data + WAL) e la velocità di commit.
    func testInsertThroughputBenchmark() async throws {
        let iterations = 10_000
        let tempDir = try makeTemporaryDirectory()
        defer { try? FileManager.default.removeItem(at: tempDir) }
        
        let db = try makeDatabase(at: tempDir, bufferPoolSize: 512)
        try await db.start()
        var didShutdown = false
        defer {
            if !didShutdown {
                Task {
                    try? await db.shutdown()
                }
            }
        }
        try await createBenchmarkTable(in: db)
        
        let txId = try await db.beginTransaction()
        let start = Date()
        var logicalBytes: UInt64 = 0
        
        for i in 0..<iterations {
            let payload = "value_\(i)"
            let row: Row = [
                "id": .int(Int64(i)),
                "value": .string(payload)
            ]
            logicalBytes += UInt64(approximateRowSize(row))
            _ = try await db.insert(table: "benchmark_table", row: row, txId: txId)
        }
        try await db.commit(txId: txId)
        let duration = Date().timeIntervalSince(start)
        
        // Flush pending WAL to capture final on-disk size
        try await db.shutdown()
        didShutdown = true
        
        let walBytes = fileSize(tempDir.appendingPathComponent("wal.log"))
        let heapBytes = fileSize(tempDir.appendingPathComponent("data.db"))
        let totalBytes = walBytes + heapBytes
        
        let throughput = Double(iterations) / duration
        let bandwidth = Double(totalBytes) / duration / 1_000_000.0
        
        attachResult(
            BenchmarkResult(
                name: "InsertThroughput",
                iterations: iterations,
                bytesWritten: totalBytes,
                durationSeconds: duration,
                throughputOpsPerSec: throughput,
                bandwidthMBPerSec: bandwidth,
                notes: "Logical payload \(logicalBytes) bytes; WAL+\(heapBytes) bytes on disk"
            )
        )
    }
    
    /// Misura il tempo necessario per leggere righe già salvate, usando query SQL per esercitare parser/optimizer/executor.
    func testSelectLatencyBenchmark() async throws {
        let rows = 2_000
        let selectProbes = 200
        
        let tempDir = try makeTemporaryDirectory()
        defer { try? FileManager.default.removeItem(at: tempDir) }
        
        let db = try makeDatabase(at: tempDir, bufferPoolSize: 512)
        try await db.start()
        var didShutdown = false
        defer {
            if !didShutdown {
                Task {
                    try? await db.shutdown()
                }
            }
        }
        try await createBenchmarkTable(in: db)
        
        // Seed data
        let seedTx = try await db.beginTransaction()
        for i in 0..<rows {
            let row: Row = [
                "id": .int(Int64(i)),
                "value": .string("seed_\(i)")
            ]
            _ = try await db.insert(table: "benchmark_table", row: row, txId: seedTx)
        }
        try await db.commit(txId: seedTx)
        
        // SELECT benchmark (random point lookups)
        var rng = SystemRandomNumberGenerator()
        let ids = (0..<selectProbes).map { _ in Int.random(in: 0..<rows, using: &rng) }
        
        let txId = try await db.beginTransaction()
        let start = Date()
        for id in ids {
            let query = "SELECT * FROM benchmark_table WHERE id = \(id)"
            _ = try await db.executeQuery(query, txId: txId)
        }
        try await db.commit(txId: txId)
        let duration = Date().timeIntervalSince(start)
        
        let throughput = Double(selectProbes) / duration
        
        attachResult(
            BenchmarkResult(
                name: "SelectLatency",
                iterations: selectProbes,
                bytesWritten: fileSize(tempDir.appendingPathComponent("wal.log")),
                durationSeconds: duration,
                throughputOpsPerSec: throughput,
                bandwidthMBPerSec: 0, // reads, non scriviamo nuovi dati
                notes: "Point-selects over \(rows) persisted rows"
            )
        )
        
        try await db.shutdown()
        didShutdown = true
    }

    /// Benchmark completo DML: INSERT -> UPDATE -> DELETE con misurazioni distinte.
    func testMixedDMLBenchmark() async throws {
        let insertCount = 15_000
        let updateCount = 7_500
        let deleteCount = 3_750
        
        let tempDir = try makeTemporaryDirectory()
        defer { try? FileManager.default.removeItem(at: tempDir) }
        
        let db = try makeDatabase(at: tempDir, bufferPoolSize: 1_024)
        try await db.start()
        var didShutdown = false
        defer {
            if !didShutdown {
                Task {
                    try? await db.shutdown()
                }
            }
        }
        try await createBenchmarkTable(in: db)
        
        var rids: [RID] = []
        rids.reserveCapacity(insertCount)
        
        // INSERT phase
        let insertTx = try await db.beginTransaction()
        let insertStart = Date()
        var insertBytes: UInt64 = 0
        for i in 0..<insertCount {
            let row: Row = [
                "id": .int(Int64(i)),
                "value": .string("value_\(i)")
            ]
            insertBytes += UInt64(approximateRowSize(row))
            let rid = try await db.insert(table: "benchmark_table", row: row, txId: insertTx)
            rids.append(rid)
        }
        try await db.commit(txId: insertTx)
        let insertDuration = Date().timeIntervalSince(insertStart)
        
        attachResult(
            BenchmarkResult(
                name: "DML-Insert",
                iterations: insertCount,
                bytesWritten: insertBytes,
                durationSeconds: insertDuration,
                throughputOpsPerSec: Double(insertCount) / insertDuration,
                bandwidthMBPerSec: Double(insertBytes) / insertDuration / 1_000_000.0,
                notes: "Inserted rows kept in memory for subsequent UPDATE/DELETE phases"
            )
        )
        
        // UPDATE phase
        let updateTx = try await db.beginTransaction()
        let updateStart = Date()
        let rowsToUpdate = Array(rids.prefix(updateCount))
        for (offset, rid) in rowsToUpdate.enumerated() {
            let newValue = Value.string("updated_\(offset)")
            try await db.update(
                table: "benchmark_table",
                rid: rid,
                row: ["value": newValue],
                txId: updateTx
            )
        }
        try await db.commit(txId: updateTx)
        let updateDuration = Date().timeIntervalSince(updateStart)
        
        attachResult(
            BenchmarkResult(
                name: "DML-Update",
                iterations: updateCount,
                bytesWritten: UInt64(updateCount * approximateValueSize(.string("updated_0"))),
                durationSeconds: updateDuration,
                throughputOpsPerSec: Double(updateCount) / updateDuration,
                bandwidthMBPerSec: Double(updateCount * approximateValueSize(.string("updated_0"))) / updateDuration / 1_000_000.0,
                notes: "In-place update of 'value' column via heap table"
            )
        )
        
        // DELETE phase
        let deleteTx = try await db.beginTransaction()
        let deleteStart = Date()
        let rowsToDelete = Array(rids.prefix(deleteCount))
        for rid in rowsToDelete {
            try await db.delete(table: "benchmark_table", rid: rid, txId: deleteTx)
        }
        try await db.commit(txId: deleteTx)
        let deleteDuration = Date().timeIntervalSince(deleteStart)
        
        attachResult(
            BenchmarkResult(
                name: "DML-Delete",
                iterations: deleteCount,
                bytesWritten: UInt64(deleteCount * MemoryLayout<PageSlot>.size),
                durationSeconds: deleteDuration,
                throughputOpsPerSec: Double(deleteCount) / deleteDuration,
                bandwidthMBPerSec: 0,
                notes: "Deletes mark tombstones; bytes estimate accounts for slot metadata"
            )
        )
        
        // Shutdown to flush metrics and capture final file sizes
        try await db.shutdown()
        didShutdown = true
        
        let walBytes = fileSize(tempDir.appendingPathComponent("wal.log"))
        let heapBytes = fileSize(tempDir.appendingPathComponent("data.db"))
        
        attachResult(
            BenchmarkResult(
                name: "DML-Summary",
                iterations: insertCount + updateCount + deleteCount,
                bytesWritten: walBytes + heapBytes,
                durationSeconds: insertDuration + updateDuration + deleteDuration,
                throughputOpsPerSec: Double(insertCount + updateCount + deleteCount) / (insertDuration + updateDuration + deleteDuration),
                bandwidthMBPerSec: Double(walBytes + heapBytes) / (insertDuration + updateDuration + deleteDuration) / 1_000_000.0,
                notes: "Final files -> WAL: \(walBytes) bytes, Heap: \(heapBytes) bytes"
            )
        )
    }
    
    /// Misura operazioni su B+Tree in memoria, utile per capire costi indice.
    func testBTreeIndexBenchmark() throws {
        let iterations = 100_000
        let btree = BTreeIndex()
        
        let insertStart = Date()
        for i in 0..<iterations {
            let key = Value.string("key_\(i)")
            let rid = RID(pageID: UInt64(i / 1024), slotID: UInt32(i % 1024))
            try btree.insert(key: key, rid: rid)
        }
        let insertDuration = Date().timeIntervalSince(insertStart)
        
        let searchStart = Date()
        var hits = 0
        for i in stride(from: 0, to: iterations, by: 50) {
            let key = Value.string("key_\(i)")
            if btree.search(key: key) != nil {
                hits += 1
            }
        }
        let searchDuration = Date().timeIntervalSince(searchStart)
        
        let insertOps = Double(iterations) / insertDuration
        let searchOps = Double(iterations / 50) / searchDuration
        
        attachResult(
            BenchmarkResult(
                name: "BTreeIndexInsert",
                iterations: iterations,
                bytesWritten: 0,
                durationSeconds: insertDuration,
                throughputOpsPerSec: insertOps,
                bandwidthMBPerSec: 0,
                notes: "In-memory insert benchmark"
            )
        )
        
        attachResult(
            BenchmarkResult(
                name: "BTreeIndexSearch",
                iterations: iterations / 50,
                bytesWritten: 0,
                durationSeconds: searchDuration,
                throughputOpsPerSec: searchOps,
                bandwidthMBPerSec: 0,
                notes: "Found \(hits) keys"
            )
        )
    }

    /// Hash index benchmark (actor-based) per misurare costo inserimenti/ricerche/cancellazioni.
    func testHashIndexBenchmark() async throws {
        let iterations = 120
        let hashIndex = HashIndex(isUnique: true)
        
        // Insert
        let insertStart = Date()
        for i in 0..<iterations {
            let key = Value.int(Int64(i))
            let rid = RID(pageID: UInt64(i / 1024), slotID: UInt32(i % 1024))
            try await hashIndex.insert(key: key, rid: rid)
        }
        let insertDuration = Date().timeIntervalSince(insertStart)
        
        // Search
        var hits = 0
        let lookupIterations = iterations / 20
        let searchStart = Date()
        for i in stride(from: 0, to: iterations, by: 20) {
            if let _ = try await hashIndex.search(key: .int(Int64(i))) {
                hits += 1
            }
        }
        let searchDuration = Date().timeIntervalSince(searchStart)
        
        // Delete
        let deleteStart = Date()
        for i in stride(from: 0, to: iterations, by: 50) {
            try await hashIndex.delete(key: .int(Int64(i)))
        }
        let deleteDuration = Date().timeIntervalSince(deleteStart)
        
        attachResult(
            BenchmarkResult(
                name: "HashIndexInsert",
                iterations: iterations,
                bytesWritten: 0,
                durationSeconds: insertDuration,
                throughputOpsPerSec: Double(iterations) / insertDuration,
                bandwidthMBPerSec: 0,
                notes: "Actor-based hash index with linear probing"
            )
        )
        
        attachResult(
            BenchmarkResult(
                name: "HashIndexSearch",
                iterations: lookupIterations,
                bytesWritten: 0,
                durationSeconds: searchDuration,
                throughputOpsPerSec: Double(lookupIterations) / searchDuration,
                bandwidthMBPerSec: 0,
                notes: "Search hits: \(hits)/\(lookupIterations)"
            )
        )
        
        attachResult(
            BenchmarkResult(
                name: "HashIndexDelete",
                iterations: iterations / 50,
                bytesWritten: 0,
                durationSeconds: deleteDuration,
                throughputOpsPerSec: Double(iterations / 50) / deleteDuration,
                bandwidthMBPerSec: 0,
                notes: "Deletes performed every 50th key"
            )
        )
    }
    
    // MARK: - Helpers
    
    private func makeTemporaryDirectory() throws -> URL {
        let url = FileManager.default.temporaryDirectory.appendingPathComponent(UUID().uuidString)
        try FileManager.default.createDirectory(at: url, withIntermediateDirectories: true)
        return url
    }
    
    private func makeDatabase(at directory: URL, bufferPoolSize: Int) throws -> ColibrìDB {
        let config = ColibrìDBConfiguration(
            dataDirectory: directory,
            bufferPoolSize: bufferPoolSize,
            maxConnections: 8,
            walBufferSize: 4 * 1024 * 1024,
            checkpointInterval: 30,
            logLevel: .error,
            enableStatistics: false,
            enableAutoAnalyze: false,
            disableWALFsyncForBenchmarks: true
        )
        return try ColibrìDB(config: config)
    }
    
    private func createBenchmarkTable(in db: ColibrìDB) async throws {
        let table = TableDefinition(
            name: "benchmark_table",
            columns: [
                ColumnDefinition(name: "id", type: .int, nullable: false),
                ColumnDefinition(name: "value", type: .string, nullable: true)
            ],
            primaryKey: ["id"]
        )
        try await db.createTable(table)
    }
    
    private func fileSize(_ url: URL) -> UInt64 {
        guard let attributes = try? FileManager.default.attributesOfItem(atPath: url.path),
              let size = attributes[.size] as? NSNumber else {
            return 0
        }
        return size.uint64Value
    }
    
    private func approximateRowSize(_ row: Row) -> Int {
        row.values.reduce(0) { partial, value in
            partial + approximateValueSize(value)
        }
    }
    
    private func approximateValueSize(_ value: Value) -> Int {
        switch value {
        case .int:
            return MemoryLayout<Int64>.size
        case .double:
            return MemoryLayout<Double>.size
        case .bool:
            return 1
        case .string(let s):
            return s.lengthOfBytes(using: .utf8)
        case .null:
            return 0
        case .decimal(let decimal):
            return NSDecimalNumber(decimal: decimal).stringValue.lengthOfBytes(using: .utf8)
        case .date:
            return MemoryLayout<Double>.size
        case .bytes(let data):
            return data.count
        }
    }
    
    private func attachResult(_ result: BenchmarkResult) {
        guard let data = try? JSONEncoder().encode(result) else {
            return
        }
        let attachment = XCTAttachment(data: data, uniformTypeIdentifier: "public.json")
        attachment.lifetime = .keepAlways
        attachment.name = "\(result.name)-benchmark.json"
        add(attachment)
        
        let humanReadable = """
        [Benchmark] \(result.name):
          iterations=\(result.iterations)
          bytesWritten=\(result.bytesWritten)
          duration=\(String(format: "%.3f", result.durationSeconds))s
          throughput=\(String(format: "%.2f", result.throughputOpsPerSec)) ops/s
          bandwidth=\(String(format: "%.2f", result.bandwidthMBPerSec)) MB/s
          notes=\(result.notes)
        """
        print(humanReadable)
    }
}

