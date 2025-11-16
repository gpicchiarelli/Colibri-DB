//
//  main.swift
//  benchmarks - ColibrìDB Benchmarks
//
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//

import Foundation
import ColibriCore

@main
struct BenchmarksMain {
    static func main() async {
        print("ColibrìDB Benchmarks - Version 1.0.0\n")
        
        // Benchmark 1: Insert performance
        await benchmarkInsert()
        
        // Benchmark 2: Read performance
        await benchmarkRead()
        
        // Benchmark 3: BTree index operations
        await benchmarkBTreeIndex()
        
        // Benchmark 4: Hashing backends (SHA-256 vs XXHash64)
        benchmarkHashing()
        
        // Benchmark 5: CRC32 throughput (HW/fallback via unified API)
        benchmarkCRC32()
    }
    
    static func benchmarkInsert() async {
        print("=== Insert Benchmark ===")
        let iterations = 10_000
        let startTime = Date()
        
        let tempDir = FileManager.default.temporaryDirectory.appendingPathComponent(UUID().uuidString)
        try? FileManager.default.createDirectory(at: tempDir, withIntermediateDirectories: true)
        
        do {
            let config = ColibrìDBConfiguration(dataDirectory: tempDir, bufferPoolSize: 100)
            let db = try ColibrìDB(config: config)
            try await db.start()
            
            let tableDef = TableDefinition(
                name: "test_table",
                columns: [
                    ColumnDefinition(name: "id", type: .int, nullable: false),
                    ColumnDefinition(name: "value", type: .string, nullable: true)
                ]
            )
            try await db.createTable(tableDef)
            
            let txId = try await db.beginTransaction()
            
            for i in 0..<iterations {
                let row: Row = [
                    "id": .int(Int64(i)),
                    "value": .string("value_\(i)")
                ]
                _ = try await db.insert(table: "test_table", row: row, txId: txId)
            }
            
            try await db.commit(txId: txId)
            try await db.shutdown()
            
            let elapsed = Date().timeIntervalSince(startTime)
            let opsPerSec = Double(iterations) / elapsed
            
            print("  Inserted \(iterations) rows in \(String(format: "%.2f", elapsed))s")
            print("  Throughput: \(String(format: "%.0f", opsPerSec)) ops/s\n")
            
            try? FileManager.default.removeItem(at: tempDir)
        } catch {
            print("  Error: \(error)\n")
        }
    }
    
    static func benchmarkRead() async {
        print("=== Read Benchmark ===")
        print("  (Read benchmark requires data from insert benchmark)\n")
    }
    
    static func benchmarkBTreeIndex() async {
        print("=== BTree Index Benchmark ===")
        let iterations = 100_000
        let startTime = Date()
        
        let btree = BTreeIndex()
        
        // Insert
        for i in 0..<iterations {
            let key = Value.string("key_\(i)")
            let rid = RID(pageID: UInt64(i / 1000), slotID: UInt32(i % 1000))
            try? btree.insert(key: key, rid: rid)
        }
        
        let insertTime = Date().timeIntervalSince(startTime)
        
        // Search
        let searchStart = Date()
        var found = 0
        for i in stride(from: 0, to: iterations, by: 100) {
            let key = Value.string("key_\(i)")
            if btree.search(key: key) != nil {
                found += 1
            }
        }
        let searchTime = Date().timeIntervalSince(searchStart)
        
        let insertOpsPerSec = Double(iterations) / insertTime
        let searchOpsPerSec = Double(iterations / 100) / searchTime
        
        print("  Insert: \(iterations) ops in \(String(format: "%.2f", insertTime))s (\(String(format: "%.0f", insertOpsPerSec)) ops/s)")
        print("  Search: \(iterations / 100) ops in \(String(format: "%.2f", searchTime))s (\(String(format: "%.0f", searchOpsPerSec)) ops/s)")
        print("  Found: \(found)/\(iterations / 100) keys\n")
    }
    
    // MARK: - Hashing Benchmarks
    static func benchmarkHashing() {
        print("=== Hashing Benchmark (SHA-256 vs XXHash64) ===")
        let numItems = 200_000
        let values: [Value] = (0..<numItems).map { i in
            // Mixed content to mimic keys
            if i % 3 == 0 { return .string("key_\(i)") }
            if i % 3 == 1 { return .int(Int64(i)) }
            return .bytes(randomData(length: 32, seed: UInt64(i)))
        }
        
        // SHA-256 backend
        var t0 = Date()
        var acc1: UInt64 = 0
        for i in 0..<numItems {
            let (h1, h2) = HardwareHash.hash64x2(values[i], seed: UInt64(i), backend: .sha256)
            acc1 &+= (h1 ^ h2)
        }
        let shaElapsed = Date().timeIntervalSince(t0)
        
        // XXHash64 backend
        t0 = Date()
        var acc2: UInt64 = 0
        for i in 0..<numItems {
            let (h1, h2) = HardwareHash.hash64x2(values[i], seed: UInt64(i), backend: .xxhash64)
            acc2 &+= (h1 ^ h2)
        }
        let xxElapsed = Date().timeIntervalSince(t0)
        
        print("  Items: \(numItems)")
        print("  SHA-256: \(String(format: "%.2f", shaElapsed))s (\(String(format: "%.0f", Double(numItems)/shaElapsed)) ops/s) acc=\(acc1)")
        print("  XXHash64: \(String(format: "%.2f", xxElapsed))s (\(String(format: "%.0f", Double(numItems)/xxElapsed)) ops/s) acc=\(acc2)\n")
    }
    
    // MARK: - CRC32 Benchmarks
    static func benchmarkCRC32() {
        print("=== CRC32 Benchmark (HW if available, else fallback) ===")
        let sizes = [64, 256, 1024, 4096, 16384]
        let itersPerSize = 50_000
        
        for sz in sizes {
            var buffers: [Data] = []
            buffers.reserveCapacity(1000)
            for i in 0..<1000 { buffers.append(randomData(length: sz, seed: UInt64(i))) }
            
            var idx = 0
            let start = Date()
            var acc: UInt32 = 0
            for _ in 0..<itersPerSize {
                acc &+= CRC32Accelerator.calculate(buffers[idx])
                idx += 1
                if idx == buffers.count { idx = 0 }
            }
            let elapsed = Date().timeIntervalSince(start)
            let totalBytes = Double(itersPerSize * sz)
            let mbps = (totalBytes / elapsed) / (1024.0 * 1024.0)
            print("  Size \(sz)B: \(String(format: "%.2f", elapsed))s, \(String(format: "%.1f", mbps)) MB/s, acc=\(acc)")
        }
        print("")
    }
    
    // MARK: - Helpers
    static func randomData(length: Int, seed: UInt64) -> Data {
        var x = seed &+ 0x9E3779B97F4A7C15
        var bytes = [UInt8](repeating: 0, count: length)
        for i in 0..<length {
            // xorshift64*
            x ^= x >> 12; x ^= x << 25; x ^= x >> 27
            let v = x &* 2685821657736338717
            bytes[i] = UInt8(truncatingIfNeeded: v)
        }
        return Data(bytes)
    }
}
