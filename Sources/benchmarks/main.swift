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
}
