//
//  main.swift
//  Test Group Commit
//

import Foundation
import ColibriCore

print("═══════════════════════════════════════════════════════════")
print("  Colibrì-DB Group Commit Performance Tests")
print("═══════════════════════════════════════════════════════════")
print("")

func testBasicGroupCommit() throws {
    print("🧪 Test 1: Basic Group Commit Comparison")
    print("─────────────────────────────────────────────────────────\n")
    
    let testDir = "/tmp/colibri_group_commit_test_\(UUID().uuidString)"
    defer { try? FileManager.default.removeItem(atPath: testDir) }
    
    let iterations = 500  // Reduced for quick test
    
    // Test WITHOUT Group Commit
    print("Testing WITHOUT Group Commit...")
    var config1 = DBConfig(dataDir: testDir + "_nogc", storageEngine: "FileHeap")
    config1.walEnabled = true
    config1.walGroupCommitMs = 0.0  // Disabled
    config1.defaultIsolationLevel = IsolationLevel.readCommitted
    
    let db1 = Database(config: config1)
    try db1.createTable("test")
    
    let start1 = Date()
    for i in 0..<iterations {
        let tid = try db1.begin()
        try db1.insert(into: "test", row: ["id": .int(Int64(i)), "value": .string("test\(i)")], tid: tid)
        try db1.commit(tid)
    }
    let elapsed1 = Date().timeIntervalSince(start1)
    
    try db1.close()
    
    print("  ✓ \(iterations) commits in \(String(format: "%.3f", elapsed1))s")
    print("  ✓ \(String(format: "%.2f", Double(iterations) / elapsed1)) commits/sec")
    
    // Test WITH Group Commit
    print("\nTesting WITH Group Commit...")
    var config2 = DBConfig(dataDir: testDir + "_gc", storageEngine: "FileHeap")
    config2.walEnabled = true
    config2.walGroupCommitMs = 2.0  // Enabled
    config2.defaultIsolationLevel = IsolationLevel.readCommitted
    
    let db2 = Database(config: config2)
    try db2.createTable("test")
    
    let start2 = Date()
    for i in 0..<iterations {
        let tid = try db2.begin()
        try db2.insert(into: "test", row: ["id": .int(Int64(i)), "value": .string("test\(i)")], tid: tid)
        try db2.commit(tid)
    }
    let elapsed2 = Date().timeIntervalSince(start2)
    
    // Get metrics
    if let metrics = db2.groupCommitMetrics() {
        print("  ✓ \(iterations) commits in \(String(format: "%.3f", elapsed2))s")
        print("  ✓ \(String(format: "%.2f", Double(iterations) / elapsed2)) commits/sec")
        print("\n  Group Commit Metrics:")
        print("    • Total commits: \(metrics.totalCommits)")
        print("    • Total batches: \(metrics.totalBatches)")
        print("    • Average batch size: \(String(format: "%.1f", metrics.averageBatchSize))")
        print("    • Largest batch: \(metrics.largestBatch)")
        print("    • Sync reduction: \(String(format: "%.1f%%", metrics.syncReduction * 100))")
        print("    • Performance multiplier: \(String(format: "%.1fx", metrics.performanceMultiplier))")
    }
    
    try db2.close()
    
    // Calculate improvement
    let speedup = elapsed1 / elapsed2
    print("\n  📊 Performance Improvement: \(String(format: "%.2fx", speedup)) faster")
    
    if speedup >= 2.0 {
        print("  ✅ Significant improvement achieved!")
    } else if speedup >= 1.5 {
        print("  ⚠️  Moderate improvement")
    } else {
        print("  ⚠️  Limited improvement (expected in small tests)")
    }
}

do {
    try testBasicGroupCommit()
    
    print("\n\n")
    print("═══════════════════════════════════════════════════════════")
    print("  ✅ Group Commit Test Completed Successfully!")
    print("═══════════════════════════════════════════════════════════")
    
} catch {
    print("\n❌ Test Error: \(error)")
    exit(1)
}

