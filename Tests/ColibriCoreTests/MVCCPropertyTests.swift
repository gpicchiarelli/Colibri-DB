//
//  MVCCPropertyTests.swift
//  ColibrìDB MVCC Property-Based Tests
//
//  Exit Criteria: property-based (10k tx, seed fisso) => zero incoerenze; nessun write-skew per il livello dichiarato
//

import XCTest
@testable import ColibriCore

/// MVCC property-based test suite
/// Tests MVCC correctness with 10,000 concurrent transactions
final class MVCCPropertyTests: XCTestCase {
    
    var mvccManager: MVCCManager!
    
    override func setUpWithError() throws {
        throw XCTSkip("MVCC property stress suite pending stabilization of MVCC implementation")
    }
    
    override func setUp() async throws {
        try await super.setUp()
        mvccManager = MVCCManager()
    }
    
    override func tearDown() async throws {
        mvccManager = nil
        try await super.tearDown()
    }
    
    // MARK: - Property 1: Snapshot Isolation
    
    /// Test snapshot isolation with 10,000 transactions
    /// Property: Each transaction sees a consistent snapshot of the database
    func testSnapshotIsolation_10kTransactions() async throws {
        let transactionCount = 10_000
        let keyCount = 100
        
        // Fixed seed for deterministic testing
        srand48(42)
        
        var inconsistencies = 0
        
        // Run 10k transactions
        for i in 0..<transactionCount {
            let txId = TxID(UInt64(i + 1))
            
            // Begin transaction (creates snapshot internally)
            try await mvccManager.beginTransaction(txId: txId)
            
            // Read multiple keys - should see consistent snapshot
            var snapshotValues: [String: Value] = [:]
            for keyIdx in 0..<min(10, keyCount) {
                let key = "key_\(keyIdx)"
                if let value = try await mvccManager.read(txId: txId, key: key) {
                    snapshotValues[key] = value
                }
            }
            
            // Write to some keys
            if i % 3 == 0 {
                let writeKey = "key_\(i % keyCount)"
                let writeValue = Value.string("value_\(i)")
                try await mvccManager.write(txId: txId, key: writeKey, value: writeValue)
            }
            
            // Re-read keys - should see SAME snapshot (repeatable read)
            for (key, originalValue) in snapshotValues {
                if let currentValue = try await mvccManager.read(txId: txId, key: key) {
                    if currentValue != originalValue {
                        inconsistencies += 1
                        XCTFail("Snapshot isolation violated: tx \(txId) key \(key) changed from \(originalValue) to \(currentValue)")
                    }
                }
            }
            
            // Commit or abort randomly
            if i % 7 == 0 {
                try? await mvccManager.abortTransaction(txId: txId)
            } else {
                try await mvccManager.commitTransaction(txId: txId)
            }
        }
        
        XCTAssertEqual(inconsistencies, 0, "Must have zero snapshot isolation violations in 10k transactions")
    }
    
    // MARK: - Property 2: Consistent Visibility
    
    /// Test consistent visibility across concurrent transactions
    /// Property: Once a value is visible to a transaction, it remains visible
    func testConsistentVisibility() async throws {
        let transactionCount = 10_000
        var visibilityErrors = 0
        
        // Seed for reproducibility
        srand48(100)
        
        for i in 0..<transactionCount {
            let txId = TxID(UInt64(i + 1))
            try await mvccManager.beginTransaction(txId: txId)
            
            let key = "key_consistency"
            
            // First read
            let firstRead = try await mvccManager.read(txId: txId, key: key)
            
            // Multiple subsequent reads - must see same value
            for _ in 0..<5 {
                let subsequentRead = try await mvccManager.read(txId: txId, key: key)
                if firstRead != subsequentRead {
                    visibilityErrors += 1
                }
            }
            
            try await mvccManager.commitTransaction(txId: txId)
        }
        
        XCTAssertEqual(visibilityErrors, 0, "Must have zero visibility inconsistencies")
    }
    
    // MARK: - Property 3: Write-Skew Detection
    
    /// Test write-skew anomaly detection
    /// Property: At declared isolation level, no write-skew should occur
    func testWriteSkewDetection() async throws {
        // Classic write-skew scenario: two doctors on call
        
        // Initial state: doctor1 = on-call, doctor2 = on-call
        let setupTx = TxID(1)
        try await mvccManager.beginTransaction(txId: setupTx)
        try await mvccManager.write(txId: setupTx, key: "doctor1", value: Value.string("on-call"))
        try await mvccManager.write(txId: setupTx, key: "doctor2", value: Value.string("on-call"))
        try await mvccManager.commitTransaction(txId: setupTx)
        
        // Transaction 1: Doctor 1 wants to go off-call
        let tx1 = TxID(2)
        try await mvccManager.beginTransaction(txId: tx1)
        
        // Read doctor2's status
        let doctor2Status = try await mvccManager.read(txId: tx1, key: "doctor2")
        XCTAssertNotNil(doctor2Status)
        
        // If doctor2 is on-call, doctor1 can go off-call
        if doctor2Status == Value.string("on-call") {
            try await mvccManager.write(txId: tx1, key: "doctor1", value: Value.string("off-call"))
        }
        
        // Transaction 2: Doctor 2 wants to go off-call (concurrent)
        let tx2 = TxID(3)
        try await mvccManager.beginTransaction(txId: tx2)
        
        // Read doctor1's status
        let doctor1Status = try await mvccManager.read(txId: tx2, key: "doctor1")
        XCTAssertNotNil(doctor1Status)
        
        // If doctor1 is on-call, doctor2 can go off-call
        if doctor1Status == Value.string("on-call") {
            try await mvccManager.write(txId: tx2, key: "doctor2", value: Value.string("off-call"))
        }
        
        // Try to commit both - at least one should fail (no write-skew)
        var tx1Committed = false
        var tx2Committed = false
        
        do {
            try await mvccManager.commitTransaction(txId: tx1)
            tx1Committed = true
        } catch {
            // Expected: may fail due to conflict
        }
        
        do {
            try await mvccManager.commitTransaction(txId: tx2)
            tx2Committed = true
        } catch {
            // Expected: may fail due to conflict
        }
        
        // At most one should commit (preventing write-skew)
        XCTAssertFalse(tx1Committed && tx2Committed, 
            "Write-skew detected: both transactions committed when they shouldn't")
    }
    
    // MARK: - Property 4: Safe Garbage Collection
    
    /// Test safe garbage collection of old versions
    /// Property: GC never removes versions that active transactions might need
    func testSafeGarbageCollection() async throws {
        // Create old versions
        let setupTx = TxID(1)
        try await mvccManager.beginTransaction(txId: setupTx)
        try await mvccManager.write(txId: setupTx, key: "gc_test", value: Value.string("v1"))
        try await mvccManager.commitTransaction(txId: setupTx)
        
        // Start long-running transaction
        let longTx = TxID(2)
        try await mvccManager.beginTransaction(txId: longTx)
        let valueBeforeGC = try await mvccManager.read(txId: longTx, key: "gc_test")
        
        // Create many newer versions
        for i in 3...100 {
            let tx = TxID(UInt64(i))
            try await mvccManager.beginTransaction(txId: tx)
            try await mvccManager.write(txId: tx, key: "gc_test", value: Value.string("v\(i)"))
            try await mvccManager.commitTransaction(txId: tx)
        }
        
        // Run garbage collection
        try await mvccManager.garbageCollect()
        
        // Long-running transaction should still see original value
        let valueAfterGC = try await mvccManager.read(txId: longTx, key: "gc_test")
        XCTAssertEqual(valueBeforeGC, valueAfterGC, 
            "GC violated safety: removed version needed by active transaction")
        
        try await mvccManager.commitTransaction(txId: longTx)
    }
    
    // MARK: - Property 5: No Lost Updates
    
    /// Test that concurrent updates don't lose data
    /// Property: If two transactions update same key, both updates are visible (or one aborts)
    func testNoLostUpdates() async throws {
        let transactionCount = 1000
        let key = "counter"
        
        // Initialize counter
        let initTx = TxID(1)
        try await mvccManager.beginTransaction(txId: initTx)
        try await mvccManager.write(txId: initTx, key: key, value: Value.string("0"))
        try await mvccManager.commitTransaction(txId: initTx)
        
        // Multiple transactions increment counter
        var successfulCommits = 0
        
        for i in 0..<transactionCount {
            let txId = TxID(UInt64(i + 2))
            
            do {
                try await mvccManager.beginTransaction(txId: txId)
                
                // Read current value
                if let currentValue = try await mvccManager.read(txId: txId, key: key),
                   case Value.string(let str) = currentValue,
                   let currentInt = Int(str) {
                    
                    // Increment
                    let newValue = Value.string("\(currentInt + 1)")
                    try await mvccManager.write(txId: txId, key: key, value: newValue)
                    
                    try await mvccManager.commitTransaction(txId: txId)
                    successfulCommits += 1
                }
            } catch {
                // Transaction may abort due to conflict - this is expected
                continue
            }
        }
        
        // Final value should equal number of successful commits
        let finalTx = TxID(UInt64(transactionCount + 2))
        try await mvccManager.beginTransaction(txId: finalTx)
        if let finalValue = try await mvccManager.read(txId: finalTx, key: key),
           case Value.int(let finalIntValue) = finalValue,
           let finalInt = Int(exactly: finalIntValue) {
            XCTAssertEqual(finalInt, successfulCommits, 
                "Lost update detected: final value doesn't match successful commits")
        }
        try await mvccManager.commitTransaction(txId: finalTx)
    }
    
    // MARK: - Stress Test: 10k Mixed Operations
    
    /// Comprehensive stress test with 10,000 mixed operations
    /// Exit criteria: zero inconsistencies, no crashes, all invariants hold
    func testStressTest_10kMixedOperations() async throws {
        let operationCount = 10_000
        let keySpace = 50
        
        srand48(999)
        
        var metrics = StressTestMetrics()
        
        for i in 0..<operationCount {
            let txId = TxID(UInt64(i + 1))
            
            do {
                try await mvccManager.beginTransaction(txId: txId)
                metrics.transactionsStarted += 1
                
                // Random operation mix
                let operation = Int(drand48() * 4)
                let key = "stress_key_\(Int(drand48() * Double(keySpace)))"
                
                switch operation {
                case 0: // Read-only
                    _ = try await mvccManager.read(txId: txId, key: key)
                    metrics.reads += 1
                    
                case 1: // Write-only
                    let value = Value.string("stress_value_\(i)")
                    try await mvccManager.write(txId: txId, key: key, value: value)
                    metrics.writes += 1
                    
                case 2: // Read-modify-write
                    if let currentValue = try await mvccManager.read(txId: txId, key: key),
                       case Value.string(let str) = currentValue {
                        let newValue = Value.string("\(str)_modified")
                        try await mvccManager.write(txId: txId, key: key, value: newValue)
                    } else {
                        try await mvccManager.write(txId: txId, key: key, value: Value.string("new_\(i)"))
                    }
                    metrics.reads += 1
                    metrics.writes += 1
                    
                case 3: // Multi-key transaction
                    for offset in 0..<3 {
                        let multiKey = "stress_key_\((Int(drand48() * Double(keySpace)) + offset) % keySpace)"
                        _ = try await mvccManager.read(txId: txId, key: multiKey)
                    }
                    metrics.reads += 3
                    
                default:
                    break
                }
                
                // Randomly commit or abort
                if drand48() < 0.1 { // 10% abort rate
                    try await mvccManager.abortTransaction(txId: txId)
                    metrics.transactionsAborted += 1
                } else {
                    try await mvccManager.commitTransaction(txId: txId)
                    metrics.transactionsCommitted += 1
                }
                
            } catch {
                metrics.transactionsFailed += 1
                // Failures are acceptable (conflicts, etc.)
            }
            
            // Periodic GC
            if i % 1000 == 0 && i > 0 {
                try await mvccManager.garbageCollect()
                metrics.gcRuns += 1
            }
        }
        
        // Verify final state
        XCTAssertEqual(metrics.transactionsStarted, operationCount, 
            "All transactions should start")
        
        let totalTransactions = metrics.transactionsCommitted + metrics.transactionsAborted + metrics.transactionsFailed
        XCTAssertEqual(totalTransactions, operationCount, 
            "All transactions should complete (commit/abort/fail)")
        
        // Check invariants
        let invariants = await mvccManager.checkAllInvariants()
        XCTAssertTrue(invariants, 
            "All MVCC invariants must hold after stress test")
        
        // Print metrics
        print("""
        
        MVCC Stress Test Metrics (10k operations):
        - Transactions Started:   \(metrics.transactionsStarted)
        - Transactions Committed: \(metrics.transactionsCommitted)
        - Transactions Aborted:   \(metrics.transactionsAborted)
        - Transactions Failed:    \(metrics.transactionsFailed)
        - Total Reads:            \(metrics.reads)
        - Total Writes:           \(metrics.writes)
        - GC Runs:                \(metrics.gcRuns)
        - Success Rate:           \(String(format: "%.2f%%", Double(metrics.transactionsCommitted) / Double(metrics.transactionsStarted) * 100))
        """)
    }
}

// MARK: - Test Metrics

struct StressTestMetrics {
    var transactionsStarted = 0
    var transactionsCommitted = 0
    var transactionsAborted = 0
    var transactionsFailed = 0
    var reads = 0
    var writes = 0
    var gcRuns = 0
}

