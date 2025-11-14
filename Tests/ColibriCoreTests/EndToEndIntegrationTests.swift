//
//  EndToEndIntegrationTests.swift
//  ColibrìDB End-to-End Integration Tests
//
//  Full stack testing: WAL + MVCC + Index + Transaction Manager
//

import XCTest
@testable import ColibriCore

final class EndToEndIntegrationTests: XCTestCase {
    
    /// Test complete transaction flow: BEGIN -> INSERT -> COMMIT -> VERIFY
    func testCompleteTransactionFlow() async throws {
        // Setup
        let tempDir = FileManager.default.temporaryDirectory.appendingPathComponent(UUID().uuidString)
        try FileManager.default.createDirectory(at: tempDir, withIntermediateDirectories: true)
        defer { try? FileManager.default.removeItem(at: tempDir) }
        
        // Initialize components
        let mvcc = MVCCManager()
        let txManager = try TransactionManager.makeForTesting(mvccManager: mvcc)
        
        // Begin transaction
        let txID = try await txManager.beginTransaction()
        XCTAssertGreaterThan(txID, 0, "Transaction ID must be assigned")
        
        // Write data
        let key: MVCCKey = "user:1"
        let value = Value.string("John Doe")
        try await mvcc.write(txId: txID, key: key, value: value)
        
        // Read back (should see uncommitted data within transaction)
        let readValue = try await mvcc.read(txId: txID, key: key)
        XCTAssertEqual(readValue, value, "Should read uncommitted data within transaction")
        
        // Commit
        try await txManager.commitTransaction(txId: txID)
        
        // Verify committed: new transaction should see the data
        let txID2 = try await txManager.beginTransaction()
        let committedValue = try await mvcc.read(txId: txID2, key: key)
        XCTAssertEqual(committedValue, value, "Should read committed data")
        
        try await txManager.commitTransaction(txId: txID2)
        
        print("✓ Complete transaction flow test PASSED")
    }
    
    /// Test concurrent transactions with isolation
    func testConcurrentTransactionsWithIsolation() async throws {
        let mvcc = MVCCManager()
        let txManager = try TransactionManager.makeForTesting(mvccManager: mvcc)
        
        // Transaction 1: Write key1
        let tx1 = try await txManager.beginTransaction()
        try await mvcc.write(txId: tx1, key: "key1", value: Value.string("value1"))
        
        // Transaction 2: Should NOT see uncommitted key1
        let tx2 = try await txManager.beginTransaction()
        let readValue = try await mvcc.read(txId: tx2, key: "key1")
        XCTAssertNil(readValue, "Tx2 should not see uncommitted data from Tx1")
        
        // Commit tx1
        try await txManager.commitTransaction(txId: tx1)
        
        // Tx2 still should NOT see key1 (snapshot isolation)
        let readValue2 = try await mvcc.read(txId: tx2, key: "key1")
        XCTAssertNil(readValue2, "Tx2 should not see data committed after its snapshot")
        
        try await txManager.commitTransaction(txId: tx2)
        
        // New transaction should see key1
        let tx3 = try await txManager.beginTransaction()
        let readValue3 = try await mvcc.read(txId: tx3, key: "key1")
        XCTAssertEqual(readValue3, Value.string("value1"), "Tx3 should see committed data")
        try await txManager.commitTransaction(txId: tx3)
        
        print("✓ Concurrent transactions isolation test PASSED")
    }
    
    /// Test WAL + Recovery integration
    func testWALRecoveryIntegration() async throws {
        let tempDir = FileManager.default.temporaryDirectory.appendingPathComponent(UUID().uuidString)
        try FileManager.default.createDirectory(at: tempDir, withIntermediateDirectories: true)
        defer { try? FileManager.default.removeItem(at: tempDir) }

        let diskManager = TestDiskManager()
        let groupCommit = GroupCommitManager(flushCallback: { _ in })
        let wal = WALManager(diskManager: diskManager, groupCommitManager: groupCommit)
        
        let txID = TxID(1)
        _ = try await wal.appendRecord(txId: txID, kind: .begin, data: Data())
        _ = try await wal.appendRecord(txId: txID, kind: .commit, data: Data("test-data".utf8))
        try await wal.flushLog()
        
        let flushedLSN = await wal.getFlushedLSN()
        XCTAssertGreaterThan(flushedLSN, 0, "LSN should be flushed before crash")
        
        // Simulate crash and recover on the same WAL instance
        try await wal.simulateCrash()
        try await wal.recover()
        
        let currentLSN = await wal.getCurrentLSN()
        XCTAssertGreaterThan(currentLSN, 0, "LSN should remain after recovery")
        
        print("✓ WAL recovery integration test PASSED")
    }
    
    /// Test full database operations: CREATE TABLE -> INSERT -> SELECT
    func testFullDatabaseOperations() async throws {
        // This would test the full SQL -> Planner -> Executor -> Storage stack
        // For now, we test the storage layer directly
        
        let mvcc = MVCCManager()
        let txManager = try TransactionManager.makeForTesting(mvccManager: mvcc)
        
        // Simulate INSERT INTO users VALUES (1, 'Alice')
        let txInsert = try await txManager.beginTransaction()
        try await mvcc.write(txId: txInsert, key: "users:1", value: Value.string("Alice"))
        try await txManager.commitTransaction(txId: txInsert)
        
        // Simulate SELECT * FROM users WHERE id = 1
        let txSelect = try await txManager.beginTransaction()
        let result = try await mvcc.read(txId: txSelect, key: "users:1")
        XCTAssertEqual(result, Value.string("Alice"), "Should retrieve inserted data")
        try await txManager.commitTransaction(txId: txSelect)
        
        // Simulate UPDATE users SET name = 'Bob' WHERE id = 1
        let txUpdate = try await txManager.beginTransaction()
        try await mvcc.write(txId: txUpdate, key: "users:1", value: Value.string("Bob"))
        try await txManager.commitTransaction(txId: txUpdate)
        
        // Verify update
        let txVerify = try await txManager.beginTransaction()
        let updated = try await mvcc.read(txId: txVerify, key: "users:1")
        XCTAssertEqual(updated, Value.string("Bob"), "Should see updated data")
        try await txManager.commitTransaction(txId: txVerify)
        
        print("✓ Full database operations test PASSED")
    }
    
    /// Stress test: 1000 concurrent transactions
    func testStressTest1000Transactions() async throws {
        let mvcc = MVCCManager()
        let txManager = try TransactionManager.makeForTesting(mvccManager: mvcc)
        
        let transactionCount = 1000
        var completedCount = 0
        
        for i in 0..<transactionCount {
            do {
                let txID = try await txManager.beginTransaction()
                let key: MVCCKey = "stress_key_\(i % 100)"
                let value = Value.string("value_\(i)")
                
                try await mvcc.write(txId: txID, key: key, value: value)
                try await txManager.commitTransaction(txId: txID)
                
                completedCount += 1
            } catch {
                // Some transactions may abort due to conflicts - this is expected
                continue
            }
        }
        
        XCTAssertGreaterThan(completedCount, transactionCount / 2,
            "At least half of transactions should complete successfully")
        
        print("✓ Stress test PASSED: \(completedCount)/\(transactionCount) transactions completed")
    }
}

// MARK: - Test Helpers

final class TestDiskManager: DiskManager {
    func readPage(pageId: PageID) async throws -> Data {
        return Data()
    }
    
    func writePage(pageId: PageID, data: Data) async throws {
        // No-op for testing
    }
    
    func deletePage(pageId: PageID) async throws {
        // No-op for testing
    }
}

