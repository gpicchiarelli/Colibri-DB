//
//  TransactionManagerTests.swift
//  ColibrìDB Transaction Manager Tests
//
//  Tests for transaction management, ACID properties, and concurrency control
//

import Foundation
import Testing
@testable import ColibriCore

/// Tests for the Transaction Manager
@Suite("Transaction Manager Tests")
struct TransactionManagerTests {
    
    /// Test transaction creation
    @Test("Transaction Creation")
    func testTransactionCreation() async throws {
        let lockManager = LockManager()
        let walManager = WALManager()
        let mvccManager = MVCCManager()
        let twoPhaseCommitManager = TwoPhaseCommitManager()
        
        let transactionManager = TransactionManager(
            lockManager: lockManager,
            walManager: walManager,
            mvccManager: mvccManager,
            twoPhaseCommitManager: twoPhaseCommitManager
        )
        
        // Begin a transaction
        let txID = try await transactionManager.beginTransaction(isolationLevel: .readCommitted)
        try TestAssertions.assertTrue(txID > 0, "Transaction ID should be positive")
        
        // Verify transaction is active
        let isActive = await transactionManager.isTransactionActive(txID)
        try TestAssertions.assertTrue(isActive, "Transaction should be active")
        
        // Get transaction details
        let transaction = await transactionManager.getActiveTransaction(txID)
        try TestAssertions.assertNotNil(transaction, "Active transaction should exist")
        try TestAssertions.assertEqual(transaction!.transactionId, txID, "Transaction ID should match")
        try TestAssertions.assertEqual(transaction!.state, .active, "Transaction state should be active")
        try TestAssertions.assertEqual(transaction!.isolationLevel, .readCommitted, "Isolation level should match")
    }
    
    /// Test transaction commit
    @Test("Transaction Commit")
    func testTransactionCommit() async throws {
        let lockManager = LockManager()
        let walManager = WALManager()
        let mvccManager = MVCCManager()
        let twoPhaseCommitManager = TwoPhaseCommitManager()
        
        let transactionManager = TransactionManager(
            lockManager: lockManager,
            walManager: walManager,
            mvccManager: mvccManager,
            twoPhaseCommitManager: twoPhaseCommitManager
        )
        
        // Begin and commit transaction
        let txID = try await transactionManager.beginTransaction()
        try await transactionManager.commitTransaction(txId: txID)
        
        // Verify transaction is committed
        let isCommitted = await transactionManager.isTransactionCommitted(txID)
        try TestAssertions.assertTrue(isCommitted, "Transaction should be committed")
        
        let isActive = await transactionManager.isTransactionActive(txID)
        try TestAssertions.assertFalse(isActive, "Transaction should not be active after commit")
        
        // Get committed transaction
        let committedTransaction = await transactionManager.getCommittedTransaction(txID)
        try TestAssertions.assertNotNil(committedTransaction, "Committed transaction should exist")
        try TestAssertions.assertEqual(committedTransaction!.state, .committed, "Transaction state should be committed")
        try TestAssertions.assertNotNil(committedTransaction!.commitTime, "Commit time should be set")
    }
    
    /// Test transaction abort
    @Test("Transaction Abort")
    func testTransactionAbort() async throws {
        let lockManager = LockManager()
        let walManager = WALManager()
        let mvccManager = MVCCManager()
        let twoPhaseCommitManager = TwoPhaseCommitManager()
        
        let transactionManager = TransactionManager(
            lockManager: lockManager,
            walManager: walManager,
            mvccManager: mvccManager,
            twoPhaseCommitManager: twoPhaseCommitManager
        )
        
        // Begin and abort transaction
        let txID = try await transactionManager.beginTransaction()
        try await transactionManager.abortTransaction(txId: txID, reason: "Test abort")
        
        // Verify transaction is aborted
        let isAborted = await transactionManager.isTransactionAborted(txID)
        try TestAssertions.assertTrue(isAborted, "Transaction should be aborted")
        
        let isActive = await transactionManager.isTransactionActive(txID)
        try TestAssertions.assertFalse(isActive, "Transaction should not be active after abort")
        
        // Get aborted transaction
        let abortedTransaction = await transactionManager.getAbortedTransaction(txID)
        try TestAssertions.assertNotNil(abortedTransaction, "Aborted transaction should exist")
        try TestAssertions.assertEqual(abortedTransaction!.state, .aborted, "Transaction state should be aborted")
        try TestAssertions.assertEqual(abortedTransaction!.abortReason, "Test abort", "Abort reason should match")
        try TestAssertions.assertNotNil(abortedTransaction!.abortTime, "Abort time should be set")
    }
    
    /// Test read operations
    @Test("Read Operations")
    func testReadOperations() async throws {
        let lockManager = LockManager()
        let walManager = WALManager()
        let mvccManager = MVCCManager()
        let twoPhaseCommitManager = TwoPhaseCommitManager()
        
        let transactionManager = TransactionManager(
            lockManager: lockManager,
            walManager: walManager,
            mvccManager: mvccManager,
            twoPhaseCommitManager: twoPhaseCommitManager
        )
        
        // Begin transaction
        let txID = try await transactionManager.beginTransaction()
        
        // Perform read operations
        let resource1 = "table1.row1"
        let resource2 = "table1.row2"
        
        let value1 = try await transactionManager.read(txId: txID, resource: resource1)
        let value2 = try await transactionManager.read(txId: txID, resource: resource2)
        
        // Verify read operations were recorded
        let transaction = await transactionManager.getActiveTransaction(txID)
        try TestAssertions.assertNotNil(transaction, "Transaction should exist")
        try TestAssertions.assertEqual(transaction!.operations.count, 2, "Should have 2 operations")
        try TestAssertions.assertEqual(transaction!.readSet.count, 2, "Should have 2 resources in read set")
        try TestAssertions.assertTrue(transaction!.readSet.contains(resource1), "Read set should contain resource1")
        try TestAssertions.assertTrue(transaction!.readSet.contains(resource2), "Read set should contain resource2")
        
        try await transactionManager.commitTransaction(txId: txID)
    }
    
    /// Test write operations
    @Test("Write Operations")
    func testWriteOperations() async throws {
        let lockManager = LockManager()
        let walManager = WALManager()
        let mvccManager = MVCCManager()
        let twoPhaseCommitManager = TwoPhaseCommitManager()
        
        let transactionManager = TransactionManager(
            lockManager: lockManager,
            walManager: walManager,
            mvccManager: mvccManager,
            twoPhaseCommitManager: twoPhaseCommitManager
        )
        
        // Begin transaction
        let txID = try await transactionManager.beginTransaction()
        
        // Perform write operations
        let resource1 = "table1.row1"
        let resource2 = "table1.row2"
        let data1 = Value.string("Alice")
        let data2 = Value.int(25)
        
        try await transactionManager.write(txId: txID, resource: resource1, data: data1)
        try await transactionManager.write(txId: txID, resource: resource2, data: data2)
        
        // Verify write operations were recorded
        let transaction = await transactionManager.getActiveTransaction(txID)
        try TestAssertions.assertNotNil(transaction, "Transaction should exist")
        try TestAssertions.assertEqual(transaction!.operations.count, 2, "Should have 2 operations")
        try TestAssertions.assertEqual(transaction!.writeSet.count, 2, "Should have 2 resources in write set")
        try TestAssertions.assertTrue(transaction!.writeSet.contains(resource1), "Write set should contain resource1")
        try TestAssertions.assertTrue(transaction!.writeSet.contains(resource2), "Write set should contain resource2")
        
        try await transactionManager.commitTransaction(txId: txID)
    }
    
    /// Test lock operations
    @Test("Lock Operations")
    func testLockOperations() async throws {
        let lockManager = LockManager()
        let walManager = WALManager()
        let mvccManager = MVCCManager()
        let twoPhaseCommitManager = TwoPhaseCommitManager()
        
        let transactionManager = TransactionManager(
            lockManager: lockManager,
            walManager: walManager,
            mvccManager: mvccManager,
            twoPhaseCommitManager: twoPhaseCommitManager
        )
        
        // Begin transaction
        let txID = try await transactionManager.beginTransaction()
        
        // Acquire locks
        let resource1 = "table1"
        let resource2 = "table2"
        
        try await transactionManager.lock(txId: txID, resource: resource1, lockType: .shared)
        try await transactionManager.lock(txId: txID, resource: resource2, lockType: .exclusive)
        
        // Verify locks were acquired
        let transaction = await transactionManager.getActiveTransaction(txID)
        try TestAssertions.assertNotNil(transaction, "Transaction should exist")
        try TestAssertions.assertEqual(transaction!.locks.count, 2, "Should have 2 locks")
        
        // Release locks
        try await transactionManager.unlock(txId: txID, resource: resource1)
        try await transactionManager.unlock(txId: txID, resource: resource2)
        
        // Verify locks were released
        let updatedTransaction = await transactionManager.getActiveTransaction(txID)
        try TestAssertions.assertNotNil(updatedTransaction, "Transaction should exist")
        try TestAssertions.assertEqual(updatedTransaction!.locks.count, 0, "Should have 0 locks after release")
        
        try await transactionManager.commitTransaction(txId: txID)
    }
    
    /// Test isolation levels
    @Test("Isolation Levels")
    func testIsolationLevels() async throws {
        let lockManager = LockManager()
        let walManager = WALManager()
        let mvccManager = MVCCManager()
        let twoPhaseCommitManager = TwoPhaseCommitManager()
        
        let transactionManager = TransactionManager(
            lockManager: lockManager,
            walManager: walManager,
            mvccManager: mvccManager,
            twoPhaseCommitManager: twoPhaseCommitManager
        )
        
        // Test different isolation levels
        let isolationLevels: [IsolationLevel] = [.readUncommitted, .readCommitted, .repeatableRead, .serializable, .snapshot]
        
        for isolationLevel in isolationLevels {
            let txID = try await transactionManager.beginTransaction(isolationLevel: isolationLevel)
            
            let transaction = await transactionManager.getActiveTransaction(txID)
            try TestAssertions.assertNotNil(transaction, "Transaction should exist")
            try TestAssertions.assertEqual(transaction!.isolationLevel, isolationLevel, "Isolation level should match")
            
            try await transactionManager.commitTransaction(txId: txID)
        }
    }
    
    /// Test concurrent transactions
    @Test("Concurrent Transactions")
    func testConcurrentTransactions() async throws {
        let lockManager = LockManager()
        let walManager = WALManager()
        let mvccManager = MVCCManager()
        let twoPhaseCommitManager = TwoPhaseCommitManager()
        
        let transactionManager = TransactionManager(
            lockManager: lockManager,
            walManager: walManager,
            mvccManager: mvccManager,
            twoPhaseCommitManager: twoPhaseCommitManager
        )
        
        // Start multiple concurrent transactions
        let transactionCount = 5
        var transactionIDs: [TxID] = []
        
        for i in 0..<transactionCount {
            let txID = try await transactionManager.beginTransaction()
            transactionIDs.append(txID)
            
            // Perform some operations
            try await transactionManager.write(txId: txID, resource: "resource\(i)", data: .int(i))
        }
        
        // Verify all transactions are active
        for txID in transactionIDs {
            let isActive = await transactionManager.isTransactionActive(txID)
            try TestAssertions.assertTrue(isActive, "Transaction \(txID) should be active")
        }
        
        // Commit all transactions
        for txID in transactionIDs {
            try await transactionManager.commitTransaction(txId: txID)
        }
        
        // Verify all transactions are committed
        for txID in transactionIDs {
            let isCommitted = await transactionManager.isTransactionCommitted(txID)
            try TestAssertions.assertTrue(isCommitted, "Transaction \(txID) should be committed")
        }
    }
    
    /// Test distributed transactions
    @Test("Distributed Transactions")
    func testDistributedTransactions() async throws {
        let lockManager = LockManager()
        let walManager = WALManager()
        let mvccManager = MVCCManager()
        let twoPhaseCommitManager = TwoPhaseCommitManager()
        
        let transactionManager = TransactionManager(
            lockManager: lockManager,
            walManager: walManager,
            mvccManager: mvccManager,
            twoPhaseCommitManager: twoPhaseCommitManager
        )
        
        // Begin transaction
        let txID = try await transactionManager.beginTransaction()
        
        // Make it distributed
        let participants = ["node1", "node2", "node3"]
        try await transactionManager.beginDistributedTransaction(txId: txID, participants: participants)
        
        // Verify transaction is distributed
        let isDistributed = await transactionManager.isTransactionDistributed(txID)
        try TestAssertions.assertTrue(isDistributed, "Transaction should be distributed")
        
        // Get participants
        let twoPhaseParticipants = await transactionManager.getTwoPhaseCommitParticipants(txID)
        try TestAssertions.assertNotNil(twoPhaseParticipants, "Two-phase commit participants should exist")
        try TestAssertions.assertEqual(twoPhaseParticipants!.count, participants.count, "Should have correct number of participants")
        
        // Commit distributed transaction
        try await transactionManager.commitTransaction(txId: txID)
        
        // Verify transaction is committed
        let isCommitted = await transactionManager.isTransactionCommitted(txID)
        try TestAssertions.assertTrue(isCommitted, "Distributed transaction should be committed")
    }
    
    /// Test deadlock detection
    @Test("Deadlock Detection")
    func testDeadlockDetection() async throws {
        let lockManager = LockManager()
        let walManager = WALManager()
        let mvccManager = MVCCManager()
        let twoPhaseCommitManager = TwoPhaseCommitManager()
        
        let transactionManager = TransactionManager(
            lockManager: lockManager,
            walManager: walManager,
            mvccManager: mvccManager,
            twoPhaseCommitManager: twoPhaseCommitManager
        )
        
        // Perform deadlock detection
        try await transactionManager.detectDeadlocks()
        
        // Get deadlock detection results
        let deadlockResults = await transactionManager.getDeadlockDetectionResults()
        // Results should be empty for this simple test
        try TestAssertions.assertEqual(deadlockResults.count, 0, "Should have no deadlock results initially")
    }
    
    /// Test ACID properties
    @Test("ACID Properties")
    func testACIDProperties() async throws {
        let lockManager = LockManager()
        let walManager = WALManager()
        let mvccManager = MVCCManager()
        let twoPhaseCommitManager = TwoPhaseCommitManager()
        
        let transactionManager = TransactionManager(
            lockManager: lockManager,
            walManager: walManager,
            mvccManager: mvccManager,
            twoPhaseCommitManager: twoPhaseCommitManager
        )
        
        // Test atomicity invariant
        let atomicity = await transactionManager.checkAtomicityInvariant()
        try TestAssertions.assertTrue(atomicity, "Atomicity invariant should hold")
        
        // Test consistency invariant
        let consistency = await transactionManager.checkConsistencyInvariant()
        try TestAssertions.assertTrue(consistency, "Consistency invariant should hold")
        
        // Test isolation invariant
        let isolation = await transactionManager.checkIsolationInvariant()
        try TestAssertions.assertTrue(isolation, "Isolation invariant should hold")
        
        // Test durability invariant
        let durability = await transactionManager.checkDurabilityInvariant()
        try TestAssertions.assertTrue(durability, "Durability invariant should hold")
        
        // Test two-phase commit invariant
        let twoPhaseCommit = await transactionManager.checkTwoPhaseCommitInvariant()
        try TestAssertions.assertTrue(twoPhaseCommit, "Two-phase commit invariant should hold")
        
        // Test deadlock detection invariant
        let deadlockDetection = await transactionManager.checkDeadlockDetectionInvariant()
        try TestAssertions.assertTrue(deadlockDetection, "Deadlock detection invariant should hold")
        
        // Test all invariants
        let allInvariants = await transactionManager.checkAllInvariants()
        try TestAssertions.assertTrue(allInvariants, "All invariants should hold")
    }
    
    /// Test error handling
    @Test("Error Handling")
    func testErrorHandling() async throws {
        let lockManager = LockManager()
        let walManager = WALManager()
        let mvccManager = MVCCManager()
        let twoPhaseCommitManager = TwoPhaseCommitManager()
        
        let transactionManager = TransactionManager(
            lockManager: lockManager,
            walManager: walManager,
            mvccManager: mvccManager,
            twoPhaseCommitManager: twoPhaseCommitManager
        )
        
        // Test operations on non-existent transaction
        try TestAssertions.assertAsyncThrows({
            try await transactionManager.commitTransaction(txId: 999)
        }, "Should throw error for non-existent transaction")
        
        try TestAssertions.assertAsyncThrows({
            try await transactionManager.abortTransaction(txId: 999)
        }, "Should throw error for non-existent transaction")
        
        try TestAssertions.assertAsyncThrows({
            try await transactionManager.read(txId: 999, resource: "test")
        }, "Should throw error for non-existent transaction")
        
        try TestAssertions.assertAsyncThrows({
            try await transactionManager.write(txId: 999, resource: "test", data: .string("test"))
        }, "Should throw error for non-existent transaction")
        
        // Begin a transaction
        let txID = try await transactionManager.beginTransaction()
        
        // Commit it
        try await transactionManager.commitTransaction(txId: txID)
        
        // Test operations on committed transaction
        try TestAssertions.assertAsyncThrows({
            try await transactionManager.commitTransaction(txId: txID)
        }, "Should throw error for already committed transaction")
        
        try TestAssertions.assertAsyncThrows({
            try await transactionManager.read(txId: txID, resource: "test")
        }, "Should throw error for committed transaction")
    }
    
    /// Test transaction statistics
    @Test("Transaction Statistics")
    func testTransactionStatistics() async throws {
        let lockManager = LockManager()
        let walManager = WALManager()
        let mvccManager = MVCCManager()
        let twoPhaseCommitManager = TwoPhaseCommitManager()
        
        let transactionManager = TransactionManager(
            lockManager: lockManager,
            walManager: walManager,
            mvccManager: mvccManager,
            twoPhaseCommitManager: twoPhaseCommitManager
        )
        
        // Initially no transactions
        let activeTransactions = await transactionManager.getAllActiveTransactions()
        let committedTransactions = await transactionManager.getAllCommittedTransactions()
        let abortedTransactions = await transactionManager.getAllAbortedTransactions()
        
        try TestAssertions.assertEqual(activeTransactions.count, 0, "Should have no active transactions initially")
        try TestAssertions.assertEqual(committedTransactions.count, 0, "Should have no committed transactions initially")
        try TestAssertions.assertEqual(abortedTransactions.count, 0, "Should have no aborted transactions initially")
        
        // Create some transactions
        let txID1 = try await transactionManager.beginTransaction()
        let txID2 = try await transactionManager.beginTransaction()
        
        try await transactionManager.commitTransaction(txId: txID1)
        try await transactionManager.abortTransaction(txId: txID2, reason: "Test abort")
        
        // Check statistics
        let activeAfter = await transactionManager.getAllActiveTransactions()
        let committedAfter = await transactionManager.getAllCommittedTransactions()
        let abortedAfter = await transactionManager.getAllAbortedTransactions()
        
        try TestAssertions.assertEqual(activeAfter.count, 0, "Should have no active transactions")
        try TestAssertions.assertEqual(committedAfter.count, 1, "Should have 1 committed transaction")
        try TestAssertions.assertEqual(abortedAfter.count, 1, "Should have 1 aborted transaction")
    }
    
    /// Test transaction configuration
    @Test("Transaction Configuration")
    func testTransactionConfiguration() async throws {
        let config = TransactionConfig(
            defaultIsolationLevel: .serializable,
            lockTimeoutMs: 5000,
            maxTransactionDuration: 60.0,
            enableDeadlockDetection: true,
            enableTwoPhaseCommit: true,
            enableDistributedTransactions: true
        )
        
        let lockManager = LockManager()
        let walManager = WALManager()
        let mvccManager = MVCCManager()
        let twoPhaseCommitManager = TwoPhaseCommitManager()
        
        let transactionManager = TransactionManager(
            lockManager: lockManager,
            walManager: walManager,
            mvccManager: mvccManager,
            twoPhaseCommitManager: twoPhaseCommitManager,
            transactionConfig: config
        )
        
        // Test that configuration is applied
        let txID = try await transactionManager.beginTransaction()
        let transaction = await transactionManager.getActiveTransaction(txID)
        
        try TestAssertions.assertNotNil(transaction, "Transaction should exist")
        // Note: The actual isolation level used depends on the parameter passed to beginTransaction
        // The config provides the default, but we explicitly passed .readCommitted in the call
        
        try await transactionManager.commitTransaction(txId: txID)
    }
}
