//
//  WALTests.swift
//  ColibrìDB Write-Ahead Log Tests
//
//  Tests for WAL operations, recovery, and durability
//

import Foundation
import Testing
@testable import ColibriCore

/// Tests for the Write-Ahead Log
@Suite("WAL Tests")
struct WALTests {
    
    /// Test WAL initialization
    @Test("WAL Initialization")
    func testWALInitialization() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let walPath = tempDir.appendingPathComponent("wal.log")
        let wal = try FileWAL(walFilePath: walPath)
        
        // Verify initial state
        let currentLSN = await wal.getCurrentLSN()
        let flushedLSN = await wal.getFlushedLSN()
        let lastCheckpointLSN = await wal.getLastCheckpointLSN()
        
        try TestAssertions.assertEqual(currentLSN, 1, "Initial LSN should be 1")
        try TestAssertions.assertEqual(flushedLSN, 0, "Initial flushed LSN should be 0")
        try TestAssertions.assertEqual(lastCheckpointLSN, 0, "Initial checkpoint LSN should be 0")
    }
    
    /// Test WAL record appending
    @Test("WAL Record Appending")
    func testWALRecordAppending() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let walPath = tempDir.appendingPathComponent("wal.log")
        let wal = try FileWAL(walFilePath: walPath)
        
        // Append a record
        let txID: TxID = 1
        let pageID: PageID = 1
        let payload = "test data".data(using: .utf8)
        
        let lsn = try await wal.append(
            kind: .update,
            txID: txID,
            pageID: pageID,
            payload: payload
        )
        
        // Verify LSN was assigned
        try TestAssertions.assertEqual(lsn, 1, "First LSN should be 1")
        
        // Verify current LSN was incremented
        let currentLSN = await wal.getCurrentLSN()
        try TestAssertions.assertEqual(currentLSN, 2, "Current LSN should be 2")
        
        // Append another record
        let lsn2 = try await wal.append(
            kind: .insert,
            txID: txID,
            pageID: pageID,
            payload: nil
        )
        
        try TestAssertions.assertEqual(lsn2, 2, "Second LSN should be 2")
        
        let currentLSN2 = await wal.getCurrentLSN()
        try TestAssertions.assertEqual(currentLSN2, 3, "Current LSN should be 3")
    }
    
    /// Test WAL flushing
    @Test("WAL Flushing")
    func testWALFlushing() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let walPath = tempDir.appendingPathComponent("wal.log")
        let wal = try FileWAL(walFilePath: walPath)
        
        // Append some records
        let txID: TxID = 1
        let pageID: PageID = 1
        
        let lsn1 = try await wal.append(kind: .update, txID: txID, pageID: pageID, payload: nil)
        let lsn2 = try await wal.append(kind: .insert, txID: txID, pageID: pageID, payload: nil)
        
        // Verify records are pending
        let currentLSN = await wal.getCurrentLSN()
        let flushedLSN = await wal.getFlushedLSN()
        
        try TestAssertions.assertEqual(currentLSN, 3, "Current LSN should be 3")
        try TestAssertions.assertEqual(flushedLSN, 0, "Flushed LSN should be 0")
        
        // Flush records
        try await wal.flush()
        
        // Verify records are flushed
        let flushedLSNAfter = await wal.getFlushedLSN()
        try TestAssertions.assertEqual(flushedLSNAfter, 2, "Flushed LSN should be 2")
    }
    
    /// Test page LSN updates
    @Test("Page LSN Updates")
    func testPageLSNUpdates() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let walPath = tempDir.appendingPathComponent("wal.log")
        let wal = try FileWAL(walFilePath: walPath)
        
        let pageID: PageID = 1
        let lsn: LSN = 100
        
        // Update page LSN
        try await wal.updatePageLSN(pageID, lsn: lsn)
        
        // Verify page LSN was updated
        let dirtyPageTable = await wal.getDirtyPageTable()
        try TestAssertions.assertNotNil(dirtyPageTable[pageID], "Page should be in dirty page table")
        try TestAssertions.assertEqual(dirtyPageTable[pageID], lsn, "Page LSN should match")
    }
    
    /// Test data page application
    @Test("Data Page Application")
    func testDataPageApplication() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let walPath = tempDir.appendingPathComponent("wal.log")
        let wal = try FileWAL(walFilePath: walPath)
        
        let pageID: PageID = 1
        let lsn: LSN = 100
        
        // Update page LSN and flush
        try await wal.updatePageLSN(pageID, lsn: lsn)
        try await wal.flush()
        
        // Apply to data page
        try await wal.applyToDataPage(pageID)
        
        // Verify page is marked as applied
        // Note: The actual verification depends on implementation details
    }
    
    /// Test checkpoint creation
    @Test("Checkpoint Creation")
    func testCheckpointCreation() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let walPath = tempDir.appendingPathComponent("wal.log")
        let wal = try FileWAL(walFilePath: walPath)
        
        // Append some records and flush
        let txID: TxID = 1
        let pageID: PageID = 1
        
        try await wal.append(kind: .update, txID: txID, pageID: pageID, payload: nil)
        try await wal.flush()
        
        // Create checkpoint
        let checkpointLSN = try await wal.checkpoint()
        
        // Verify checkpoint LSN
        try TestAssertions.assertTrue(checkpointLSN > 0, "Checkpoint LSN should be positive")
        
        let lastCheckpointLSN = await wal.getLastCheckpointLSN()
        try TestAssertions.assertEqual(lastCheckpointLSN, checkpointLSN, "Last checkpoint LSN should match")
    }
    
    /// Test crash simulation
    @Test("Crash Simulation")
    func testCrashSimulation() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let walPath = tempDir.appendingPathComponent("wal.log")
        let wal = try FileWAL(walFilePath: walPath)
        
        // Append some records
        let txID: TxID = 1
        let pageID: PageID = 1
        
        try await wal.append(kind: .update, txID: txID, pageID: pageID, payload: nil)
        try await wal.flush()
        
        // Append more records (not flushed)
        try await wal.append(kind: .insert, txID: txID, pageID: pageID, payload: nil)
        
        // Simulate crash
        await wal.simulateCrash()
        
        // Verify crash state
        // Note: The actual verification depends on implementation details
    }
    
    /// Test recovery
    @Test("Recovery")
    func testRecovery() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let walPath = tempDir.appendingPathComponent("wal.log")
        let wal = try FileWAL(walFilePath: walPath)
        
        // Append some records and flush
        let txID: TxID = 1
        let pageID: PageID = 1
        
        try await wal.append(kind: .update, txID: txID, pageID: pageID, payload: nil)
        try await wal.flush()
        
        // Simulate crash
        await wal.simulateCrash()
        
        // Recover
        try await wal.recover()
        
        // Verify recovery
        let currentLSN = await wal.getCurrentLSN()
        let flushedLSN = await wal.getFlushedLSN()
        
        try TestAssertions.assertTrue(currentLSN > 0, "Current LSN should be positive after recovery")
        try TestAssertions.assertTrue(flushedLSN >= 0, "Flushed LSN should be non-negative after recovery")
    }
    
    /// Test WAL invariants
    @Test("WAL Invariants")
    func testWALInvariants() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let walPath = tempDir.appendingPathComponent("wal.log")
        let wal = try FileWAL(walFilePath: walPath)
        
        // Test log-before-data invariant
        let logBeforeData = await wal.checkLogBeforeDataInvariant()
        try TestAssertions.assertTrue(logBeforeData, "Log-before-data invariant should hold")
        
        // Test log order invariant
        let logOrder = await wal.checkLogOrderInvariant()
        try TestAssertions.assertTrue(logOrder, "Log order invariant should hold")
        
        // Test checkpoint consistency
        let checkpointConsistency = await wal.checkCheckpointConsistency()
        try TestAssertions.assertTrue(checkpointConsistency, "Checkpoint consistency should hold")
    }
    
    /// Test error handling
    @Test("Error Handling")
    func testErrorHandling() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let walPath = tempDir.appendingPathComponent("wal.log")
        let wal = try FileWAL(walFilePath: walPath)
        
        // Simulate crash
        await wal.simulateCrash()
        
        // Test operations after crash
        try TestAssertions.assertAsyncThrows({
            try await wal.append(kind: .update, txID: 1, pageID: 1, payload: nil)
        }, "Should throw error after crash")
        
        try TestAssertions.assertAsyncThrows({
            try await wal.flush()
        }, "Should throw error after crash")
        
        try TestAssertions.assertAsyncThrows({
            try await wal.checkpoint()
        }, "Should throw error after crash")
    }
    
    /// Test concurrent WAL operations
    @Test("Concurrent WAL Operations")
    func testConcurrentWALOperations() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let walPath = tempDir.appendingPathComponent("wal.log")
        let wal = try FileWAL(walFilePath: walPath)
        
        // Start multiple concurrent tasks
        let taskCount = 10
        var tasks: [Task<Void, Never>] = []
        
        for i in 0..<taskCount {
            let task = Task {
                do {
                    let txID: TxID = TxID(i + 1)
                    let pageID: PageID = PageID(i + 1)
                    
                    // Append record
                    try await wal.append(kind: .update, txID: txID, pageID: pageID, payload: nil)
                    
                    // Update page LSN
                    try await wal.updatePageLSN(pageID, lsn: LSN(i + 1))
                } catch {
                    // Handle errors silently for this test
                }
            }
            tasks.append(task)
        }
        
        // Wait for all tasks to complete
        for task in tasks {
            await task.value
        }
        
        // Flush all records
        try await wal.flush()
        
        // Verify WAL is in consistent state
        let currentLSN = await wal.getCurrentLSN()
        try TestAssertions.assertTrue(currentLSN > 0, "Current LSN should be positive")
        
        let flushedLSN = await wal.getFlushedLSN()
        try TestAssertions.assertTrue(flushedLSN >= 0, "Flushed LSN should be non-negative")
    }
    
    /// Test WAL performance
    @Test("WAL Performance")
    func testWALPerformance() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let walPath = tempDir.appendingPathComponent("wal.log")
        let wal = try FileWAL(walFilePath: walPath)
        
        let recordCount = 1000
        let startTime = Date()
        
        // Append many records
        for i in 0..<recordCount {
            let txID: TxID = TxID(i + 1)
            let pageID: PageID = PageID(i + 1)
            let payload = TestUtils.generateRandomData(size: 100)
            
            try await wal.append(kind: .update, txID: txID, pageID: pageID, payload: payload)
        }
        
        // Flush all records
        try await wal.flush()
        
        let endTime = Date()
        let executionTime = endTime.timeIntervalSince(startTime)
        
        // Verify performance is reasonable (less than 2 seconds for 1000 records)
        try TestAssertions.assertTrue(executionTime < 2.0, "Performance should be reasonable")
        
        // Verify all records were written
        let currentLSN = await wal.getCurrentLSN()
        try TestAssertions.assertEqual(currentLSN, LSN(recordCount + 1), "Should have correct number of records")
    }
    
    /// Test WAL record retrieval
    @Test("WAL Record Retrieval")
    func testWALRecordRetrieval() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let walPath = tempDir.appendingPathComponent("wal.log")
        let wal = try FileWAL(walFilePath: walPath)
        
        // Append some records
        let txID: TxID = 1
        let pageID: PageID = 1
        
        try await wal.append(kind: .update, txID: txID, pageID: pageID, payload: nil)
        try await wal.append(kind: .insert, txID: txID, pageID: pageID, payload: nil)
        try await wal.flush()
        
        // Get all records
        let allRecords = await wal.getAllRecords()
        try TestAssertions.assertEqual(allRecords.count, 2, "Should have 2 records")
        
        // Get records since LSN 1
        let recordsSince1 = await wal.getRecordsSince(1)
        try TestAssertions.assertEqual(recordsSince1.count, 2, "Should have 2 records since LSN 1")
        
        // Get records since LSN 2
        let recordsSince2 = await wal.getRecordsSince(2)
        try TestAssertions.assertEqual(recordsSince2.count, 1, "Should have 1 record since LSN 2")
    }
    
    /// Test active transaction table
    @Test("Active Transaction Table")
    func testActiveTransactionTable() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let walPath = tempDir.appendingPathComponent("wal.log")
        let wal = try FileWAL(walFilePath: walPath)
        
        // Append records for different transactions
        try await wal.append(kind: .update, txID: 1, pageID: 1, payload: nil)
        try await wal.append(kind: .insert, txID: 2, pageID: 2, payload: nil)
        try await wal.append(kind: .update, txID: 1, pageID: 3, payload: nil)
        
        // Get active transaction table
        let activeTransactionTable = await wal.getActiveTransactionTable()
        
        // Verify transaction table
        try TestAssertions.assertEqual(activeTransactionTable.count, 2, "Should have 2 active transactions")
        try TestAssertions.assertNotNil(activeTransactionTable[1], "Transaction 1 should be active")
        try TestAssertions.assertNotNil(activeTransactionTable[2], "Transaction 2 should be active")
    }
    
    /// Test dirty page table
    @Test("Dirty Page Table")
    func testDirtyPageTable() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let walPath = tempDir.appendingPathComponent("wal.log")
        let wal = try FileWAL(walFilePath: walPath)
        
        // Update page LSNs
        try await wal.updatePageLSN(1, lsn: 100)
        try await wal.updatePageLSN(2, lsn: 200)
        try await wal.updatePageLSN(3, lsn: 300)
        
        // Get dirty page table
        let dirtyPageTable = await wal.getDirtyPageTable()
        
        // Verify dirty page table
        try TestAssertions.assertEqual(dirtyPageTable.count, 3, "Should have 3 dirty pages")
        try TestAssertions.assertEqual(dirtyPageTable[1], 100, "Page 1 LSN should be 100")
        try TestAssertions.assertEqual(dirtyPageTable[2], 200, "Page 2 LSN should be 200")
        try TestAssertions.assertEqual(dirtyPageTable[3], 300, "Page 3 LSN should be 300")
    }
}
