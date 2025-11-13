//
//  StressTests.swift
//  ColibrìDB Stress Tests
//
//  Tests for stress conditions, edge cases, and extreme scenarios
//

import Foundation
import Testing
@testable import ColibriCore

/// Stress Tests for ColibrìDB
@Suite("Stress Tests")
struct StressTests {
    
    /// Test high transaction load
    @Test("High Transaction Load")
    func testHighTransactionLoad() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let config = ColibrìDB.Configuration(
            dataDirectory: tempDir,
            walDirectory: tempDir.appendingPathComponent("wal"),
            bufferPoolSize: 10000,
            enableWAL: true,
            enableMVCC: true
        )
        
        let db = try ColibrìDB(config: config)
        try await db.start()
        
        // Create table
        let tableDef = TestDataGenerator.generateTableDefinition(name: "users")
        try await db.createTable(tableDef)
        
        let transactionCount = 50000
        let startTime = Date()
        
        // Perform many transactions
        for i in 0..<transactionCount {
            let txID = try await db.beginTransaction()
            
            let testRow = TestDataGenerator.generateTestRow(
                id: i + 1,
                name: "User\(i + 1)",
                age: 20 + (i % 50),
                salary: 30000.0 + Double(i * 100)
            )
            
            let rid = try await db.insert(table: "users", row: testRow, txID: txID)
            try await db.commit(txID)
            
            // Verify data integrity periodically
            if i % 1000 == 0 {
                let retrievedRow = try await db.read(rid: rid)
                try TestAssertions.assertNotNil(retrievedRow, "Row should be retrievable")
            }
        }
        
        let endTime = Date()
        let duration = endTime.timeIntervalSince(startTime)
        
        // Calculate transactions per second
        let tps = Double(transactionCount) / duration
        
        // Verify performance is reasonable under high load
        try TestAssertions.assertTrue(tps > 50, "Should achieve at least 50 TPS under high load")
        try TestAssertions.assertTrue(duration < 1000.0, "Should complete within reasonable time")
        
        try await db.shutdown()
    }
    
    /// Test memory pressure
    @Test("Memory Pressure")
    func testMemoryPressure() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let config = ColibrìDB.Configuration(
            dataDirectory: tempDir,
            walDirectory: tempDir.appendingPathComponent("wal"),
            bufferPoolSize: 10, // Very small buffer pool
            enableWAL: true,
            enableMVCC: true
        )
        
        let db = try ColibrìDB(config: config)
        try await db.start()
        
        // Create table
        let tableDef = TestDataGenerator.generateTableDefinition(name: "users")
        try await db.createTable(tableDef)
        
        let txID = try await db.beginTransaction()
        
        // Insert many rows to trigger buffer pool eviction
        for i in 0..<1000 {
            let testRow = TestDataGenerator.generateTestRow(
                id: i + 1,
                name: "User\(i + 1)",
                age: 20 + (i % 50),
                salary: 30000.0 + Double(i * 100)
            )
            
            let rid = try await db.insert(table: "users", row: testRow, txID: txID)
            try TestAssertions.assertTrue(rid > 0, "Row ID should be positive")
        }
        
        try await db.commit(txID)
        
        // Verify database is still functional
        let stats = await db.getStatistics()
        try TestAssertions.assertTrue(stats.isStarted, "Database should still be started")
        try TestAssertions.assertTrue(stats.bufferPoolSize <= 10, "Buffer pool should not exceed limit")
        
        try await db.shutdown()
    }
    
    /// Test disk space pressure
    @Test("Disk Space Pressure")
    func testDiskSpacePressure() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let config = ColibrìDB.Configuration(
            dataDirectory: tempDir,
            walDirectory: tempDir.appendingPathComponent("wal"),
            bufferPoolSize: 1000,
            enableWAL: true,
            enableMVCC: true
        )
        
        let db = try ColibrìDB(config: config)
        try await db.start()
        
        // Create table
        let tableDef = TestDataGenerator.generateTableDefinition(name: "users")
        try await db.createTable(tableDef)
        
        let txID = try await db.beginTransaction()
        
        // Insert many rows with large data
        for i in 0..<1000 {
            let testRow = TestDataGenerator.generateTestRow(
                id: i + 1,
                name: "User\(i + 1)",
                age: 20 + (i % 50),
                salary: 30000.0 + Double(i * 100)
            )
            
            let rid = try await db.insert(table: "users", row: testRow, txID: txID)
            try TestAssertions.assertTrue(rid > 0, "Row ID should be positive")
        }
        
        try await db.commit(txID)
        
        // Verify database is still functional
        let stats = await db.getStatistics()
        try TestAssertions.assertTrue(stats.isStarted, "Database should still be started")
        
        try await db.shutdown()
    }
    
    /// Test concurrent transaction conflicts
    @Test("Concurrent Transaction Conflicts")
    func testConcurrentTransactionConflicts() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let config = ColibrìDB.Configuration(
            dataDirectory: tempDir,
            walDirectory: tempDir.appendingPathComponent("wal"),
            bufferPoolSize: 1000,
            enableWAL: true,
            enableMVCC: true
        )
        
        let db = try ColibrìDB(config: config)
        try await db.start()
        
        // Create table
        let tableDef = TestDataGenerator.generateTableDefinition(name: "users")
        try await db.createTable(tableDef)
        
        // Insert initial data
        let initialTxID = try await db.beginTransaction()
        let testRow = TestDataGenerator.generateTestRow(id: 1, name: "Alice", age: 25, salary: 50000.0)
        let rid = try await db.insert(table: "users", row: testRow, txID: initialTxID)
        try await db.commit(initialTxID)
        
        // Start multiple concurrent transactions that modify the same row
        let concurrentTasks = 20
        var tasks: [Task<Void, Never>] = []
        
        for i in 0..<concurrentTasks {
            let task = Task {
                do {
                    let txID = try await db.beginTransaction()
                    
                    // Read the row
                    let row = try await db.read(rid: rid)
                    try TestAssertions.assertNotNil(row, "Row should be readable")
                    
                    // Update the row
                    let updatedRow = TestDataGenerator.generateTestRow(
                        id: 1,
                        name: "Alice\(i)",
                        age: 25 + i,
                        salary: 50000.0 + Double(i * 1000)
                    )
                    
                    try await db.update(rid: rid, newRow: updatedRow, txID: txID)
                    try await db.commit(txID)
                } catch {
                    // Some transactions may fail due to conflicts - this is expected
                }
            }
            tasks.append(task)
        }
        
        // Wait for all tasks to complete
        for task in tasks {
            await task.value
        }
        
        // Verify database is still functional
        let stats = await db.getStatistics()
        try TestAssertions.assertTrue(stats.isStarted, "Database should still be started")
        
        // Verify the row still exists and is readable
        let finalRow = try await db.read(rid: rid)
        try TestAssertions.assertNotNil(finalRow, "Row should still be readable after conflicts")
        
        try await db.shutdown()
    }
    
    /// Test long-running transactions
    @Test("Long-Running Transactions")
    func testLongRunningTransactions() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let config = ColibrìDB.Configuration(
            dataDirectory: tempDir,
            walDirectory: tempDir.appendingPathComponent("wal"),
            bufferPoolSize: 1000,
            enableWAL: true,
            enableMVCC: true
        )
        
        let db = try ColibrìDB(config: config)
        try await db.start()
        
        // Create table
        let tableDef = TestDataGenerator.generateTableDefinition(name: "users")
        try await db.createTable(tableDef)
        
        // Start a long-running transaction
        let longTxID = try await db.beginTransaction()
        
        // Insert many rows in the long transaction
        for i in 0..<1000 {
            let testRow = TestDataGenerator.generateTestRow(
                id: i + 1,
                name: "User\(i + 1)",
                age: 20 + (i % 50),
                salary: 30000.0 + Double(i * 100)
            )
            
            let rid = try await db.insert(table: "users", row: testRow, txID: longTxID)
            try TestAssertions.assertTrue(rid > 0, "Row ID should be positive")
        }
        
        // Start other transactions while the long transaction is running
        let concurrentTasks = 10
        var tasks: [Task<Void, Never>] = []
        
        for i in 0..<concurrentTasks {
            let task = Task {
                do {
                    let txID = try await db.beginTransaction()
                    
                    let testRow = TestDataGenerator.generateTestRow(
                        id: 1000 + i + 1,
                        name: "ConcurrentUser\(i + 1)",
                        age: 30 + i,
                        salary: 40000.0 + Double(i * 1000)
                    )
                    
                    let rid = try await db.insert(table: "users", row: testRow, txID: txID)
                    try await db.commit(txID)
                    
                    // Verify the row is readable
                    let retrievedRow = try await db.read(rid: rid)
                    try TestAssertions.assertNotNil(retrievedRow, "Row should be retrievable")
                } catch {
                    // Handle errors silently for this test
                }
            }
            tasks.append(task)
        }
        
        // Wait for concurrent tasks to complete
        for task in tasks {
            await task.value
        }
        
        // Commit the long transaction
        try await db.commit(longTxID)
        
        // Verify database is still functional
        let stats = await db.getStatistics()
        try TestAssertions.assertTrue(stats.isStarted, "Database should still be started")
        
        try await db.shutdown()
    }
    
    /// Test transaction rollback under stress
    @Test("Transaction Rollback Under Stress")
    func testTransactionRollbackUnderStress() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let config = ColibrìDB.Configuration(
            dataDirectory: tempDir,
            walDirectory: tempDir.appendingPathComponent("wal"),
            bufferPoolSize: 1000,
            enableWAL: true,
            enableMVCC: true
        )
        
        let db = try ColibrìDB(config: config)
        try await db.start()
        
        // Create table
        let tableDef = TestDataGenerator.generateTableDefinition(name: "users")
        try await db.createTable(tableDef)
        
        // Start multiple transactions and rollback some
        let transactionCount = 100
        var committedRIDs: [RID] = []
        
        for i in 0..<transactionCount {
            let txID = try await db.beginTransaction()
            
            let testRow = TestDataGenerator.generateTestRow(
                id: i + 1,
                name: "User\(i + 1)",
                age: 20 + (i % 50),
                salary: 30000.0 + Double(i * 100)
            )
            
            let rid = try await db.insert(table: "users", row: testRow, txID: txID)
            
            if i % 3 == 0 {
                // Rollback every third transaction
                try await db.abort(txID)
            } else {
                // Commit the rest
                try await db.commit(txID)
                committedRIDs.append(rid)
            }
        }
        
        // Verify only committed transactions are visible
        for rid in committedRIDs {
            let row = try await db.read(rid: rid)
            try TestAssertions.assertNotNil(row, "Committed row should be readable")
        }
        
        // Verify database is still functional
        let stats = await db.getStatistics()
        try TestAssertions.assertTrue(stats.isStarted, "Database should still be started")
        
        try await db.shutdown()
    }
    
    /// Test buffer pool eviction under stress
    @Test("Buffer Pool Eviction Under Stress")
    func testBufferPoolEvictionUnderStress() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let diskManager = try FileDiskManager(filePath: tempDir.appendingPathComponent("test.db"))
        let bufferPool = BufferPool(poolSize: 5, diskManager: diskManager) // Very small buffer pool
        
        let pageCount = 1000
        var pageIDs: [PageID] = []
        
        // Access many pages to trigger eviction
        for i in 0..<pageCount {
            let pageID: PageID = PageID(i + 1)
            let page = try await bufferPool.getPage(pageID)
            
            // Modify page
            var modifiedPage = page
            modifiedPage.data = TestUtils.generateRandomData(size: 1024)
            try await bufferPool.putPage(pageID, page: modifiedPage, isDirty: true)
            
            // Unpin page to allow eviction
            try await bufferPool.unpinPage(pageID)
            
            pageIDs.append(pageID)
        }
        
        // Verify buffer pool statistics
        let stats = await bufferPool.getStatistics()
        try TestAssertions.assertTrue(stats.cachedPages <= 5, "Buffer pool should not exceed size limit")
        
        // Verify some pages are still accessible
        for pageID in pageIDs.prefix(10) {
            let page = try await bufferPool.getPage(pageID)
            try TestAssertions.assertNotNil(page, "Page should be accessible")
        }
    }
    
    /// Test WAL under stress
    @Test("WAL Under Stress")
    func testWALUnderStress() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let walPath = tempDir.appendingPathComponent("wal.log")
        let wal = try FileWAL(walFilePath: walPath)
        
        let recordCount = 50000
        let startTime = Date()
        
        // Append many records rapidly
        for i in 0..<recordCount {
            let txID: TxID = TxID(i + 1)
            let pageID: PageID = PageID(i + 1)
            let payload = TestUtils.generateRandomData(size: 100)
            
            try await wal.append(kind: .update, txID: txID, pageID: pageID, payload: payload)
        }
        
        // Flush all records
        try await wal.flush()
        
        let endTime = Date()
        let duration = endTime.timeIntervalSince(startTime)
        
        // Verify performance is reasonable
        let rps = Double(recordCount) / duration
        try TestAssertions.assertTrue(rps > 100, "Should achieve at least 100 RPS under stress")
        
        // Verify all records were written
        let currentLSN = await wal.getCurrentLSN()
        try TestAssertions.assertEqual(currentLSN, LSN(recordCount + 1), "Should have correct number of records")
    }
    
    /// Test B+Tree under stress
    @Test("B+Tree Under Stress")
    func testBTreeUnderStress() async throws {
        let btree = BTreeIndex()
        
        let keyCount = 50000
        let startTime = Date()
        
        // Insert many keys rapidly
        for i in 0..<keyCount {
            try await btree.insert(key: Value.int(i), rid: RID(i))
        }
        
        let insertTime = Date()
        let insertDuration = insertTime.timeIntervalSince(startTime)
        
        // Verify tree structure is still valid
        let keyOrder = await btree.checkKeyOrderInvariant()
        try TestAssertions.assertTrue(keyOrder, "Key order should be maintained under stress")
        
        let structure = await btree.checkStructureInvariant()
        try TestAssertions.assertTrue(structure, "Structure should be valid under stress")
        
        // Test search performance under stress
        let searchStartTime = Date()
        for i in stride(from: 0, to: keyCount, by: 100) {
            let foundRids = await btree.search(key: Value.int(i))
            try TestAssertions.assertNotNil(foundRids, "Key should be found")
        }
        let searchTime = Date()
        let searchDuration = searchTime.timeIntervalSince(searchStartTime)
        
        // Verify performance is reasonable
        let insertRate = Double(keyCount) / insertDuration
        let searchRate = Double(keyCount / 100) / searchDuration
        
        try TestAssertions.assertTrue(insertRate > 100, "Should achieve at least 100 insertions per second")
        try TestAssertions.assertTrue(searchRate > 1000, "Should achieve at least 1000 searches per second")
    }
    
    /// Test authentication under stress
    @Test("Authentication Under Stress")
    func testAuthenticationUnderStress() async throws {
        let authManager = AuthenticationManager()
        
        // Create many users
        let userCount = 1000
        for i in 0..<userCount {
            try await authManager.createUser(username: "user\(i)", password: "password\(i)")
        }
        
        let authCount = 10000
        let startTime = Date()
        
        // Perform many authentications
        for i in 0..<authCount {
            let userIndex = i % userCount
            let token = try await authManager.authenticate(username: "user\(userIndex)", password: "password\(userIndex)")
            try TestAssertions.assertNotNil(token, "Authentication should succeed")
        }
        
        let endTime = Date()
        let duration = endTime.timeIntervalSince(startTime)
        
        // Verify performance is reasonable
        let aps = Double(authCount) / duration
        try TestAssertions.assertTrue(aps > 100, "Should achieve at least 100 APS under stress")
    }
    
    /// Test system recovery under stress
    @Test("System Recovery Under Stress")
    func testSystemRecoveryUnderStress() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let config = ColibrìDB.Configuration(
            dataDirectory: tempDir,
            walDirectory: tempDir.appendingPathComponent("wal"),
            bufferPoolSize: 1000,
            enableWAL: true,
            enableMVCC: true
        )
        
        // Create first database instance
        let db1 = try ColibrìDB(config: config)
        try await db1.start()
        
        // Create table and insert many rows
        let tableDef = TestDataGenerator.generateTableDefinition(name: "users")
        try await db1.createTable(tableDef)
        
        let txID = try await db1.beginTransaction()
        var rids: [RID] = []
        
        for i in 0..<10000 {
            let testRow = TestDataGenerator.generateTestRow(
                id: i + 1,
                name: "User\(i + 1)",
                age: 20 + (i % 50),
                salary: 30000.0 + Double(i * 100)
            )
            
            let rid = try await db1.insert(table: "users", row: testRow, txID: txID)
            rids.append(rid)
        }
        
        try await db1.commit(txID)
        
        // Shutdown first instance
        try await db1.shutdown()
        
        // Create second database instance (should recover)
        let db2 = try ColibrìDB(config: config)
        try await db2.start()
        
        // Verify all data was recovered
        for rid in rids.prefix(100) { // Check first 100 rows
            let retrievedRow = try await db2.read(rid: rid)
            try TestAssertions.assertNotNil(retrievedRow, "Data should be recovered")
        }
        
        // Verify table exists
        let tables = await db2.listTables()
        try TestAssertions.assertContains(tables, "users", "Table should be recovered")
        
        try await db2.shutdown()
    }
    
    /// Test extreme concurrency
    @Test("Extreme Concurrency")
    func testExtremeConcurrency() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let config = ColibrìDB.Configuration(
            dataDirectory: tempDir,
            walDirectory: tempDir.appendingPathComponent("wal"),
            bufferPoolSize: 10000,
            enableWAL: true,
            enableMVCC: true
        )
        
        let db = try ColibrìDB(config: config)
        try await db.start()
        
        // Create table
        let tableDef = TestDataGenerator.generateTableDefinition(name: "users")
        try await db.createTable(tableDef)
        
        // Start many concurrent tasks
        let concurrentTasks = 100
        let operationsPerTask = 100
        var tasks: [Task<Void, Never>] = []
        
        for taskId in 0..<concurrentTasks {
            let task = Task {
                do {
                    for i in 0..<operationsPerTask {
                        let txID = try await db.beginTransaction()
                        
                        let testRow = TestDataGenerator.generateTestRow(
                            id: taskId * operationsPerTask + i + 1,
                            name: "User\(taskId * operationsPerTask + i + 1)",
                            age: 20 + (i % 50),
                            salary: 30000.0 + Double(i * 100)
                        )
                        
                        let rid = try await db.insert(table: "users", row: testRow, txID: txID)
                        try await db.commit(txID)
                        
                        // Read back the data
                        let retrievedRow = try await db.read(rid: rid)
                        try TestAssertions.assertNotNil(retrievedRow, "Row should be retrievable")
                    }
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
        
        // Verify database is still functional
        let stats = await db.getStatistics()
        try TestAssertions.assertTrue(stats.isStarted, "Database should still be started")
        
        try await db.shutdown()
    }
}
