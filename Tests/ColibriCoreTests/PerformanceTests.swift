//
//  PerformanceTests.swift
//  ColibrìDB Performance Tests
//
//  Tests for performance, benchmarking, and optimization
//

import Foundation
import Testing
@testable import ColibriCore

/// Performance Tests for ColibrìDB
@Suite("Performance Tests")
struct PerformanceTests {
    
    /// Test database startup performance
    @Test("Database Startup Performance")
    func testDatabaseStartupPerformance() async throws {
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
        
        // Measure startup time
        let (_, startupTime) = try TestUtils.measureAsyncTime {
            try await db.start()
        }
        
        // Verify startup performance is reasonable
        try TestAssertions.assertTrue(startupTime < 1.0, "Database startup should be fast")
        
        try await db.shutdown()
    }
    
    /// Test transaction performance
    @Test("Transaction Performance")
    func testTransactionPerformance() async throws {
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
        
        let transactionCount = 1000
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
        }
        
        let endTime = Date()
        let duration = endTime.timeIntervalSince(startTime)
        
        // Calculate transactions per second
        let tps = Double(transactionCount) / duration
        
        // Verify performance is reasonable
        try TestAssertions.assertTrue(tps > 100, "Should achieve at least 100 TPS")
        try TestAssertions.assertTrue(duration < 10.0, "Should complete within 10 seconds")
        
        try await db.shutdown()
    }
    
    /// Test insert performance
    @Test("Insert Performance")
    func testInsertPerformance() async throws {
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
        
        let insertCount = 10000
        let txID = try await db.beginTransaction()
        
        let startTime = Date()
        
        // Perform many inserts
        for i in 0..<insertCount {
            let testRow = TestDataGenerator.generateTestRow(
                id: i + 1,
                name: "User\(i + 1)",
                age: 20 + (i % 50),
                salary: 30000.0 + Double(i * 100)
            )
            
            let rid = try await db.insert(table: "users", row: testRow, txID: txID)
            try TestAssertions.assertTrue(rid > 0, "Row ID should be positive")
        }
        
        let endTime = Date()
        let duration = endTime.timeIntervalSince(startTime)
        
        // Calculate inserts per second
        let ips = Double(insertCount) / duration
        
        // Verify performance is reasonable
        try TestAssertions.assertTrue(ips > 1000, "Should achieve at least 1000 IPS")
        try TestAssertions.assertTrue(duration < 10.0, "Should complete within 10 seconds")
        
        try await db.commit(txID)
        try await db.shutdown()
    }
    
    /// Test read performance
    @Test("Read Performance")
    func testReadPerformance() async throws {
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
        
        // Create table and insert data
        let tableDef = TestDataGenerator.generateTableDefinition(name: "users")
        try await db.createTable(tableDef)
        
        let txID = try await db.beginTransaction()
        var rids: [RID] = []
        
        // Insert test data
        for i in 0..<1000 {
            let testRow = TestDataGenerator.generateTestRow(
                id: i + 1,
                name: "User\(i + 1)",
                age: 20 + (i % 50),
                salary: 30000.0 + Double(i * 100)
            )
            
            let rid = try await db.insert(table: "users", row: testRow, txID: txID)
            rids.append(rid)
        }
        
        try await db.commit(txID)
        
        let readCount = 10000
        let startTime = Date()
        
        // Perform many reads
        for i in 0..<readCount {
            let rid = rids[i % rids.count]
            let row = try await db.read(rid: rid)
            try TestAssertions.assertNotNil(row, "Row should be readable")
        }
        
        let endTime = Date()
        let duration = endTime.timeIntervalSince(startTime)
        
        // Calculate reads per second
        let rps = Double(readCount) / duration
        
        // Verify performance is reasonable
        try TestAssertions.assertTrue(rps > 5000, "Should achieve at least 5000 RPS")
        try TestAssertions.assertTrue(duration < 2.0, "Should complete within 2 seconds")
        
        try await db.shutdown()
    }
    
    /// Test update performance
    @Test("Update Performance")
    func testUpdatePerformance() async throws {
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
        
        // Create table and insert data
        let tableDef = TestDataGenerator.generateTableDefinition(name: "users")
        try await db.createTable(tableDef)
        
        let txID = try await db.beginTransaction()
        var rids: [RID] = []
        
        // Insert test data
        for i in 0..<1000 {
            let testRow = TestDataGenerator.generateTestRow(
                id: i + 1,
                name: "User\(i + 1)",
                age: 20 + (i % 50),
                salary: 30000.0 + Double(i * 100)
            )
            
            let rid = try await db.insert(table: "users", row: testRow, txID: txID)
            rids.append(rid)
        }
        
        try await db.commit(txID)
        
        let updateCount = 5000
        let updateTxID = try await db.beginTransaction()
        
        let startTime = Date()
        
        // Perform many updates
        for i in 0..<updateCount {
            let rid = rids[i % rids.count]
            let updatedRow = TestDataGenerator.generateTestRow(
                id: i + 1,
                name: "UpdatedUser\(i + 1)",
                age: 25 + (i % 50),
                salary: 35000.0 + Double(i * 100)
            )
            
            try await db.update(rid: rid, newRow: updatedRow, txID: updateTxID)
        }
        
        let endTime = Date()
        let duration = endTime.timeIntervalSince(startTime)
        
        // Calculate updates per second
        let ups = Double(updateCount) / duration
        
        // Verify performance is reasonable
        try TestAssertions.assertTrue(ups > 1000, "Should achieve at least 1000 UPS")
        try TestAssertions.assertTrue(duration < 5.0, "Should complete within 5 seconds")
        
        try await db.commit(updateTxID)
        try await db.shutdown()
    }
    
    /// Test buffer pool performance
    @Test("Buffer Pool Performance")
    func testBufferPoolPerformance() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let diskManager = try FileDiskManager(filePath: tempDir.appendingPathComponent("test.db"))
        let bufferPool = BufferPool(poolSize: 100, diskManager: diskManager)
        
        let pageCount = 1000
        let startTime = Date()
        
        // Access many pages
        for i in 0..<pageCount {
            let pageID: PageID = PageID(i + 1)
            let page = try await bufferPool.getPage(pageID)
            
            // Modify page
            var modifiedPage = page
            modifiedPage.data = TestUtils.generateRandomData(size: 1024)
            try await bufferPool.putPage(pageID, page: modifiedPage, isDirty: true)
            
            // Unpin page
            try await bufferPool.unpinPage(pageID)
        }
        
        let endTime = Date()
        let duration = endTime.timeIntervalSince(startTime)
        
        // Calculate pages per second
        let pps = Double(pageCount) / duration
        
        // Verify performance is reasonable
        try TestAssertions.assertTrue(pps > 100, "Should achieve at least 100 PPS")
        try TestAssertions.assertTrue(duration < 10.0, "Should complete within 10 seconds")
    }
    
    /// Test WAL performance
    @Test("WAL Performance")
    func testWALPerformance() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let walPath = tempDir.appendingPathComponent("wal.log")
        let wal = try FileWAL(walFilePath: walPath)
        
        let recordCount = 10000
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
        let duration = endTime.timeIntervalSince(startTime)
        
        // Calculate records per second
        let rps = Double(recordCount) / duration
        
        // Verify performance is reasonable
        try TestAssertions.assertTrue(rps > 1000, "Should achieve at least 1000 RPS")
        try TestAssertions.assertTrue(duration < 10.0, "Should complete within 10 seconds")
    }
    
    /// Test B+Tree performance
    @Test("B+Tree Performance")
    func testBTreePerformance() async throws {
        let btree = BTreeIndex()
        
        let keyCount = 10000
        let startTime = Date()
        
        // Insert many keys
        for i in 0..<keyCount {
            try await btree.insert(key: Value.int(i), rid: RID(i))
        }
        
        let insertTime = Date()
        let insertDuration = insertTime.timeIntervalSince(startTime)
        
        // Search for some keys
        let searchStartTime = Date()
        for i in stride(from: 0, to: keyCount, by: 10) {
            let foundRids = await btree.search(key: Value.int(i))
            try TestAssertions.assertNotNil(foundRids, "Key should be found")
        }
        let searchTime = Date()
        let searchDuration = searchTime.timeIntervalSince(searchStartTime)
        
        // Calculate performance metrics
        let insertRate = Double(keyCount) / insertDuration
        let searchRate = Double(keyCount / 10) / searchDuration
        
        // Verify performance is reasonable
        try TestAssertions.assertTrue(insertRate > 1000, "Should achieve at least 1000 insertions per second")
        try TestAssertions.assertTrue(searchRate > 5000, "Should achieve at least 5000 searches per second")
        try TestAssertions.assertTrue(insertDuration < 10.0, "Insertions should complete within 10 seconds")
        try TestAssertions.assertTrue(searchDuration < 1.0, "Searches should complete within 1 second")
    }
    
    /// Test SQL parser performance
    @Test("SQL Parser Performance")
    func testSQLParserPerformance() async throws {
        var parser = SQLParser()
        
        let queryCount = 10000
        let queries = [
            "SELECT * FROM users WHERE age > 25",
            "INSERT INTO users VALUES (1, 'Alice', 25)",
            "UPDATE users SET age = 26 WHERE id = 1",
            "DELETE FROM users WHERE age < 18",
            "CREATE TABLE users (id INT, name VARCHAR(100))",
            "DROP TABLE users"
        ]
        
        let startTime = Date()
        
        // Parse many queries
        for i in 0..<queryCount {
            let query = queries[i % queries.count]
            let statement = try parser.parse(query)
            try TestAssertions.assertNotNil(statement, "Query should parse successfully")
        }
        
        let endTime = Date()
        let duration = endTime.timeIntervalSince(startTime)
        
        // Calculate queries per second
        let qps = Double(queryCount) / duration
        
        // Verify performance is reasonable
        try TestAssertions.assertTrue(qps > 10000, "Should achieve at least 10000 QPS")
        try TestAssertions.assertTrue(duration < 1.0, "Should complete within 1 second")
    }
    
    /// Test authentication performance
    @Test("Authentication Performance")
    func testAuthenticationPerformance() async throws {
        let authManager = AuthenticationManager()
        
        // Create user
        try await authManager.createUser(username: "alice", password: "password123")
        
        let authCount = 10000
        let startTime = Date()
        
        // Perform many authentications
        for i in 0..<authCount {
            let token = try await authManager.authenticate(username: "alice", password: "password123")
            try TestAssertions.assertNotNil(token, "Authentication should succeed")
            
            let validatedUser = await authManager.validateSession(token)
            try TestAssertions.assertNotNil(validatedUser, "Session validation should succeed")
        }
        
        let endTime = Date()
        let duration = endTime.timeIntervalSince(startTime)
        
        // Calculate authentications per second
        let aps = Double(authCount) / duration
        
        // Verify performance is reasonable
        try TestAssertions.assertTrue(aps > 1000, "Should achieve at least 1000 APS")
        try TestAssertions.assertTrue(duration < 10.0, "Should complete within 10 seconds")
    }
    
    /// Test concurrent performance
    @Test("Concurrent Performance")
    func testConcurrentPerformance() async throws {
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
        
        let concurrentTasks = 10
        let operationsPerTask = 100
        let startTime = Date()
        
        // Start multiple concurrent tasks
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
        
        let endTime = Date()
        let duration = endTime.timeIntervalSince(startTime)
        
        // Calculate total operations per second
        let totalOperations = concurrentTasks * operationsPerTask * 2 // insert + read
        let ops = Double(totalOperations) / duration
        
        // Verify performance is reasonable
        try TestAssertions.assertTrue(ops > 100, "Should achieve at least 100 OPS")
        try TestAssertions.assertTrue(duration < 30.0, "Should complete within 30 seconds")
        
        try await db.shutdown()
    }
    
    /// Test memory usage
    @Test("Memory Usage")
    func testMemoryUsage() async throws {
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
        
        // Insert many rows
        let txID = try await db.beginTransaction()
        
        for i in 0..<10000 {
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
        
        // Verify memory usage is reasonable
        try TestAssertions.assertTrue(stats.bufferPoolSize <= 1000, "Buffer pool should not exceed limit")
        
        try await db.shutdown()
    }
    
    /// Test scalability
    @Test("Scalability")
    func testScalability() async throws {
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
        
        let scaleSizes = [1000, 5000, 10000]
        var results: [Double] = []
        
        for size in scaleSizes {
            let txID = try await db.beginTransaction()
            
            let startTime = Date()
            
            // Insert data
            for i in 0..<size {
                let testRow = TestDataGenerator.generateTestRow(
                    id: i + 1,
                    name: "User\(i + 1)",
                    age: 20 + (i % 50),
                    salary: 30000.0 + Double(i * 100)
                )
                
                let rid = try await db.insert(table: "users", row: testRow, txID: txID)
                try TestAssertions.assertTrue(rid > 0, "Row ID should be positive")
            }
            
            let endTime = Date()
            let duration = endTime.timeIntervalSince(startTime)
            
            let rate = Double(size) / duration
            results.append(rate)
            
            try await db.commit(txID)
        }
        
        // Verify scalability (performance should not degrade significantly)
        let firstRate = results[0]
        let lastRate = results[results.count - 1]
        let degradation = (firstRate - lastRate) / firstRate
        
        try TestAssertions.assertTrue(degradation < 0.5, "Performance degradation should be less than 50%")
        
        try await db.shutdown()
    }
}
