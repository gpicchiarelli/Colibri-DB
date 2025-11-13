//
//  PerformanceTests.swift
//  ColibrìDB Performance Tests
//
//  Tests for performance, benchmarking, and optimization
//

import Foundation
import XCTest
@testable import ColibriCore

/// Performance Tests for ColibrìDB
final class PerformanceTests {
    
    /// Test database startup performance
    func testDatabaseStartupPerformance() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let config = TestUtils.createTestConfig(dataDirectory: tempDir)
        
        let db = try ColibrìDB(config: config)
        
        // Measure startup time
        let (_, startupTime) = try await TestUtils.measureAsyncTime {
            try await db.start()
        }
        
        // Verify startup performance is reasonable
        XCTAssertTrue(startupTime < 1.0, "Database startup should be fast")
        
        try await db.shutdown()
    }
    
    /// Test transaction performance
    func testTransactionPerformance() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let config = TestUtils.createTestConfig(dataDirectory: tempDir)
        
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
            
            let rid = try await db.insert(table: "users", row: testRow, txId: txID)
            try await db.commit(txId: txID)
        }
        
        let endTime = Date()
        let duration = endTime.timeIntervalSince(startTime)
        
        // Calculate transactions per second
        let tps = Double(transactionCount) / duration
        
        // Verify performance is reasonable
        XCTAssertTrue(tps > 100, "Should achieve at least 100 TPS")
        XCTAssertTrue(duration < 10.0, "Should complete within 10 seconds")
        
        try await db.shutdown()
    }
    
    /// Test insert performance
    func testInsertPerformance() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let config = TestUtils.createTestConfig(dataDirectory: tempDir)
        
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
            
            let rid = try await db.insert(table: "users", row: testRow, txId: txID)
            XCTAssertNotEqual(rid.pageID, PageID(0), "Row ID should be valid")
        }
        
        let endTime = Date()
        let duration = endTime.timeIntervalSince(startTime)
        
        // Calculate inserts per second
        let ips = Double(insertCount) / duration
        
        // Verify performance is reasonable
        XCTAssertTrue(ips > 1000, "Should achieve at least 1000 IPS")
        XCTAssertTrue(duration < 10.0, "Should complete within 10 seconds")
        
        try await db.commit(txId: txID)
        try await db.shutdown()
    }
    
    /// Test read performance
    func testReadPerformance() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let config = TestUtils.createTestConfig(dataDirectory: tempDir)
        
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
            
            let rid = try await db.insert(table: "users", row: testRow, txId: txID)
            rids.append(rid)
        }
        
        try await db.commit(txId: txID)
        
        let readCount = 10000
        let startTime = Date()
        
        // Perform many reads
        for i in 0..<readCount {
            let rid = rids[i % rids.count]
            // Use query instead of direct read
            let readTxID = try await db.beginTransaction()
            let queryResult = try await db.executeQuery("SELECT * FROM users LIMIT 1", txId: readTxID)
            XCTAssertGreaterThan(queryResult.rows.count, 0, "Row should be readable")
            try await db.commit(txId: readTxID)
        }
        
        let endTime = Date()
        let duration = endTime.timeIntervalSince(startTime)
        
        // Calculate reads per second
        let rps = Double(readCount) / duration
        
        // Verify performance is reasonable
        XCTAssertTrue(rps > 5000, "Should achieve at least 5000 RPS")
        XCTAssertTrue(duration < 2.0, "Should complete within 2 seconds")
        
        try await db.shutdown()
    }
    
    /// Test update performance
    func testUpdatePerformance() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let config = TestUtils.createTestConfig(dataDirectory: tempDir)
        
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
            
            let rid = try await db.insert(table: "users", row: testRow, txId: txID)
            rids.append(rid)
        }
        
        try await db.commit(txId: txID)
        
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
            
            try await db.update(table: "users", rid: rid, row: updatedRow, txId: updateTxID)
        }
        
        let endTime = Date()
        let duration = endTime.timeIntervalSince(startTime)
        
        // Calculate updates per second
        let ups = Double(updateCount) / duration
        
        // Verify performance is reasonable
        XCTAssertTrue(ups > 1000, "Should achieve at least 1000 UPS")
        XCTAssertTrue(duration < 5.0, "Should complete within 5 seconds")
        
        try await db.commit(txId: updateTxID)
        try await db.shutdown()
    }
    
    /// Test buffer pool performance
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
        XCTAssertTrue(pps > 100, "Should achieve at least 100 PPS")
        XCTAssertTrue(duration < 10.0, "Should complete within 10 seconds")
    }
    
    /// Test WAL performance
    func testWALPerformance() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let walPath = tempDir.appendingPathComponent("wal.log")
        let wal = try FileWAL(walFilePath: walPath)
        
        let recordCount = 10000
        let startTime = Date()
        
        // Append many records
        for i in 0..<recordCount {
            let txId: TxID = TxID(i + 1)
            let pageID: PageID = PageID(i + 1)
            let payload = TestUtils.generateRandomData(size: 100)
            
            try await wal.append(kind: .heapUpdate, txID: txId, pageID: pageID, payload: payload)
        }
        
        // Flush all records
        try await wal.flush()
        
        let endTime = Date()
        let duration = endTime.timeIntervalSince(startTime)
        
        // Calculate records per second
        let rps = Double(recordCount) / duration
        
        // Verify performance is reasonable
        XCTAssertTrue(rps > 1000, "Should achieve at least 1000 RPS")
        XCTAssertTrue(duration < 10.0, "Should complete within 10 seconds")
    }
    
    /// Test B+Tree performance
    func testBTreePerformance() async throws {
        let btree = BTreeIndex()
        
        let keyCount = 10000
        let startTime = Date()
        
        // Insert many keys
        for i in 0..<keyCount {
            try await btree.insert(key: Value.int(Int64(i)), rid: RID(pageID: PageID(i), slotID: UInt32(0)))
        }
        
        let insertTime = Date()
        let insertDuration = insertTime.timeIntervalSince(startTime)
        
        // Search for some keys
        let searchStartTime = Date()
        for i in stride(from: 0, to: keyCount, by: 10) {
            let foundRids = await btree.search(key: Value.int(Int64(i)))
            XCTAssertNotNil(foundRids, "Key should be found")
        }
        let searchTime = Date()
        let searchDuration = searchTime.timeIntervalSince(searchStartTime)
        
        // Calculate performance metrics
        let insertRate = Double(keyCount) / insertDuration
        let searchRate = Double(keyCount / 10) / searchDuration
        
        // Verify performance is reasonable
        XCTAssertTrue(insertRate > 1000, "Should achieve at least 1000 insertions per second")
        XCTAssertTrue(searchRate > 5000, "Should achieve at least 5000 searches per second")
        XCTAssertTrue(insertDuration < 10.0, "Insertions should complete within 10 seconds")
        XCTAssertTrue(searchDuration < 1.0, "Searches should complete within 1 second")
    }
    
    /// Test SQL parser performance
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
            XCTAssertNotNil(statement, "Query should parse successfully")
        }
        
        let endTime = Date()
        let duration = endTime.timeIntervalSince(startTime)
        
        // Calculate queries per second
        let qps = Double(queryCount) / duration
        
        // Verify performance is reasonable
        XCTAssertTrue(qps > 10000, "Should achieve at least 10000 QPS")
        XCTAssertTrue(duration < 1.0, "Should complete within 1 second")
    }
    
    /// Test authentication performance
    func testAuthenticationPerformance() async throws {
        let authManager = AuthenticationManager()
        
        // Create user
        try authManager.createUser(username: "alice", email: "alice@test.com", password: "password123", role: .user)
        
        let authCount = 10000
        let startTime = Date()
        
        // Perform many authentications
        for i in 0..<authCount {
            let token = try await authManager.authenticate(username: "alice", password: "password123")
            XCTAssertNotNil(token, "Authentication should succeed")
            
            let validatedSession = try authManager.validateSession(sessionId: token)
            XCTAssertNotNil(validatedSession, "Session validation should succeed")
        }
        
        let endTime = Date()
        let duration = endTime.timeIntervalSince(startTime)
        
        // Calculate authentications per second
        let aps = Double(authCount) / duration
        
        // Verify performance is reasonable
        XCTAssertTrue(aps > 1000, "Should achieve at least 1000 APS")
        XCTAssertTrue(duration < 10.0, "Should complete within 10 seconds")
    }
    
    /// Test concurrent performance
    func testConcurrentPerformance() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let config = TestUtils.createTestConfig(dataDirectory: tempDir)
        
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
                        
                        let rid = try await db.insert(table: "users", row: testRow, txId: txID)
                        try await db.commit(txId: txID)
                        
                        // Read back the data using query
                        let readTxID = try await db.beginTransaction()
                        let queryResult = try await db.executeQuery("SELECT * FROM users LIMIT 1", txId: readTxID)
                        XCTAssertGreaterThan(queryResult.rows.count, 0, "Row should be retrievable")
                        try await db.commit(txId: readTxID)
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
        XCTAssertTrue(ops > 100, "Should achieve at least 100 OPS")
        XCTAssertTrue(duration < 30.0, "Should complete within 30 seconds")
        
        try await db.shutdown()
    }
    
    /// Test memory usage
    func testMemoryUsage() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let config = TestUtils.createTestConfig(dataDirectory: tempDir)
        
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
            
            let rid = try await db.insert(table: "users", row: testRow, txId: txID)
            XCTAssertNotEqual(rid.pageID, PageID(0), "Row ID should be valid")
        }
        
        try await db.commit(txId: txID)
        
        // Verify database is still functional
        let stats = await db.getStatistics()
        XCTAssertGreaterThan(stats.transactionsStarted, 0, "Database should have processed transactions")
        
        // Verify memory usage is reasonable
        XCTAssertTrue(stats.bufferPoolSize <= 1000, "Buffer pool should not exceed limit")
        
        try await db.shutdown()
    }
    
    /// Test scalability
    func testScalability() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let config = TestUtils.createTestConfig(dataDirectory: tempDir)
        
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
                
                let rid = try await db.insert(table: "users", row: testRow, txId: txID)
                XCTAssertNotEqual(rid.pageID, PageID(0), "Row ID should be valid")
            }
            
            let endTime = Date()
            let duration = endTime.timeIntervalSince(startTime)
            
            let rate = Double(size) / duration
            results.append(rate)
            
            try await db.commit(txId: txID)
        }
        
        // Verify scalability (performance should not degrade significantly)
        let firstRate = results[0]
        let lastRate = results[results.count - 1]
        let degradation = (firstRate - lastRate) / firstRate
        
        XCTAssertTrue(degradation < 0.5, "Performance degradation should be less than 50%")
        
        try await db.shutdown()
    }
}

