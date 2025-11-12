import XCTest
@testable import ColibriCore

final class DatabaseIntegrationTests: XCTestCase {
    // MARK: - Helpers
    
    private func makeTempDirectory() throws -> URL {
        let url = FileManager.default.temporaryDirectory.appendingPathComponent(UUID().uuidString)
        try FileManager.default.createDirectory(at: url, withIntermediateDirectories: true)
        return url
    }
    
    private func makeDatabase() throws -> (db: ColibrìDB, directory: URL) {
        let directory = try makeTempDirectory()
        let config = ColibrìDBConfiguration(
            dataDirectory: directory,
            bufferPoolSize: 64,
            maxConnections: 8,
            walBufferSize: 64 * 1024,
            checkpointInterval: 60,
            logLevel: .warning,
            enableStatistics: true,
            enableAutoAnalyze: false
        )
        let database = try ColibrìDB(config: config)
        return (database, directory)
    }
    
    private func cleanup(_ directory: URL) {
        try? FileManager.default.removeItem(at: directory)
    }
    
    // MARK: - Tests
    
    func testDatabaseLifecycle() async throws {
        let (db, directory) = try makeDatabase()
        do {
            try await db.start()
            let runningAfterStart = await db.isDatabaseRunning()
            XCTAssertTrue(runningAfterStart)
            
            try await db.shutdown()
            let runningAfterShutdown = await db.isDatabaseRunning()
            XCTAssertFalse(runningAfterShutdown)
        } catch {
            try? await db.shutdown()
            throw error
        }
        cleanup(directory)
    }
    
    func testCreateAndDropTableUpdatesStatistics() async throws {
        let (db, directory) = try makeDatabase()
        do {
            try await db.start()
            
            let table = TestDataGenerator.generateTableDefinition(name: "users")
            try await db.createTable(table)
            
            var stats = await db.getStatistics()
            XCTAssertEqual(stats.tablesCreated, 1)
            
            try await db.dropTable("users")
            stats = await db.getStatistics()
            XCTAssertEqual(stats.tablesDropped, 1)
        } catch {
            try? await db.shutdown()
            cleanup(directory)
            throw error
        }
        
        try await db.shutdown()
        cleanup(directory)
    }
    
    func testInsertAndCommitTracksStatistics() async throws {
        let (db, directory) = try makeDatabase()
        do {
            try await db.start()
            
            let table = TestDataGenerator.generateTableDefinition(name: "orders")
            try await db.createTable(table)
            
            let baselineStats = await db.getStatistics()
            let txId = try await db.beginTransaction()
            let row = TestDataGenerator.generateTestRow(
                id: 1,
                name: "Order1",
                age: 42,
                salary: 123_45.0
            )
            _ = try await db.insert(table: "orders", row: row, txId: txId)
            try await db.commit(txId: txId)
            
            let stats = await db.getStatistics()
            XCTAssertEqual(stats.transactionsCommitted, baselineStats.transactionsCommitted + 1)
            XCTAssertEqual(stats.rowsInserted, baselineStats.rowsInserted + 1)
        } catch {
            try? await db.shutdown()
            cleanup(directory)
            throw error
        }
        
        try await db.shutdown()
        cleanup(directory)
    }
    
    func testExecuteQueryReturnsResult() async throws {
        let (db, directory) = try makeDatabase()
        do {
            try await db.start()
            
            let table = TestDataGenerator.generateTableDefinition(name: "logs")
            try await db.createTable(table)
            
            let txId = try await db.beginTransaction()
            _ = try await db.executeQuery("SELECT * FROM logs", txId: txId)
            try await db.abort(txId: txId)
            
            let stats = await db.getStatistics()
            XCTAssertEqual(stats.queriesExecuted, 1)
        } catch {
            try? await db.shutdown()
            cleanup(directory)
            throw error
        }
        
        try await db.shutdown()
        cleanup(directory)
    }
}

