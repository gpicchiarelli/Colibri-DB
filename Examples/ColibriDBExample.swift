//
//  ColibriDBExample.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-26.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Example usage of ColibrìDB system.

import Foundation
import ColibriCore

/// Example usage of ColibrìDB
public class ColibriDBExample {
    
    public static func runExample() {
        print("🚀 ColibrìDB Example")
        print("===================")
        
        // Create database configuration
        let config = DBConfig(
            dataDir: "./example_data",
            pageSize: 8192,
            dataBufferPoolPages: 1000,
            indexBufferPoolPages: 500,
            walEnabled: true,
            walFullFSyncEnabled: false,
            walCompression: .none,
            ioSequentialReadHint: true,
            autoCompactionEnabled: true,
            autoCompactionIntervalSeconds: 300,
            autoCompactionPagesPerRun: 32,
            lockTimeoutSeconds: 30.0
        )
        
        // Initialize ColibrìDB
        let colibriDB = ColibriDB(config: config)
        
        do {
            // Initialize the system
            try colibriDB.initialize()
            print("✅ Database initialized")
            
            // Start the system
            try colibriDB.start()
            print("✅ Database started")
            
            // Run example operations
            try runDatabaseOperations(colibriDB)
            try runQueryOperations(colibriDB)
            try runTransactionOperations(colibriDB)
            try runIndexOperations(colibriDB)
            try runMonitoringOperations(colibriDB)
            try runTestingOperations(colibriDB)
            
            // Get system status
            let status = colibriDB.getStatus()
            print("📊 System Status:")
            print("   Initialized: \(status.isInitialized)")
            print("   Running: \(status.isRunning)")
            print("   Health: \(status.healthStatus.status)")
            print("   Total Errors: \(status.errorStatistics.totalErrors)")
            
            // Get system info
            let systemInfo = colibriDB.getSystemInfo()
            print("💻 System Info:")
            print("   Version: \(systemInfo.version)")
            print("   Platform: \(systemInfo.platform)")
            print("   Architecture: \(systemInfo.architecture)")
            print("   CPU Cores: \(systemInfo.cpuCores)")
            print("   Memory Total: \(systemInfo.memoryTotal / 1024 / 1024) MB")
            print("   Memory Used: \(systemInfo.memoryUsed / 1024 / 1024) MB")
            print("   Optimizations: \(systemInfo.optimizationStatistics.optimizationsApplied.joined(separator: ", "))")
            
            // Stop the system
            try colibriDB.stop()
            print("✅ Database stopped")
            
            // Shutdown the system
            try colibriDB.shutdown()
            print("✅ Database shutdown")
            
        } catch {
            print("❌ Error: \(error.localizedDescription)")
        }
    }
    
    /// Run database operations example
    private static func runDatabaseOperations(_ colibriDB: ColibriDB) throws {
        print("\n📚 Database Operations Example")
        print("------------------------------")
        
        let database = colibriDB.database
        
        // Create a table
        let schema = CatalogTableSchema(columns: [
            CatalogColumnDefinition(name: "id", type: .int, nullable: false, defaultValue: nil),
            CatalogColumnDefinition(name: "name", type: .string, nullable: true, defaultValue: nil),
            CatalogColumnDefinition(name: "email", type: .string, nullable: true, defaultValue: nil),
            CatalogColumnDefinition(name: "age", type: .int, nullable: true, defaultValue: nil),
            CatalogColumnDefinition(name: "created_at", type: .date, nullable: false, defaultValue: nil)
        ])
        
        try database.createTable("users", in: "default", schema: schema)
        print("✅ Created table 'users'")
        
        // Insert some data
        let users = [
            (1, "Alice", "alice@example.com", 25, Date()),
            (2, "Bob", "bob@example.com", 30, Date()),
            (3, "Charlie", "charlie@example.com", 35, Date()),
            (4, "Diana", "diana@example.com", 28, Date()),
            (5, "Eve", "eve@example.com", 32, Date())
        ]
        
        for (id, name, email, age, createdAt) in users {
            let row: Row = [
                "id": .int(Int64(id)),
                "name": .string(name),
                "email": .string(email),
                "age": .int(Int64(age)),
                "created_at": .date(createdAt)
            ]
            
            let rid = try database.insert(into: "users", row: row)
            print("✅ Inserted user \(name) with RID: \(rid)")
        }
        
        // Get table statistics
        let stats = try database.getTableStatistics("users", in: "default")
        print("📊 Table Statistics:")
        print("   Row Count: \(stats.rowCount)")
        print("   Size Bytes: \(stats.sizeBytes)")
        print("   Avg Row Size: \(stats.avgRowSizeBytes) bytes")
    }
    
    /// Run query operations example
    private static func runQueryOperations(_ colibriDB: ColibriDB) throws {
        print("\n🔍 Query Operations Example")
        print("----------------------------")
        
        let queryExecutor = colibriDB.queryExecutor
        let context = ExecutionContext(database: colibriDB.database)
        
        // Simple SELECT query
        let result = try queryExecutor.executeSelect(table: "users", context: context)
        print("✅ SELECT query executed")
        print("   Rows returned: \(result.rowCount)")
        print("   Execution time: \(result.executionTime)s")
        
        // SELECT with WHERE clause
        let filteredResult = try queryExecutor.executeSelect(
            table: "users",
            whereClause: "age > 30",
            context: context
        )
        print("✅ SELECT with WHERE executed")
        print("   Rows returned: \(filteredResult.rowCount)")
        
        // INSERT query
        let insertResult = try queryExecutor.executeInsert(
            table: "users",
            values: [
                "id": .int(6),
                "name": .string("Frank"),
                "email": .string("frank@example.com"),
                "age": .int(27),
                "created_at": .date(Date())
            ],
            context: context
        )
        print("✅ INSERT query executed")
        print("   RID: \(insertResult.rid)")
        
        // UPDATE query
        let updateResult = try queryExecutor.executeUpdate(
            table: "users",
            values: ["age": .int(26)],
            whereClause: "name = 'Frank'",
            context: context
        )
        print("✅ UPDATE query executed")
        print("   Rows updated: \(updateResult.updatedCount)")
        
        // DELETE query
        let deleteResult = try queryExecutor.executeDelete(
            table: "users",
            whereClause: "age < 25",
            context: context
        )
        print("✅ DELETE query executed")
        print("   Rows deleted: \(deleteResult.deletedCount)")
    }
    
    /// Run transaction operations example
    private static func runTransactionOperations(_ colibriDB: ColibriDB) throws {
        print("\n🔄 Transaction Operations Example")
        print("---------------------------------")
        
        let transactionManager = colibriDB.transactionManager
        
        // Begin transaction
        let tid = transactionManager.begin(isolationLevel: .readCommitted)
        print("✅ Transaction \(tid) started")
        
        // Perform operations within transaction
        let database = colibriDB.database
        
        // Insert data within transaction
        let row: Row = [
            "id": .int(7),
            "name": .string("Grace"),
            "email": .string("grace@example.com"),
            "age": .int(29),
            "created_at": .date(Date())
        ]
        
        let rid = try database.insert(into: "users", row: row)
        print("✅ Inserted user within transaction, RID: \(rid)")
        
        // Commit transaction
        try transactionManager.commit(tid: tid)
        print("✅ Transaction \(tid) committed")
        
        // Begin another transaction
        let tid2 = transactionManager.begin(isolationLevel: .repeatableRead)
        print("✅ Transaction \(tid2) started")
        
        // Rollback transaction
        try transactionManager.rollback(tid: tid2)
        print("✅ Transaction \(tid2) rolled back")
        
        // Get transaction statistics
        let stats = transactionManager.getStatistics()
        print("📊 Transaction Statistics:")
        print("   Active Transactions: \(stats.activeTransactions)")
        print("   Total Transactions: \(stats.totalTransactions)")
        print("   Next Transaction ID: \(stats.nextTransactionId)")
    }
    
    /// Run index operations example
    private static func runIndexOperations(_ colibriDB: ColibriDB) throws {
        print("\n📇 Index Operations Example")
        print("---------------------------")
        
        let indexManager = colibriDB.indexManager
        
        // Create B+Tree index
        try indexManager.createIndex(
            name: "users_id_idx",
            on: "users",
            columns: ["id"],
            type: .bTree
        )
        print("✅ Created B+Tree index on 'id' column")
        
        // Create ART index
        try indexManager.createIndex(
            name: "users_name_idx",
            on: "users",
            columns: ["name"],
            type: .art
        )
        print("✅ Created ART index on 'name' column")
        
        // Create LSM-Tree index
        try indexManager.createIndex(
            name: "users_email_idx",
            on: "users",
            columns: ["email"],
            type: .lsmTree
        )
        print("✅ Created LSM-Tree index on 'email' column")
        
        // Search using index
        let searchResults = try indexManager.search(
            key: [1], // Search for id = 1
            in: "users_id_idx",
            on: "users"
        )
        print("✅ Index search executed")
        print("   Results: \(searchResults.count) RIDs")
        
        // Get index statistics
        let stats = try indexManager.getStatistics(for: "users_id_idx", on: "users")
        print("📊 Index Statistics:")
        print("   Entry Count: \(stats.entryCount)")
        print("   Size Bytes: \(stats.sizeBytes)")
        print("   Type: \(stats.type)")
        
        // Get all indexes for table
        let indexes = indexManager.getIndexes(for: "users")
        print("📋 Table Indexes: \(indexes.joined(separator: ", "))")
    }
    
    /// Run monitoring operations example
    private static func runMonitoringOperations(_ colibriDB: ColibriDB) throws {
        print("\n📊 Monitoring Operations Example")
        print("--------------------------------")
        
        let systemMonitor = colibriDB.systemMonitor
        
        // Get current metrics
        let metrics = systemMonitor.getCurrentMetrics()
        print("📈 Current Metrics:")
        print("   CPU Usage: \(String(format: "%.1f", metrics.cpu.usage))%")
        print("   Memory Usage: \(String(format: "%.1f", metrics.memory.usage))%")
        print("   I/O Read Latency: \(String(format: "%.1f", metrics.io.readLatency))ms")
        print("   I/O Write Latency: \(String(format: "%.1f", metrics.io.writeLatency))ms")
        print("   Active Queries: \(metrics.queries.activeQueries)")
        print("   Total Queries: \(metrics.queries.totalQueries)")
        print("   Active Transactions: \(metrics.transactions.activeCount)")
        print("   Total Transactions: \(metrics.transactions.totalCount)")
        
        // Get health status
        let healthStatus = systemMonitor.getHealthStatus()
        print("🏥 Health Status:")
        print("   Status: \(healthStatus.status)")
        print("   Issues: \(healthStatus.issues.count)")
        
        for issue in healthStatus.issues {
            print("   - \(issue.severity): \(issue.message)")
        }
        
        // Get error statistics
        let errorStats = colibriDB.getErrorStatistics()
        print("🚨 Error Statistics:")
        print("   Total Errors: \(errorStats.totalErrors)")
        print("   Critical Errors: \(errorStats.criticalErrors)")
        print("   High Errors: \(errorStats.highErrors)")
        print("   Medium Errors: \(errorStats.mediumErrors)")
        print("   Low Errors: \(errorStats.lowErrors)")
    }
    
    /// Run testing operations example
    private static func runTestingOperations(_ colibriDB: ColibriDB) throws {
        print("\n🧪 Testing Operations Example")
        print("-----------------------------")
        
        // Run unit tests
        let testResults = colibriDB.runUnitTests()
        print("🔬 Unit Tests:")
        print("   Total Tests: \(testResults.totalTests)")
        print("   Passed Tests: \(testResults.passedTests)")
        print("   Failed Tests: \(testResults.failedTests)")
        print("   Success Rate: \(String(format: "%.1f", testResults.successRate * 100))%")
        print("   Total Duration: \(String(format: "%.3f", testResults.totalDuration))s")
        
        // Run performance tests
        let benchmarkResults = colibriDB.runPerformanceTests()
        print("⚡ Performance Tests:")
        print("   Total Operations: \(benchmarkResults.totalOperations)")
        print("   Total Duration: \(String(format: "%.3f", benchmarkResults.totalDuration))s")
        print("   Average Throughput: \(String(format: "%.1f", benchmarkResults.averageThroughput)) ops/s")
        
        // Run diagnostics
        let diagnosticResults = colibriDB.runDiagnostics()
        print("🔍 System Diagnostics:")
        print("   Total Tests: \(diagnosticResults.totalTests)")
        print("   Passed Tests: \(diagnosticResults.passedTests)")
        print("   Failed Tests: \(diagnosticResults.failedTests)")
        print("   Success Rate: \(String(format: "%.1f", diagnosticResults.successRate * 100))%")
        
        for test in diagnosticResults.tests {
            let status = test.passed ? "✅" : "❌"
            print("   \(status) \(test.name): \(String(format: "%.3f", test.duration))s")
        }
    }
}

/// Main function to run the example
public func main() {
    ColibriDBExample.runExample()
}
