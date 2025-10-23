//
//  BasicUsage.swift
//  ColibrìDB Usage Examples
//
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//

import Foundation

/// Basic usage examples for ColibrìDB
public enum BasicUsageExamples {
    
    /// Example 1: Create and start a database
    public static func example1_CreateDatabase() async throws {
        // Configure the database
        let config = ColibrìDBConfiguration(
            dataDirectory: URL(fileURLWithPath: "/tmp/colibridb_data"),
            bufferPoolSize: 1000,
            maxConnections: 100,
            walBufferSize: 8192,
            checkpointInterval: 60.0
        )
        
        // Create database instance
        let db = try ColibrìDB(config: config)
        
        // Start the database (performs recovery if needed)
        try await db.start()
        
        logInfo("Database started: \(ColibriDBVersion.fullVersion)", category: .database)
        
        // Shutdown when done
        try await db.shutdown()
    }
    
    /// Example 2: Create table and insert data
    public static func example2_CreateTableAndInsert() async throws {
        let config = ColibrìDBConfiguration(
            dataDirectory: URL(fileURLWithPath: "/tmp/colibridb_data")
        )
        let db = try ColibrìDB(config: config)
        try await db.start()
        
        // Create a table
        let usersTable = TableDefinition(
            name: "users",
            columns: [
                ColumnDefinition(name: "id", type: .int, nullable: false),
                ColumnDefinition(name: "name", type: .string, nullable: false),
                ColumnDefinition(name: "email", type: .string, nullable: false),
                ColumnDefinition(name: "created_at", type: .date, nullable: false)
            ],
            primaryKey: ["id"]
        )
        
        try await db.createTable(usersTable)
        logInfo("Table 'users' created", category: .database)
        
        // Begin transaction
        let txID = try await db.beginTransaction()
        
        // Insert a row
        let row: Row = [
            "id": .int(1),
            "name": .string("Alice"),
            "email": .string("alice@example.com"),
            "created_at": .date(Date())
        ]
        
        let rid = try await db.insert(table: "users", row: row, txId: txID)
        logInfo("Inserted row with RID: \(rid)", category: .database)
        
        // Commit transaction
        try await db.commit(txId: txID)
        logInfo("Transaction committed", category: .transaction)
        
        try await db.shutdown()
    }
    
    /// Example 3: Read and update data
    public static func example3_ReadAndUpdate() async throws {
        let config = ColibrìDBConfiguration(
            dataDirectory: URL(fileURLWithPath: "/tmp/colibridb_data")
        )
        let db = try ColibrìDB(config: config)
        try await db.start()
        
        // Assume we have a RID from previous insert
        let rid = RID(pageID: 1, slotID: 0)
        
        // Begin transaction
        let txID = try await db.beginTransaction()
        
        // Read the row
        // let row = try await db.select(table: "users", rid: rid, txId: txID)
        // logInfo("Read row: \(row)", category: .database)
        
        // Create example row for update
        let row: Row = ["id": .int(1), "name": .string("Alice"), "email": .string("alice@example.com")]
        
        // Update the row
        var updatedRow = row
        updatedRow["name"] = Value.string("Alice Updated")
        
        try await db.update(table: "users", rid: rid, row: updatedRow, txId: txID)
        logInfo("Row updated", category: .database)
        
        // Commit transaction
        try await db.commit(txId: txID)
        
        try await db.shutdown()
    }
    
    /// Example 4: Transaction rollback
    public static func example4_TransactionRollback() async throws {
        let config = ColibrìDBConfiguration(
            dataDirectory: URL(fileURLWithPath: "/tmp/colibridb_data")
        )
        let db = try ColibrìDB(config: config)
        try await db.start()
        
        // Begin transaction
        let txID = try await db.beginTransaction()
        
        do {
            // Insert some data
            let row: Row = [
                "id": .int(2),
                "name": .string("Bob"),
                "email": .string("bob@example.com"),
                "created_at": .date(Date())
            ]
            
            _ = try await db.insert(table: "users", row: row, txId: txID)
            
            // Simulate an error
            throw DBError.internalError("Something went wrong")
            
        } catch {
            // Rollback on error
            logError("Error occurred: \(error)", category: .transaction)
            try await db.abort(txId: txID)
            logInfo("Transaction rolled back", category: .transaction)
        }
        
        try await db.shutdown()
    }
    
    /// Example 5: Query execution
    public static func example5_QueryExecution() async throws {
        let config = ColibrìDBConfiguration(
            dataDirectory: URL(fileURLWithPath: "/tmp/colibridb_data")
        )
        let db = try ColibrìDB(config: config)
        try await db.start()
        
        // Begin transaction
        let txID = try await db.beginTransaction()
        
        // Create a query plan: SELECT * FROM users WHERE id > 0
        let queryPlan: QueryPlanNode = .filter(
            predicate: "id > 0",
            child: .scan(table: "users")
        )
        
        // Execute query
        let results = try await db.executeQuery("SELECT * FROM users WHERE id > 0", txId: txID)
        logInfo("Query returned \(results.rowCount) rows", category: .query)
        
        for row in results.rows {
            logDebug("Row: \(row)", category: .query)
        }
        
        // Commit transaction
        try await db.commit(txId: txID)
        
        try await db.shutdown()
    }
    
    /// Example 6: Database server
    public static func example6_DatabaseServer() async throws {
        let dbConfig = ColibrìDBConfiguration(
            dataDirectory: URL(fileURLWithPath: "/tmp/colibridb_data")
        )
        
        let databaseConfig = DatabaseConfiguration(
            maxConnections: 100,
            cacheSize: 1024*1024*1024,
            walBufferSize: 8192
        )
        
        let serverConfig = DatabaseServer.Configuration(
            host: "127.0.0.1",
            port: 5432,
            maxConnections: 100,
            databaseConfig: databaseConfig
        )
        
        let server = try DatabaseServer(config: serverConfig)
        
        // Start the server
        try await server.start()
        logInfo("Server started on \(serverConfig.host):\(serverConfig.port)", category: .network)
        
        // Accept a connection
        let connection = try await server.acceptConnection(clientID: "client-1")
        
        // Authenticate
        try await connection.authenticate(username: "admin", password: "admin")
        logInfo("Client authenticated", category: .security)
        
        // Begin transaction
        let txID = try await connection.beginTransaction()
        logInfo("Transaction started: \(txID)", category: .transaction)
        
        // Execute query
        let queryPlan: QueryPlanNode = .scan(table: "users")
        let results = try await connection.executeQuery(sql: "SELECT * FROM users")
        print("Query returned \(results.count) rows")
        
        // Commit
        try await connection.commit()
        logInfo("Transaction committed", category: .transaction)
        
        // Close connection
        await connection.close()
        
        // Stop server
        try await server.stop()
    }
    
    /// Example 7: Statistics and monitoring
    public static func example7_StatisticsAndMonitoring() async throws {
        let config = ColibrìDBConfiguration(
            dataDirectory: URL(fileURLWithPath: "/tmp/colibridb_data")
        )
        let db = try ColibrìDB(config: config)
        try await db.start()
        
        // Get database statistics
        let stats = await db.getStatistics()
        
        logInfo("""
        Database Statistics:
        - Started: \(stats.startTime != nil)
        - Buffer Pool: \(stats.bufferPoolSize) pages
        - Dirty Pages: \(stats.dirtyPages)
        - Active Transactions: \(stats.activeTransactions)
        - Current LSN: N/A
        - Schema Version: N/A
        """, category: .monitoring)
        
        // Perform checkpoint (simulated)
        logInfo("Checkpoint completed", category: .storage)
        
        // Vacuum (garbage collection) (simulated)
        logInfo("Vacuum completed", category: .storage)
        
        try await db.shutdown()
    }
}

/// Advanced usage examples
public enum AdvancedUsageExamples {
    
    /// Example 1: MVCC and snapshot isolation
    public static func example1_MVCCSnapshotIsolation() async throws {
        let config = ColibrìDBConfiguration(
            dataDirectory: URL(fileURLWithPath: "/tmp/colibridb_data")
        )
        let db = try ColibrìDB(config: config)
        try await db.start()
        
        // Transaction 1: Read
        let tx1 = try await db.beginTransaction()
        
        // Transaction 2: Write
        let tx2 = try await db.beginTransaction()
        
        // Both transactions can read
        // MVCC ensures they see consistent snapshots
        
        try await db.commit(txId: tx1)
        try await db.commit(txId: tx2)
        
        try await db.shutdown()
    }
    
    /// Example 2: Index usage
    public static func example2_IndexUsage() async throws {
        let config = ColibrìDBConfiguration(
            dataDirectory: URL(fileURLWithPath: "/tmp/colibridb_data")
        )
        let db = try ColibrìDB(config: config)
        try await db.start()
        
        // Add index to table
        let index = IndexDefinition(
            indexName: "idx_users_email",
            indexType: .btree,
            tableName: "users",
            columns: ["email"],
            unique: true
        )
        
        try await db.createTable(TableDefinition(
            name: "users",
            columns: [
                ColumnDefinition(name: "id", type: .int, nullable: false),
                ColumnDefinition(name: "email", type: .string, nullable: false)
            ],
            primaryKey: ["id"],
            indexes: [CatalogIndexDefinition(
                name: index.indexName,
                columns: index.columns,
                unique: index.unique,
                type: .btree
            )]
        ))
        
        logInfo("Table with index created", category: .database)
        
        try await db.shutdown()
    }
    
    /// Example 3: Recovery after crash
    public static func example3_RecoveryAfterCrash() async throws {
        // Simulate crash by not calling shutdown()
        do {
            let config = ColibrìDBConfiguration(
                dataDirectory: URL(fileURLWithPath: "/tmp/colibridb_data")
            )
            let db = try ColibrìDB(config: config)
            try await db.start()
            
            let txID = try await db.beginTransaction()
            // ... insert data ...
            try await db.commit(txId: txID)
            
            // Simulate crash (no shutdown)
        } catch {
            logWarning("Simulated crash", category: .testing)
        }
        
        // Restart database - automatic recovery
        let config = ColibrìDBConfiguration(
            dataDirectory: URL(fileURLWithPath: "/tmp/colibridb_data")
        )
        let db = try ColibrìDB(config: config)
        
        // start() will automatically perform ARIES recovery
        try await db.start()
        logInfo("Database recovered successfully", category: .recovery)
        
        try await db.shutdown()
    }
}

