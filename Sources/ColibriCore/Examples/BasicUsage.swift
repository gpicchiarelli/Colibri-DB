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
        let config = ColibrìDB.Configuration(
            dataDirectory: URL(fileURLWithPath: "/tmp/colibridb_data"),
            bufferPoolSize: 1000,
            enableWAL: true,
            enableMVCC: true
        )
        
        // Create database instance
        let db = try ColibrìDB(config: config)
        
        // Start the database (performs recovery if needed)
        try await db.start()
        
        print("Database started: \(ColibriDBVersion.fullVersion)")
        
        // Shutdown when done
        try await db.shutdown()
    }
    
    /// Example 2: Create table and insert data
    public static func example2_CreateTableAndInsert() async throws {
        let config = ColibrìDB.Configuration(
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
        print("Table 'users' created")
        
        // Begin transaction
        let txID = try await db.beginTransaction()
        
        // Insert a row
        let row: Row = [
            "id": .int(1),
            "name": .string("Alice"),
            "email": .string("alice@example.com"),
            "created_at": .date(Date())
        ]
        
        let rid = try await db.insert(table: "users", row: row, txID: txID)
        print("Inserted row with RID: \(rid)")
        
        // Commit transaction
        try await db.commit(txID)
        print("Transaction committed")
        
        try await db.shutdown()
    }
    
    /// Example 3: Read and update data
    public static func example3_ReadAndUpdate() async throws {
        let config = ColibrìDB.Configuration(
            dataDirectory: URL(fileURLWithPath: "/tmp/colibridb_data")
        )
        let db = try ColibrìDB(config: config)
        try await db.start()
        
        // Assume we have a RID from previous insert
        let rid = RID(pageID: 1, slotID: 0)
        
        // Begin transaction
        let txID = try await db.beginTransaction(isolationLevel: .repeatableRead)
        
        // Read the row
        let row = try await db.read(rid: rid)
        print("Read row: \(row)")
        
        // Update the row
        var updatedRow = row
        updatedRow["name"] = .string("Alice Updated")
        
        try await db.update(rid: rid, newRow: updatedRow, txID: txID)
        print("Row updated")
        
        // Commit transaction
        try await db.commit(txID)
        
        try await db.shutdown()
    }
    
    /// Example 4: Transaction rollback
    public static func example4_TransactionRollback() async throws {
        let config = ColibrìDB.Configuration(
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
            
            _ = try await db.insert(table: "users", row: row, txID: txID)
            
            // Simulate an error
            throw DBError.internalError("Something went wrong")
            
        } catch {
            // Rollback on error
            print("Error occurred: \(error)")
            try await db.abort(txID)
            print("Transaction rolled back")
        }
        
        try await db.shutdown()
    }
    
    /// Example 5: Query execution
    public static func example5_QueryExecution() async throws {
        let config = ColibrìDB.Configuration(
            dataDirectory: URL(fileURLWithPath: "/tmp/colibridb_data")
        )
        let db = try ColibrìDB(config: config)
        try await db.start()
        
        // Begin transaction
        let txID = try await db.beginTransaction(isolationLevel: .repeatableRead)
        
        // Create a query plan: SELECT * FROM users WHERE id > 0
        let queryPlan: PlanNode = .filter(
            predicate: { row in
                if case .int(let id) = row["id"] {
                    return id > 0
                }
                return false
            },
            child: .scan(table: "users")
        )
        
        // Execute query
        let results = try await db.executeQuery(plan: queryPlan, txID: txID)
        print("Query returned \(results.count) rows")
        
        for row in results {
            print("Row: \(row)")
        }
        
        // Commit transaction
        try await db.commit(txID)
        
        try await db.shutdown()
    }
    
    /// Example 6: Database server
    public static func example6_DatabaseServer() async throws {
        let dbConfig = ColibrìDB.Configuration(
            dataDirectory: URL(fileURLWithPath: "/tmp/colibridb_data")
        )
        
        let serverConfig = DatabaseServer.Configuration(
            host: "127.0.0.1",
            port: 5432,
            maxConnections: 100,
            databaseConfig: dbConfig
        )
        
        let server = try DatabaseServer(config: serverConfig)
        
        // Start the server
        try await server.start()
        print("Server started on \(serverConfig.host):\(serverConfig.port)")
        
        // Accept a connection
        let connection = try await server.acceptConnection(clientID: "client-1")
        
        // Authenticate
        try await connection.authenticate(username: "admin", password: "admin")
        print("Client authenticated")
        
        // Begin transaction
        let txID = try await connection.beginTransaction()
        print("Transaction started: \(txID)")
        
        // Execute query
        let queryPlan: PlanNode = .scan(table: "users")
        let results = try await connection.executeQuery(plan: queryPlan)
        print("Query returned \(results.count) rows")
        
        // Commit
        try await connection.commit()
        print("Transaction committed")
        
        // Close connection
        await connection.close()
        
        // Stop server
        try await server.stop()
    }
    
    /// Example 7: Statistics and monitoring
    public static func example7_StatisticsAndMonitoring() async throws {
        let config = ColibrìDB.Configuration(
            dataDirectory: URL(fileURLWithPath: "/tmp/colibridb_data")
        )
        let db = try ColibrìDB(config: config)
        try await db.start()
        
        // Get database statistics
        let stats = await db.getStatistics()
        
        print("""
        Database Statistics:
        - Started: \(stats.isStarted)
        - Buffer Pool: \(stats.bufferPoolSize) pages
        - Dirty Pages: \(stats.dirtyPages)
        - Active Transactions: \(stats.activeTransactions)
        - Current LSN: \(stats.currentLSN)
        - Schema Version: \(stats.schemaVersion)
        """)
        
        // Perform checkpoint
        try await db.checkpoint()
        print("Checkpoint completed")
        
        // Vacuum (garbage collection)
        await db.vacuum()
        print("Vacuum completed")
        
        try await db.shutdown()
    }
}

/// Advanced usage examples
public enum AdvancedUsageExamples {
    
    /// Example 1: MVCC and snapshot isolation
    public static func example1_MVCCSnapshotIsolation() async throws {
        let config = ColibrìDB.Configuration(
            dataDirectory: URL(fileURLWithPath: "/tmp/colibridb_data")
        )
        let db = try ColibrìDB(config: config)
        try await db.start()
        
        // Transaction 1: Read
        let tx1 = try await db.beginTransaction(isolationLevel: .repeatableRead)
        
        // Transaction 2: Write
        let tx2 = try await db.beginTransaction(isolationLevel: .repeatableRead)
        
        // Both transactions can read
        // MVCC ensures they see consistent snapshots
        
        try await db.commit(tx1)
        try await db.commit(tx2)
        
        try await db.shutdown()
    }
    
    /// Example 2: Index usage
    public static func example2_IndexUsage() async throws {
        let config = ColibrìDB.Configuration(
            dataDirectory: URL(fileURLWithPath: "/tmp/colibridb_data")
        )
        let db = try ColibrìDB(config: config)
        try await db.start()
        
        // Add index to table
        let index = IndexDefinition(
            name: "idx_users_email",
            columns: ["email"],
            unique: true,
            type: .btree
        )
        
        try await db.createTable(TableDefinition(
            name: "users",
            columns: [
                ColumnDefinition(name: "id", type: .int, nullable: false),
                ColumnDefinition(name: "email", type: .string, nullable: false)
            ],
            primaryKey: ["id"],
            indexes: [index]
        ))
        
        print("Table with index created")
        
        try await db.shutdown()
    }
    
    /// Example 3: Recovery after crash
    public static func example3_RecoveryAfterCrash() async throws {
        // Simulate crash by not calling shutdown()
        do {
            let config = ColibrìDB.Configuration(
                dataDirectory: URL(fileURLWithPath: "/tmp/colibridb_data")
            )
            let db = try ColibrìDB(config: config)
            try await db.start()
            
            let txID = try await db.beginTransaction()
            // ... insert data ...
            try await db.commit(txID)
            
            // Simulate crash (no shutdown)
        } catch {
            print("Simulated crash")
        }
        
        // Restart database - automatic recovery
        let config = ColibrìDB.Configuration(
            dataDirectory: URL(fileURLWithPath: "/tmp/colibridb_data")
        )
        let db = try ColibrìDB(config: config)
        
        // start() will automatically perform ARIES recovery
        try await db.start()
        print("Database recovered successfully")
        
        try await db.shutdown()
    }
}

