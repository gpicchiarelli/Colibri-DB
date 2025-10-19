//
//  ColibrìDB.swift
//  ColibrìDB Main Database Engine
//
//  Based on: spec/ColibriDB.tla
//  Implements: Complete database system integration
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//

import Foundation

/// Main ColibrìDB Database Engine
/// Integrates all subsystems: Storage, Transactions, Query, Recovery, Security
/// Corresponds to TLA+ module: ColibriDB.tla
public actor ColibrìDB {
    // MARK: - Configuration
    
    public struct Configuration {
        public let dataDirectory: URL
        public let walDirectory: URL
        public let bufferPoolSize: Int
        public let enableWAL: Bool
        public let enableMVCC: Bool
        
        public init(
            dataDirectory: URL,
            walDirectory: URL? = nil,
            bufferPoolSize: Int = 1000,
            enableWAL: Bool = true,
            enableMVCC: Bool = true
        ) {
            self.dataDirectory = dataDirectory
            self.walDirectory = walDirectory ?? dataDirectory.appendingPathComponent("wal")
            self.bufferPoolSize = bufferPoolSize
            self.enableWAL = enableWAL
            self.enableMVCC = enableMVCC
        }
    }
    
    // MARK: - Core Components
    
    private let config: Configuration
    
    // Storage Layer
    private let wal: FileWAL
    private let diskManager: FileDiskManager
    private let bufferPool: BufferPool
    private let heapTable: HeapTable
    
    // Transaction Layer
    private let mvcc: MVCCManager
    private let lockManager: LockManager
    private let transactionManager: TransactionManager
    
    // Recovery Layer
    private let recovery: ARIESRecovery
    
    // Query Layer
    private let catalog: Catalog
    private let queryExecutor: QueryExecutor
    
    // Security Layer
    private let auth: AuthenticationManager
    
    // State
    private var isStarted: Bool = false
    private var isRecovered: Bool = false
    
    // MARK: - Initialization
    
    public init(config: Configuration) throws {
        self.config = config
        
        // Create directories if needed
        try FileManager.default.createDirectory(at: config.dataDirectory, withIntermediateDirectories: true)
        try FileManager.default.createDirectory(at: config.walDirectory, withIntermediateDirectories: true)
        
        // Initialize WAL
        let walPath = config.walDirectory.appendingPathComponent("wal.log")
        self.wal = try FileWAL(walFilePath: walPath)
        
        // Initialize disk manager
        let dataPath = config.dataDirectory.appendingPathComponent("data.db")
        self.diskManager = try FileDiskManager(filePath: dataPath)
        
        // Initialize buffer pool
        self.bufferPool = BufferPool(poolSize: config.bufferPoolSize, diskManager: diskManager)
        
        // Initialize heap table
        self.heapTable = HeapTable(bufferPool: bufferPool, wal: wal)
        
        // Initialize transaction components
        self.mvcc = MVCCManager()
        self.lockManager = LockManager()
        self.transactionManager = TransactionManager(wal: wal, mvcc: mvcc, lockManager: lockManager)
        
        // Initialize recovery
        self.recovery = ARIESRecovery(wal: wal, bufferPool: bufferPool)
        
        // Initialize catalog
        self.catalog = Catalog()
        
        // Initialize query executor
        self.queryExecutor = QueryExecutor(transactionManager: transactionManager, catalog: catalog)
        
        // Initialize authentication
        self.auth = AuthenticationManager()
    }
    
    // MARK: - Database Lifecycle
    
    /// Start the database
    public func start() async throws {
        guard !isStarted else { return }
        
        print("Starting ColibrìDB...")
        
        // Perform recovery if needed
        if !isRecovered {
            print("Performing recovery...")
            try await recovery.recover()
            isRecovered = true
        }
        
        isStarted = true
        print("ColibrìDB started successfully")
    }
    
    /// Shutdown the database
    public func shutdown() async throws {
        guard isStarted else { return }
        
        print("Shutting down ColibrìDB...")
        
        // Flush all dirty pages
        try await bufferPool.flushAll()
        
        // Flush WAL
        try await wal.flush()
        
        // Checkpoint
        _ = try await wal.checkpoint()
        
        isStarted = false
        print("ColibrìDB shut down successfully")
    }
    
    // MARK: - Transaction API
    
    /// Begin a new transaction
    public func beginTransaction(isolationLevel: IsolationLevel = .repeatableRead) async throws -> TxID {
        guard isStarted else {
            throw DBError.internalError("Database not started")
        }
        
        return try await transactionManager.begin(isolationLevel: isolationLevel)
    }
    
    /// Commit a transaction
    public func commit(_ txID: TxID) async throws {
        try await transactionManager.commit(txID)
    }
    
    /// Abort a transaction
    public func abort(_ txID: TxID) async throws {
        try await transactionManager.abort(txID)
    }
    
    // MARK: - DDL Operations
    
    /// Create table
    public func createTable(_ table: TableDefinition) async throws {
        try await catalog.createTable(table)
    }
    
    /// Drop table
    public func dropTable(_ tableName: String) async throws {
        try await catalog.dropTable(tableName)
    }
    
    /// Get table definition
    public func getTable(_ tableName: String) async -> TableDefinition? {
        return await catalog.getTable(tableName)
    }
    
    /// List all tables
    public func listTables() async -> [String] {
        return await catalog.listTables()
    }
    
    // MARK: - DML Operations
    
    /// Insert row
    public func insert(table: String, row: Row, txID: TxID) async throws -> RID {
        guard isStarted else {
            throw DBError.internalError("Database not started")
        }
        
        return try await heapTable.insert(row, txID: txID)
    }
    
    /// Read row
    public func read(rid: RID) async throws -> Row {
        guard isStarted else {
            throw DBError.internalError("Database not started")
        }
        
        return try await heapTable.read(rid)
    }
    
    /// Update row
    public func update(rid: RID, newRow: Row, txID: TxID) async throws {
        try await heapTable.update(rid, newRow: newRow, txID: txID)
    }
    
    /// Delete row
    public func delete(rid: RID, txID: TxID) async throws {
        try await heapTable.delete(rid, txID: txID)
    }
    
    // MARK: - Query Execution
    
    /// Execute query
    public func executeQuery(plan: QueryPlanNode, txID: TxID) async throws -> [Row] {
        guard isStarted else {
            throw DBError.internalError("Database not started")
        }
        
        return try await queryExecutor.execute(plan: plan, txID: txID)
    }
    
    // MARK: - Authentication
    
    /// Create user
    public func createUser(username: String, password: String) async throws {
        try await auth.createUser(username: username, password: password)
    }
    
    /// Authenticate user
    public func authenticate(username: String, password: String) async throws -> String {
        return try await auth.authenticate(username: username, password: password)
    }
    
    /// Validate session
    public func validateSession(_ token: String) async -> String? {
        return await auth.validateSession(token)
    }
    
    // MARK: - Statistics and Monitoring
    
    /// Get database statistics
    public func getStatistics() async -> DatabaseStatistics {
        let bufferPoolStats = await bufferPool.getStatistics()
        let mvccStats = await mvcc.getActiveTransactionCount()
        let walStats = await wal.getCurrentLSN()
        
        return DatabaseStatistics(
            isStarted: isStarted,
            bufferPoolSize: bufferPoolStats.cachedPages,
            dirtyPages: bufferPoolStats.dirtyPages,
            activeTransactions: mvccStats,
            currentLSN: walStats,
            schemaVersion: await catalog.getSchemaVersion()
        )
    }
    
    // MARK: - Maintenance
    
    /// Perform checkpoint
    public func checkpoint() async throws {
        _ = try await wal.checkpoint()
    }
    
    /// Vacuum (garbage collection)
    public func vacuum() async {
        await mvcc.vacuum()
    }
}

// MARK: - Supporting Types

/// Database statistics
public struct DatabaseStatistics: Sendable {
    public let isStarted: Bool
    public let bufferPoolSize: Int
    public let dirtyPages: Int
    public let activeTransactions: Int
    public let currentLSN: LSN
    public let schemaVersion: Int
}

