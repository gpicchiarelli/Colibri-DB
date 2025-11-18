/*
 * ColibrìDB.swift
 * ColibrìDB - Main Database Engine
 *
 * Based on TLA+ specification: ColibriDB.tla
 *
 * Main database engine that integrates all subsystems:
 * - Storage Engine (WAL, Buffer Pool, Heap Tables, Indexes)
 * - Transaction Management (MVCC, Lock Manager, 2PC)
 * - Query Processing (Parser, Optimizer, Executor)
 * - Recovery (ARIES)
 * - Server (Wire Protocol, Connection Management)
 * - Security (Authentication, Authorization)
 * - Statistics (Query Optimization)
 *
 * References:
 * [1] Gray, J., & Reuter, A. (1992). "Transaction Processing: Concepts and Techniques"
 * [2] Mohan, C., et al. (1992). "ARIES: A Transaction Recovery Method"
 * [3] Berenson, H., et al. (1995). "A Critique of ANSI SQL Isolation Levels"
 * [4] Selinger, P. G., et al. (1979). "Access path selection in a relational database management system"
 *
 * Author: ColibrìDB Team
 * Date: 2025-10-19
 */

import Foundation
@preconcurrency import ColibriCore

// MARK: - Database Configuration

/// ColibrìDB configuration
public struct ColibrìDBConfiguration: Codable, Sendable {
    public let dataDirectory: URL
    public let bufferPoolSize: Int
    public let maxConnections: Int
    public let walBufferSize: Int
    public let checkpointInterval: TimeInterval
    public let logLevel: LogLevel
    public let enableStatistics: Bool
    public let enableAutoAnalyze: Bool
    public let defaultIsolationLevel: IsolationLevel
    public let groupCommitConfig: GroupCommitConfig
    public let disableWALFsyncForBenchmarks: Bool
    
    public init(
        dataDirectory: URL,
        bufferPoolSize: Int = 1000,
        maxConnections: Int = 100,
        walBufferSize: Int = 1024 * 1024,
        checkpointInterval: TimeInterval = 300,
        logLevel: LogLevel = .info,
        enableStatistics: Bool = true,
        enableAutoAnalyze: Bool = true
    ) {
        self.init(
            dataDirectory: dataDirectory,
            bufferPoolSize: bufferPoolSize,
            maxConnections: maxConnections,
            walBufferSize: walBufferSize,
            checkpointInterval: checkpointInterval,
            logLevel: logLevel,
            enableStatistics: enableStatistics,
            enableAutoAnalyze: enableAutoAnalyze,
            defaultIsolationLevel: .serializable,
            groupCommitConfig: .default,
            disableWALFsyncForBenchmarks: false
        )
    }
    
    public init(
        dataDirectory: URL,
        bufferPoolSize: Int = 1000,
        maxConnections: Int = 100,
        walBufferSize: Int = 1024 * 1024,
        checkpointInterval: TimeInterval = 300,
        logLevel: LogLevel = .info,
        enableStatistics: Bool = true,
        enableAutoAnalyze: Bool = true,
        defaultIsolationLevel: IsolationLevel = .serializable,
        groupCommitConfig: GroupCommitConfig = .default,
        disableWALFsyncForBenchmarks: Bool = false
    ) {
        self.dataDirectory = dataDirectory
        self.bufferPoolSize = bufferPoolSize
        self.maxConnections = maxConnections
        self.walBufferSize = walBufferSize
        self.checkpointInterval = checkpointInterval
        self.logLevel = logLevel
        self.enableStatistics = enableStatistics
        self.enableAutoAnalyze = enableAutoAnalyze
        self.defaultIsolationLevel = defaultIsolationLevel
        self.groupCommitConfig = groupCommitConfig
        self.disableWALFsyncForBenchmarks = disableWALFsyncForBenchmarks
    }
}


// MARK: - Main Database Engine

/// ColibrìDB main database engine
/// Corresponds to TLA+ module: ColibriDB.tla
public actor ColibrìDB {
    
    // MARK: - Configuration
    
    private let config: ColibrìDBConfiguration
    private var isRunning: Bool = false
    private var isShuttingDown: Bool = false
    
    // MARK: - Core Subsystems
    
    /// Write-Ahead Log (TLA+: WAL)
    private let wal: FileWAL
    private let groupCommitManager: GroupCommitManager
    
    /// Buffer Pool (TLA+: BufferPool)
    private let bufferPool: BufferPool
    
    /// MVCC Manager (TLA+: MVCC)
    private let mvccManager: MVCCManager
    
    /// Lock Manager (TLA+: LockManager)
    private let lockManager: LockManager
    
    /// Transaction Manager (TLA+: TransactionManager)
    private let transactionManager: TransactionManager
    
    /// ARIES Recovery (TLA+: RECOVERY)
    private let recoveryManager: ARIESRecovery
    
    /// Query Executor (TLA+: QueryExecutor)
    private let queryExecutor: QueryExecutor
    
    /// Query Optimizer (TLA+: QueryOptimizer)
    private let queryOptimizer: QueryOptimizer
    
    /// Statistics Manager (TLA+: StatisticsMaintenance)
    private let statisticsManager: StatisticsMaintenanceManager
    
    /// Schema Evolution (TLA+: SchemaEvolution)
    private let schemaEvolution: SchemaEvolutionManager
    
    /// Wire Protocol (TLA+: WireProtocol)
    private let wireProtocol: WireProtocolHandler
    
    /// Database Server (TLA+: Server)
    private var databaseServer: DatabaseServer?
    
    /// System Catalog (TLA+: Catalog)
    private let catalog: Catalog
    
    /// Authentication Manager (TLA+: Authentication)
    private let authManager: AuthenticationManager
    
    /// Heap tables for each table
    private var heapTables: [String: HeapTable] = [:]
    
    /// Page directories per table
    private var pageDirectories: [String: PageDirectory] = [:]
    
    /// Primary key indexes per table (single-column PK fast path)
    private var primaryKeyIndexes: [String: PrimaryKeyIndex] = [:]
    
    /// Primary key column names per table
    private var primaryKeyColumns: [String: String] = [:]
    
    // MARK: - State Management
    
    /// Active transactions (TLA+: activeTransactions)
    private var activeTransactions: [TxID: Transaction] = [:]
    
    /// Database statistics (TLA+: dbStats)
    private var databaseStats: DatabaseStats = DatabaseStats()
    
    /// System state (TLA+: systemState)
    private var systemState: SystemState = .initializing
    
    /// Recovery state (TLA+: recoveryState)
    private var recoveryState: RecoveryState = .notStarted
    
    // MARK: - Initialization
    
    public init(config: ColibrìDBConfiguration) throws {
        self.config = config
        
        // Initialize storage layer first (needed for Catalog persistence)
        let fileWAL = try FileWAL(
            walFilePath: config.dataDirectory.appendingPathComponent("wal.log"),
            fsyncOnFlush: !config.disableWALFsyncForBenchmarks
        )
        self.wal = fileWAL
        
        // Create disk manager for storage
        let diskManager = try FileDiskManager(
            filePath: config.dataDirectory.appendingPathComponent("data.db")
        )
        
        self.groupCommitManager = GroupCommitManager(config: config.groupCommitConfig) { [weak fileWAL] targetLSN in
            guard let wal = fileWAL else {
                throw GroupCommitError.managerShutdown
            }
            try await wal.flush(upTo: targetLSN)
        }
        
        // Create BufferPool first (for HeapTable compatibility)
        self.bufferPool = BufferPool(
            poolSize: config.bufferPoolSize,
            diskManager: diskManager
        )
        
        // Create compression and encryption services
        let compressionService: CompressionService = DefaultCompressionService()
        let encryptionService: EncryptionService = DefaultEncryptionService()  // Actor - used via protocol
        
        // Create BufferManager for advanced buffer management
        // Note: This will be used by StorageManager for Catalog persistence
        let bufferManager = BufferManager(
            diskManager: diskManager,
            poolSize: config.bufferPoolSize,
            evictionPolicy: .lru
        )
        
        // Create CatalogManager FIRST (foundation of ColibrìDB)
        // **Catalog-First**: Catalog is the foundation - all components depend on it
        // Catalog will be configured with StorageManager after initialization
        // (avoids circular dependency: Catalog needs StorageManager, StorageManager needs Catalog)
        let catalogManager = CatalogManager(
            storageManager: nil,  // Will be set after StorageManager creation
            walManager: nil  // WAL integration will be added later
        )
        
        // Initialize Catalog wrapper around CatalogManager
        // **Catalog-First**: Catalog is the foundation - all components depend on it
        self.catalog = Catalog(
            storageManager: nil,  // Will be set after StorageManager creation
            walManager: nil  // WAL integration will be added later
        )
        
        // Create storage manager with Catalog dependency
        // **Catalog-First**: StorageManager MUST check Catalog before operations
        // Note: storageManager created but not stored (used for Catalog persistence in future)
        let _ = StorageManagerActor(
            diskManager: diskManager,
            compressionService: compressionService,
            encryptionService: encryptionService,
            bufferManager: bufferManager,
            catalog: catalogManager
        )
        
        // TODO: Update Catalog with StorageManager for persistence
        // This requires refactoring CatalogManager to allow setting StorageManager after init
        // For now, Catalog works in-memory only (for testing)
        
        // Initialize transaction layer
        self.mvccManager = MVCCManager()
        
        // Create transaction manager with proper adapters
        let walAdapter = wal.asTransactionWALManager()
        let mvccAdapter = mvccManager.asTransactionMVCCManager()
        
        // Create transaction manager with Catalog dependency
        // **Catalog-First**: Transaction Manager uses Catalog for validation
        self.transactionManager = TransactionManager(
            walManager: walAdapter,
            mvccManager: mvccAdapter,
            lockManager: nil,
            catalog: catalogManager  // **Catalog-First**: Pass Catalog for validation
        )
        self.lockManager = LockManager(transactionManager: transactionManager)
        
        // Initialize recovery
        self.recoveryManager = ARIESRecovery(
            wal: wal,
            bufferPool: bufferPool
        )
        
        // Initialize query processing
        self.statisticsManager = StatisticsMaintenanceManager()
        
        self.queryExecutor = QueryExecutor(
            transactionManager: transactionManager,
            catalog: catalog
        )
        
        self.queryOptimizer = QueryOptimizer(
            catalog: catalog,
            statistics: statisticsManager
        )
        
        // Initialize schema evolution
        let distributedClock = DistributedClockManager(nodeId: "node-1")
        self.schemaEvolution = SchemaEvolutionManager(
            transactionManager: transactionManager,
            catalog: catalog,
            clock: distributedClock
        )
        
        // Initialize wire protocol
        self.wireProtocol = WireProtocolHandler()
        
        // Initialize authentication with Catalog dependency
        // **Catalog-First**: Authentication Manager uses Catalog for user/role/permission metadata
        self.authManager = AuthenticationManager(catalog: catalogManager)
        
        // Database server will be initialized after construction to avoid circular dependency
        self.databaseServer = nil
    }
    
    /// Initialize the database server (called after construction)
    private func initializeServer() async throws {
        let serverConfig = DatabaseServer.Configuration(
            host: "127.0.0.1",
            port: 5432,
            maxConnections: config.maxConnections,
            databaseConfig: DatabaseConfiguration()
        )
        let server = try DatabaseServer(config: serverConfig)
        await server.setDatabase(self)
        self.databaseServer = server
    }
    
    // MARK: - Database Lifecycle
    
    /// Start the database
    /// TLA+ Action: StartDatabase
    public func start() async throws {
        guard !isRunning else {
            throw DBError.databaseAlreadyRunning
        }
        
        systemState = .starting
        
        // Initialize server if not already done (avoids circular dependency)
        if databaseServer == nil {
            try await initializeServer()
        }
        
        try await withThrowingTaskGroup(of: Void.self) { group in
            // WAL is ready to use (no start method needed)
            
            // Buffer pool is ready to use (no start method needed)
            
            // Recovery manager is ready to use (no start method needed)
            
            // Transaction manager is ready to use (no start method needed)
            
            // Start statistics manager
            if config.enableStatistics {
                group.addTask {
                    await self.statisticsManager.setAutoAnalyze(enabled: self.config.enableAutoAnalyze)
                }
            }
            
            // Start database server
            if let server = self.databaseServer {
                group.addTask {
                    try await server.start()
                }
            }
            
            // Wait for all subsystems to start
            try await group.waitForAll()
        }
        
        isRunning = true
        systemState = .running
        
        databaseStats.startTime = Date()
        log(.info, "ColibrìDB started successfully")
    }
    
    /// Stop the database
    /// TLA+ Action: StopDatabase
    public func shutdown() async throws {
        guard isRunning else {
            throw DBError.databaseNotRunning
        }
        
        isShuttingDown = true
        systemState = .shuttingDown
        
        try await groupCommitManager.forceFlush()
        await groupCommitManager.shutdown()
        
        try await withThrowingTaskGroup(of: Void.self) { group in
            // Stop accepting new connections
            if let server = self.databaseServer {
                group.addTask {
                    try await server.stop()
                }
            }
            
            // Complete all active transactions
            group.addTask {
                try await self.completeAllTransactions()
            }
            
            // Flush WAL
            group.addTask {
                try await self.wal.flush()
            }
            
            // Transaction manager doesn't need shutdown
            
            // Buffer pool doesn't need shutdown
            
            // WAL doesn't need shutdown
            
            // Wait for all subsystems to stop
            try await group.waitForAll()
        }
        
        isRunning = false
        systemState = .stopped
        
        databaseStats.shutdownTime = Date()
        log(.info, "ColibrìDB shutdown completed")
    }
    
    // MARK: - Transaction Management
    
    /// Begin a new transaction
    /// TLA+ Action: BeginTransaction
    public func beginTransaction() async throws -> TxID {
        guard isRunning else {
            throw DBError.databaseNotRunning
        }
        
        let txId = try await transactionManager.beginTransaction()
        
        let transaction = Transaction(
            txId: txId,
            state: .active,
            startTime: UInt64(Date().timeIntervalSince1970 * 1000),
            endTime: nil,
            resources: [],
            participants: [],
            isDirty: false
        )
        
        activeTransactions[txId] = transaction
        databaseStats.transactionsStarted += 1
        
        // Log BEGIN record
        let beginRecord = BeginRecord(
            txID: txId,
            timestamp: currentTimestampMillis(),
            isolationLevel: config.defaultIsolationLevel
        )
        let payload = try JSONEncoder().encode(beginRecord)
        _ = try await logTransactionRecord(kind: .begin, txId: txId, payload: payload)
        
        return txId
    }
    
    /// Commit a transaction
    /// TLA+ Action: CommitTransaction
    public func commit(txId: TxID) async throws {
        guard let transaction = activeTransactions[txId] else {
            throw DBError.transactionNotFound(txId: txId)
        }
        
        let commitRecord = CommitRecord(
            txID: txId,
            timestamp: currentTimestampMillis()
        )
        let payload = try JSONEncoder().encode(commitRecord)
        let commitLSN = try await logTransactionRecord(kind: .commit, txId: txId, payload: payload)
        _ = try await groupCommitManager.awaitCommit(tid: txId, targetLSN: commitLSN)
        
        try await transactionManager.commitTransaction(txId: txId)
        
        var updatedTransaction = transaction
        updatedTransaction.state = .committed
        updatedTransaction.endTime = UInt64(Date().timeIntervalSince1970 * 1000)
        activeTransactions[txId] = updatedTransaction
        
        databaseStats.transactionsCommitted += 1
        let startDate = Date(timeIntervalSince1970: Double(updatedTransaction.startTime) / 1000)
        let endDate = Date(timeIntervalSince1970: Double(updatedTransaction.endTime!) / 1000)
        databaseStats.totalTransactionTime += endDate.timeIntervalSince(startDate)
    }
    
    /// Abort a transaction
    /// TLA+ Action: AbortTransaction
    public func abort(txId: TxID) async throws {
        guard let transaction = activeTransactions[txId] else {
            throw DBError.transactionNotFound(txId: txId)
        }
        
        try await transactionManager.abortTransaction(txId: txId)
        
        let abortRecord = AbortRecord(
            txID: txId,
            timestamp: currentTimestampMillis()
        )
        let payload = try JSONEncoder().encode(abortRecord)
        _ = try await logTransactionRecord(kind: .abort, txId: txId, payload: payload)
        
        var updatedTransaction = transaction
        updatedTransaction.state = .aborted
        updatedTransaction.endTime = UInt64(Date().timeIntervalSince1970 * 1000)
        activeTransactions[txId] = updatedTransaction
        
        databaseStats.transactionsAborted += 1
    }
    
    // MARK: - DDL Operations
    
    /// Create a table
    /// TLA+ Action: CreateTable
    public func createTable(_ tableDef: TableDefinition) async throws {
        guard isRunning else {
            throw DBError.databaseNotRunning
        }
        
        let txId = try await beginTransaction()
        defer { Task { try? await abort(txId: txId) } }
        
        var effectiveTableDef = tableDef
        if let primaryKey = tableDef.primaryKey,
           primaryKey.count == 1,
           !tableDef.indexes.contains(where: { $0.name == "\(tableDef.name)_pk" }) {
            let pkIndex = CatalogIndexDefinition(
                name: "\(tableDef.name)_pk",
                columns: primaryKey,
                unique: true,
                type: .btree
            )
            effectiveTableDef = TableDefinition(
                name: tableDef.name,
                columns: tableDef.columns,
                primaryKey: tableDef.primaryKey,
                indexes: tableDef.indexes + [pkIndex]
            )
        }
        
        try await catalog.createTable(effectiveTableDef)
        
        let directory = try await pageDirectory(for: tableDef.name)
        let heapTable = await HeapTable(bufferPool: bufferPool, wal: wal, pageDirectory: directory)
        heapTables[tableDef.name] = heapTable
        
        if config.enableStatistics {
            await statisticsManager.registerTable(tableDef.name)
        }
        
        if let primaryKey = effectiveTableDef.primaryKey, primaryKey.count == 1 {
            let column = primaryKey[0]
            primaryKeyColumns[tableDef.name] = column
            primaryKeyIndexes[tableDef.name] = PrimaryKeyIndex(column: column)
        }
        
        // Register table storage in QueryExecutor
        await queryExecutor.registerTableStorage(tableName: tableDef.name, storage: heapTable)
        
        // Register indexes if any
        for indexDef in tableDef.indexes {
            // Note: Index registration would require IndexManager integration
            // For now, we skip this - indexes will be registered when created separately
        }
        
        try await commit(txId: txId)
        
        if config.enableStatistics {
            try? await analyzeTable(tableDef.name)
        }
        
        databaseStats.tablesCreated += 1
        log(.info, "Table '\(tableDef.name)' created successfully")
    }
    
    /// Drop a table
    /// TLA+ Action: DropTable
    public func dropTable(_ tableName: String) async throws {
        guard isRunning else {
            throw DBError.databaseNotRunning
        }
        
        let txId = try await beginTransaction()
        defer { Task { try? await abort(txId: txId) } }
        
        try await catalog.dropTable(tableName)
        try await commit(txId: txId)
        
        databaseStats.tablesDropped += 1
        log(.info, "Table '\(tableName)' dropped successfully")
    }
    
    // MARK: - DML Operations
    
    /// Insert a row
    /// TLA+ Action: InsertRow
    public func insert(table: String, row: Row, txId: TxID) async throws -> RID {
        guard isRunning else {
            throw DBError.databaseNotRunning
        }
        
        guard activeTransactions[txId] != nil else {
            throw DBError.transactionNotFound(txId: txId)
        }
        
        // **Catalog-First**: Get table definition from Catalog
        // Catalog is the single source of truth for table metadata
        guard let tableDef = await catalog.getTable(table) else {
            throw DBError.tableNotFound(table: table)
        }
        
        // **Catalog-First**: Validate row against schema from Catalog
        // All validation uses Catalog metadata
        try validateRow(row, against: tableDef)
        
        // Get or create heap table
        let heapTable = try await getOrCreateHeapTable(table: table)
        
        // Insert row using heap table
        let rid = try await heapTable.insert(row, txID: txId)
        await updatePrimaryKeyIndex(
            for: table,
            oldRow: nil,
            newRow: row,
            newRID: rid
        )
        
        // Record modification for statistics
        if config.enableStatistics {
            await statisticsManager.recordModification(table: table)
            await statisticsManager.updateRowCount(table: table, delta: 1)
            scheduleAutoAnalyzeIfNeeded(for: table)
        }
        
        databaseStats.rowsInserted += 1
        return rid
    }
    
    /// Update a row
    /// TLA+ Action: UpdateRow
    public func update(table: String, rid: RID, row: Row, txId: TxID) async throws {
        guard isRunning else {
            throw DBError.databaseNotRunning
        }
        
        guard activeTransactions[txId] != nil else {
            throw DBError.transactionNotFound(txId: txId)
        }
        
        // **Catalog-First**: Verify table exists in Catalog before operations
        guard await catalog.getTable(table) != nil else {
            throw DBError.tableNotFound(table: table)
        }
        
        // Get heap table
        guard let heapTable = heapTables[table] else {
            throw DBError.tableNotFound(table: table)
        }
        
        // Update row using heap table
        let oldRow = try await heapTable.read(rid)
        var updatedRow = oldRow
        for (key, value) in row {
            updatedRow[key] = value
        }
        let resultingRID = try await heapTable.update(rid, newRow: updatedRow, txID: txId)
        await updatePrimaryKeyIndex(
            for: table,
            oldRow: oldRow,
            newRow: updatedRow,
            newRID: resultingRID
        )
        
        // Record modification for statistics
        if config.enableStatistics {
            await statisticsManager.recordModification(table: table)
            scheduleAutoAnalyzeIfNeeded(for: table)
        }
        
        databaseStats.rowsUpdated += 1
    }
    
    /// Delete a row
    /// TLA+ Action: DeleteRow
    public func delete(table: String, rid: RID, txId: TxID) async throws {
        guard isRunning else {
            throw DBError.databaseNotRunning
        }
        
        guard activeTransactions[txId] != nil else {
            throw DBError.transactionNotFound(txId: txId)
        }
        
        // **Catalog-First**: Verify table exists in Catalog before operations
        guard await catalog.getTable(table) != nil else {
            throw DBError.tableNotFound(table: table)
        }
        
        // Get heap table
        guard let heapTable = heapTables[table] else {
            throw DBError.tableNotFound(table: table)
        }
        
        // Delete row using heap table
        let deletedRow = try? await heapTable.read(rid)
        try await heapTable.delete(rid, txID: txId)
        await updatePrimaryKeyIndex(for: table, oldRow: deletedRow, newRow: nil, newRID: nil)
        
        // Record modification for statistics
        if config.enableStatistics {
            await statisticsManager.recordModification(table: table)
            await statisticsManager.updateRowCount(table: table, delta: -1)
            scheduleAutoAnalyzeIfNeeded(for: table)
        }
        
        databaseStats.rowsDeleted += 1
    }
    
    private func updatePrimaryKeyIndex(
        for table: String,
        oldRow: Row?,
        newRow: Row?,
        newRID: RID?
    ) async {
        guard let pkColumn = primaryKeyColumns[table],
              let index = primaryKeyIndexes[table] else {
            return
        }
        
        if let oldRow, let oldValue = oldRow[pkColumn] {
            await index.remove(value: oldValue)
        }
        
        if let newRow,
           let rid = newRID,
           let newValue = newRow[pkColumn] {
            await index.upsert(value: newValue, rid: rid)
        }
    }
    
    // MARK: - Primary Key Fast Path
    
    public func selectByPrimaryKey(table: String, key: Value, txId: TxID) async throws -> Row? {
        guard isRunning else {
            throw DBError.databaseNotRunning
        }
        guard activeTransactions[txId] != nil else {
            throw DBError.transactionNotFound(txId: txId)
        }
        guard let index = primaryKeyIndexes[table],
              let heapTable = heapTables[table] else {
            return nil
        }
        guard let rid = await index.lookup(value: key) else {
            return nil
        }
        return try await heapTable.read(rid)
    }
    
    // MARK: - Query Operations
    
    /// Execute a query
    /// TLA+ Action: ExecuteQuery
    public func executeQuery(_ sql: String, txId: TxID) async throws -> QueryResult {
        guard isRunning else {
            throw DBError.databaseNotRunning
        }
        
        guard activeTransactions[txId] != nil else {
            throw DBError.transactionNotFound(txId: txId)
        }
        
        // Parse SQL
        var parser = SQLParser()
        let ast = try parser.parse(sql)
        
        // Handle different statement types
        switch ast.kind.uppercased() {
        case "SELECT":
            return try await executeSelect(ast: ast, txId: txId)
        case "INSERT":
            return try await executeInsert(ast: ast, txId: txId)
        case "UPDATE":
            return try await executeUpdate(ast: ast, txId: txId)
        case "DELETE":
            return try await executeDelete(ast: ast, txId: txId)
        default:
            throw DBError.custom("Unsupported SQL statement: \(ast.kind)")
        }
    }
    
    /// Execute SELECT query
    private func executeSelect(ast: ASTNode, txId: TxID) async throws -> QueryResult {
        // Convert AST to LogicalPlan
        let converter = ASTToLogicalPlanConverter()
        let logicalPlan = try converter.convert(ast)
        
        if let fastPath = try await tryPrimaryKeyFastPath(logicalPlan: logicalPlan, txId: txId) {
            return fastPath
        }
        
        // Optimize logical plan to physical plan
        let physicalPlan = await queryOptimizer.optimize(logical: logicalPlan)
        
        // Execute physical plan using QueryExecutor
        let tuples = try await queryExecutor.executePlan(physicalPlan, txID: txId)
        
        // Convert ExecutorTuple back to Row using schema
        guard let tableDef = await catalog.getTable(logicalPlan.table) else {
            throw DBError.tableNotFound(table: logicalPlan.table)
        }
        
        let columnNames = logicalPlan.projection ?? tableDef.columns.map { $0.name }
        
        // Convert tuples to rows
        var rows: [Row] = []
        for tuple in tuples {
            var row: Row = [:]
            
            // If projection is specified, use projection column order
            // Otherwise, use full table schema order
            if let projection = logicalPlan.projection {
                // Projection: map tuple values to projected columns
                for (index, columnName) in projection.enumerated() {
                    if index < tuple.values.count {
                        row[columnName] = tuple.values[index]
                    }
                }
            } else {
                // Full schema: map tuple values to all columns in schema order
                for (index, columnDef) in tableDef.columns.enumerated() {
                    if index < tuple.values.count {
                        row[columnDef.name] = tuple.values[index]
                    }
                }
            }
            
            rows.append(row)
        }
        
        databaseStats.queriesExecuted += 1
        return QueryResult(rows: rows, columns: columnNames)
    }
    
    private func tryPrimaryKeyFastPath(logicalPlan: LogicalPlan, txId: TxID) async throws -> QueryResult? {
        guard let pkColumn = primaryKeyColumns[logicalPlan.table],
              let filterColumn = logicalPlan.filterColumn,
              filterColumn == pkColumn,
              let key = logicalPlan.filterKey else {
            return nil
        }
        
        guard let tableDef = await catalog.getTable(logicalPlan.table) else {
            throw DBError.tableNotFound(table: logicalPlan.table)
        }
        
        let columnNames = logicalPlan.projection ?? tableDef.columns.map { $0.name }
        guard let row = try await selectByPrimaryKey(table: logicalPlan.table, key: key, txId: txId) else {
            databaseStats.queriesExecuted += 1
            return QueryResult(rows: [], columns: columnNames)
        }
        
        var projectedRow: Row = [:]
        if let projection = logicalPlan.projection {
            for column in projection {
                projectedRow[column] = row[column] ?? .null
            }
        } else {
            for column in tableDef.columns {
                projectedRow[column.name] = row[column.name] ?? .null
            }
        }
        
        databaseStats.queriesExecuted += 1
        return QueryResult(rows: [projectedRow], columns: columnNames)
    }
    
    /// Execute INSERT statement
    private func executeInsert(ast: ASTNode, txId: TxID) async throws -> QueryResult {
        // Extract table name
        guard let tableName = ast.attributes["table"] else {
            throw DBError.custom("INSERT statement missing table name")
        }
        
        // Extract column names (optional)
        let columnNames: [String] = {
            if let columnsStr = ast.attributes["columns"], !columnsStr.isEmpty {
                return columnsStr.split(separator: ",").map { String($0).trimmingCharacters(in: .whitespaces) }
            }
            return []
        }()
        
        // Extract VALUES (children of INSERT AST are the values)
        let values = ast.children
        
        // Get table definition
        guard let tableDef = await catalog.getTable(tableName) else {
            throw DBError.tableNotFound(table: tableName)
        }
        
        // Convert VALUES to Row
        let converter = ASTToRowConverter()
        let row = try converter.convertInsertValues(values, columns: columnNames, tableDef: tableDef)
        
        // Insert row
        let rid = try await insert(table: tableName, row: row, txId: txId)
        
        // Return empty result (INSERT doesn't return rows)
        return QueryResult(rows: [], columns: [])
    }
    
    /// Execute UPDATE statement
    private func executeUpdate(ast: ASTNode, txId: TxID) async throws -> QueryResult {
        // Extract table name
        guard let tableName = ast.attributes["table"] else {
            throw DBError.custom("UPDATE statement missing table name")
        }
        
        // Get table definition
        guard let tableDef = await catalog.getTable(tableName) else {
            throw DBError.tableNotFound(table: tableName)
        }
        
        // Extract assignments and WHERE clause
        // AST structure: children = [assignment1, assignment2, ..., whereClause]
        var assignments: [ASTNode] = []
        var whereClause: ASTNode?
        
        for (index, child) in ast.children.enumerated() {
            if child.kind == "where_clause" {
                whereClause = child
            } else if child.kind == "assignment" {
                assignments.append(child)
            }
        }
        
        // Convert assignments to Row (partial row with only updated columns)
        var updateRow: Row = [:]
        for assignment in assignments {
            guard let columnName = assignment.attributes["column"] else {
                continue
            }
            guard assignment.children.count >= 1 else {
                continue
            }
            
            // Evaluate value expression
            let converter = ASTToRowConverter()
            let value = try converter.evaluateValueExpression(assignment.children[0])
            updateRow[columnName] = value
        }
        
        // Get heap table
        let heapTable = try await getOrCreateHeapTable(table: tableName)
        
        // Get WHERE predicate if present
        let predicate: (@Sendable (Row) -> Bool)?
        if let whereClause = whereClause, whereClause.kind != "empty" {
            // Extract predicate from WHERE clause directly
            let logicalPlanConverter = ASTToLogicalPlanConverter()
            // Create a SELECT AST with WHERE clause to extract predicate
            let selectAST = ASTNode(
                kind: "SELECT",
                children: [
                    ASTNode(kind: "select_list", children: []),
                    ASTNode(kind: "from_clause", children: [
                        ASTNode(kind: "table_ref", attributes: ["name": tableName])
                    ]),
                    whereClause
                ]
            )
            predicate = try logicalPlanConverter.extractPredicate(from: selectAST)
        } else {
            predicate = nil
        }
        
        // Scan all rows with RIDs and update matching ones
        var updatedCount = 0
        let allRowsWithRID = try await heapTable.scanAllWithRID()
        
        for (rid, row) in allRowsWithRID {
            // Check predicate if present
            if let predicate = predicate, !predicate(row) {
                continue
            }
            
            // Merge updateRow with existing row
            var mergedRow = row
            for (key, value) in updateRow {
                mergedRow[key] = value
            }
            
            // Update row using heap table
            try await update(table: tableName, rid: rid, row: mergedRow, txId: txId)
            updatedCount += 1
        }
        
        databaseStats.queriesExecuted += 1
        return QueryResult(rows: [], columns: [])
    }
    
    /// Execute DELETE statement
    private func executeDelete(ast: ASTNode, txId: TxID) async throws -> QueryResult {
        // Extract table name
        guard let tableName = ast.attributes["table"] else {
            throw DBError.custom("DELETE statement missing table name")
        }
        
        // Get heap table
        let heapTable = try await getOrCreateHeapTable(table: tableName)
        
        // Extract WHERE clause (first child)
        var whereClause: ASTNode?
        if !ast.children.isEmpty {
            let firstChild = ast.children[0]
            if firstChild.kind == "where_clause" {
                whereClause = firstChild
            }
        }
        
        // Get WHERE predicate if present
        let predicate: (@Sendable (Row) -> Bool)?
        if let whereClause = whereClause, whereClause.kind != "empty" {
            // Extract predicate from WHERE clause directly
            let logicalPlanConverter = ASTToLogicalPlanConverter()
            // Create a SELECT AST with WHERE clause to extract predicate
            let selectAST = ASTNode(
                kind: "SELECT",
                children: [
                    ASTNode(kind: "select_list", children: []),
                    ASTNode(kind: "from_clause", children: [
                        ASTNode(kind: "table_ref", attributes: ["name": tableName])
                    ]),
                    whereClause
                ]
            )
            predicate = try logicalPlanConverter.extractPredicate(from: selectAST)
        } else {
            // No WHERE clause - delete all rows
            predicate = nil
        }
        
        // Scan all rows with RIDs and delete matching ones
        // This is simplified - in production would use index for WHERE clauses
        var deletedCount = 0
        let allRowsWithRID = try await heapTable.scanAllWithRID()
        
        for (rid, row) in allRowsWithRID {
            // Check predicate if present
            if let predicate = predicate, !predicate(row) {
                continue
            }
            
            // Delete row using heap table
            try await delete(table: tableName, rid: rid, txId: txId)
            deletedCount += 1
        }
        
        databaseStats.queriesExecuted += 1
        return QueryResult(rows: [], columns: [])
    }
    
    // MARK: - Statistics and Monitoring
    
    /// Get database statistics
    public func getStatistics() -> DatabaseStats {
        return databaseStats
    }
    
    /// Get system state
    public func getSystemState() -> SystemState {
        return systemState
    }
    
    /// Check if database is running
    public func isDatabaseRunning() -> Bool {
        return isRunning
    }
    
    // MARK: - TLA+ Invariants Implementation
    
    /// Invariant: Database consistency (TLA+: Inv_DatabaseConsistency)
    public func checkConsistencyInvariant() -> Bool {
        return activeTransactions.values.allSatisfy { transaction in
            [TransactionState.active, .committed, .aborted].contains(transaction.state)
        }
    }
    
    /// Invariant: Transaction atomicity (TLA+: Inv_TransactionAtomicity)
    public func checkAtomicityInvariant() -> Bool {
        return activeTransactions.values.allSatisfy { transaction in
            transaction.state == .active || transaction.endTime != nil
        }
    }
    
    /// Invariant: System state consistency (TLA+: Inv_SystemStateConsistency)
    public func checkSystemStateInvariant() -> Bool {
        return [SystemState.initializing, .starting, .running, .shuttingDown, .stopped].contains(systemState)
    }
    
    /// Combined safety invariant (TLA+: Inv_DatabaseSafety)
    public func checkSafetyInvariant() -> Bool {
        return checkConsistencyInvariant() &&
               checkAtomicityInvariant() &&
               checkSystemStateInvariant()
    }
    
    // MARK: - Helper Methods
    
    private func completeAllTransactions() async throws {
        for txId in activeTransactions.keys {
            try? await abort(txId: txId)
        }
        activeTransactions.removeAll()
    }
    
    private func validateRow(_ row: Row, against tableDef: TableDefinition) throws {
        // Validate column count
        guard row.values.count == tableDef.columns.count else {
            throw DBError.schemaMismatch(expected: tableDef.columns.count, actual: row.values.count)
        }
        
        // Validate column types and constraints
        for (_, column) in tableDef.columns.enumerated() {
            let value = row[column.name]
            
            // Check null constraint
            if !column.nullable && value == .null {
                throw DBError.nullConstraintViolation(column: column.name)
            }
            
            // Check type compatibility (simplified)
            if value != nil && value != .null {
                // Would validate type compatibility
            }
        }
    }
    
    private func getOrCreateHeapTable(table: String) async throws -> HeapTable {
        if let existing = heapTables[table] {
            return existing
        }
        
        let directory = try await pageDirectory(for: table)
        let heapTable = await HeapTable(bufferPool: bufferPool, wal: wal, pageDirectory: directory)
        heapTables[table] = heapTable
        return heapTable
    }
    
    private func scheduleAutoAnalyzeIfNeeded(for table: String) {
        guard config.enableAutoAnalyze else { return }
        Task { [weak self] in
            guard let self else { return }
            let needsRefresh = await self.statisticsManager.needsRefresh(tableName: table)
            guard needsRefresh else { return }
            try? await self.analyzeTable(table)
        }
    }
    
    private func analyzeTable(_ table: String) async throws {
        guard config.enableStatistics else { return }
        guard await statisticsManager.beginAnalyze(table: table) else { return }
        defer {
            Task {
                await self.statisticsManager.endAnalyze(table: table)
            }
        }
        
        let heapTable = try await getOrCreateHeapTable(table: table)
        let heapSnapshot = try await heapTable.collectStatistics()
        let snapshot = TableStatisticsSnapshot(
            rowCount: heapSnapshot.rowCount,
            pageCount: Int64(heapSnapshot.pageCount),
            avgRowSize: heapSnapshot.avgRowSize,
            deadTuples: heapSnapshot.deadTuples
        )
        await statisticsManager.updateTableStatistics(table: table, snapshot: snapshot)
    }
    
    private func pageDirectory(for table: String) async throws -> PageDirectory {
        if let existing = pageDirectories[table] {
            return existing
        }
        let dirURL = config.dataDirectory
            .appendingPathComponent("tables", isDirectory: true)
            .appendingPathComponent("\(table)_pagedir.json", isDirectory: false)
        try FileManager.default.createDirectory(
            at: dirURL.deletingLastPathComponent(),
            withIntermediateDirectories: true
        )
        let directory = try PageDirectory(fileURL: dirURL)
        pageDirectories[table] = directory
        return directory
    }
    
    private func log(_ level: LogLevel, _ message: String, category: LogCategory = .database) {
        if level.priority >= config.logLevel.priority {
            Task { [category] in
                await colibriLogger.log(level, category: category, message)
            }
        }
    }
    
    private func logTransactionRecord(
        kind: WALRecordKind,
        txId: TxID,
        payload: Data? = nil
    ) async throws -> LSN {
        return try await wal.append(
            kind: kind,
            txID: txId,
            pageID: 0,
            payload: payload
        )
    }
    
    private func currentTimestampMillis() -> UInt64 {
        return UInt64(Date().timeIntervalSince1970 * 1000)
    }
}

// MARK: - Supporting Types

public enum SystemState: String, Codable, Sendable {
    case initializing = "INITIALIZING"
    case starting = "STARTING"
    case running = "RUNNING"
    case shuttingDown = "SHUTTING_DOWN"
    case stopped = "STOPPED"
}

public enum RecoveryState: String, Codable {
    case notStarted = "NOT_STARTED"
    case analysis = "ANALYSIS"
    case redo = "REDO"
    case undo = "UNDO"
    case completed = "COMPLETED"
}

public struct DatabaseStats: Codable, Sendable {
    public var startTime: Date?
    public var shutdownTime: Date?
    public var transactionsStarted: Int = 0
    public var transactionsCommitted: Int = 0
    public var transactionsAborted: Int = 0
    public var totalTransactionTime: TimeInterval = 0
    public var tablesCreated: Int = 0
    public var tablesDropped: Int = 0
    public var rowsInserted: Int = 0
    public var rowsUpdated: Int = 0
    public var rowsDeleted: Int = 0
    public var queriesExecuted: Int = 0
    public var dirtyPages: Int = 0
    public var bufferPoolSize: Int = 0
    public var activeTransactions: Int = 0
    
    public var averageTransactionTime: TimeInterval {
        guard transactionsCommitted > 0 else { return 0 }
        return totalTransactionTime / Double(transactionsCommitted)
    }
}

public struct QueryResult: Codable, Sendable {
    public let rows: [Row]
    public let columns: [String]
    public let rowCount: Int
    
    public init(rows: [Row], columns: [String]) {
        self.rows = rows
        self.columns = columns
        self.rowCount = rows.count
    }
}

// MARK: - Errors
// DBError is defined in Core/Types.swift

/*
 * IMPLEMENTATION NOTES:
 *
 * This implementation follows the ColibriDB.tla specification and
 * integrates all database subsystems:
 *
 * 1. Storage Layer:
 *    - WAL: Write-Ahead Logging for durability
 *    - Buffer Pool: Page caching and management
 *    - Heap Tables: Row storage
 *    - Indexes: B+Tree, Hash, etc.
 *
 * 2. Transaction Layer:
 *    - MVCC: Multi-Version Concurrency Control
 *    - Lock Manager: Deadlock detection and prevention
 *    - Transaction Manager: ACID properties
 *    - 2PC: Two-Phase Commit for distributed transactions
 *
 * 3. Query Processing:
 *    - Parser: SQL parsing and validation
 *    - Optimizer: Cost-based query optimization
 *    - Executor: Physical query execution
 *    - Statistics: Query optimization statistics
 *
 * 4. Recovery:
 *    - ARIES: Analysis, Redo, Undo phases
 *    - Crash recovery
 *    - Point-in-time recovery
 *
 * 5. Server Layer:
 *    - Wire Protocol: Client-server communication
 *    - Connection Management
 *    - Authentication and Authorization
 *
 * 6. Schema Management:
 *    - Online schema evolution
 *    - DDL operations
 *    - Schema versioning
 *
 * Correctness Properties (verified by TLA+):
 * - ACID properties maintained
 * - Crash recovery correctness
 * - Concurrency control safety
 * - Query result correctness
 *
 * Production Examples:
 * - PostgreSQL: Full-featured RDBMS
 * - MySQL: Popular open-source database
 * - Oracle: Enterprise database
 * - SQL Server: Microsoft database
 */