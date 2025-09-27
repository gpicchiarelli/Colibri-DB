//
//  Database.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Database facade unifying storage, WAL, MVCC, and policies.

import Foundation
import os.log

/// Coordinatore principale del motore: istanzia storage, indici, WAL, MVCC,
/// policy e cataloghi, offrendo un'unica facciata ai comandi della CLI e agli
/// operatori di query. Ogni metodo adotta lock/MVCC/WAL in modo coerente così
/// che le estensioni future (planner, server remoto) possano delegare qui.
    public final class Database {
    /// Configurazione runtime (pagina, buffer, isolamento, policy, ecc.).
    public let config: DBConfig
    
    // Apple Silicon optimizations
    private let logger = Logger(subsystem: "com.colibridb", category: "database")

    // MARK: - Storage state
    var tablesMem: [String: HeapTable] = [:]
    var tablesFile: [String: FileHeapTable] = [:]
    var wal: FileWAL?
    var lastDBLSN: UInt64 = 0

    /// Backend disponibili per ogni indice registrato.
    public enum IndexBackend {
        case anyString(AnyStringIndex)
        case persistentBTree(FileBPlusTreeIndex)
    }

    // MARK: - Index state & catalog
    var indexes: [String: [String: (columns: [String], backend: IndexBackend)]] = [:]
    var indexCatalog: IndexCatalog?
    var systemCatalog: SystemCatalog?
    var multiDatabaseCatalog: MultiDatabaseCatalog?
    var catalogManager: CatalogManager?
    var cachedTableStats: [String: HeapFragmentationStats] = [:]
    var tableStatistics: [String: TableStatistics] = [:]
    var indexStatistics: [String: IndexStatistics] = [:]
    var lastIndexCompaction: [String: Date] = [:]
    var materializedViewCache: [String: [[String: Value]]] = [:]
    let materializedViewLock = NSLock()
    
    // MARK: - Constraint management
    public var constraintManager: ConstraintManager
    
    // MARK: - Statistics
    public func getTableStatistics(_ tableName: String) throws -> TableStatistics {
        // Return cached statistics if available
        if let stats = tableStatistics[tableName] {
            return stats
        }
        
        // Create default statistics for the table
        let stats = TableStatistics(
            tableName: tableName,
            rowCount: 0,
            pageCount: 0,
            averageRowSize: 0,
            lastAnalyzed: Date()
        )
        
        // Cache the statistics
        tableStatistics[tableName] = stats
        return stats
    }
    
    // MARK: - Lifecycle
    public func close() throws {
        // Close all active transactions
        // TODO: Implement proper transaction cleanup
        
        // Clear caches
        cachedTableStats.removeAll()
        tableStatistics.removeAll()
        indexStatistics.removeAll()
        materializedViewCache.removeAll()
        
        // TODO: Close storage, indexes, etc.
    }

    // MARK: - Policies & optimizer
    var policyStore: InMemoryPolicyStore
    let simulator: SimpleOptimizationSimulator
    let mvcc = MVCCManager()
    let lockManager: LockManager
    let serialClock = SerializableClock()

    struct TransactionContext {
        let isolation: IsolationLevel
        let snapshotCutoff: UInt64
        let clockTimestamp: UInt64
    }

    var txContexts: [UInt64: TransactionContext] = [:]
    var lastCommittedClockTimestamp: UInt64 = 0

    // MARK: - Transaction state
    var nextTID: UInt64 = 1
    var activeTIDs: Set<UInt64> = []
    struct TxOp { enum Kind { case insert, delete }; let kind: Kind; let table: String; let rid: RID; let row: Row }
    struct TxState {
        var ops: [TxOp] = []
        var savepoints: [String: Int] = [:]
    }
    var txStates: [UInt64: TxState] = [:]
    var preparedTransactions: Set<UInt64> = []
    var txLastLSN: [UInt64: UInt64] = [:]

    // Dirty Page Table: pageId -> recLSN
    var dpt: [UInt64: UInt64] = [:]

    // MARK: - Vacuum background job state & metrics
    var vacuumTimer: DispatchSourceTimer?
    let vacuumQueue = DispatchQueue(label: "ColibriDB.Vacuum")
    var vacuumPositions: [String: UInt64] = [:]
    var vacuumPagesPerRun: Int = 32
    public internal(set) var vacuumTotalPagesCompacted: Int = 0
    public internal(set) var vacuumTotalBytesReclaimed: Int = 0
    public internal(set) var vacuumRuns: Int = 0
    public internal(set) var vacuumLastRun: Date? = nil

    public init(config: DBConfig) {
        self.config = config
        self.lockManager = LockManager(defaultTimeout: config.lockTimeoutSeconds)
        self.policyStore = InMemoryPolicyStore()
        self.simulator = SimpleOptimizationSimulator()
        self.constraintManager = ConstraintManager()
        // Set global buffer quotas per namespace
        BufferNamespaceManager.shared.setQuota(group: "table", pages: config.dataBufferPoolPages)
        BufferNamespaceManager.shared.setQuota(group: "index", pages: config.indexBufferPoolPages)
        if config.walEnabled {
            let walPath = URL(fileURLWithPath: config.dataDir).appendingPathComponent("wal.log").path
            self.wal = try? FileWAL(path: walPath)
            self.wal?.setFullFSync(enabled: config.walFullFSyncEnabled)
            self.wal?.setIOHints(enabled: config.ioSequentialReadHint)
            self.wal?.setCompression(config.walCompression)
        }
        // Load index catalog
        let idxDir = URL(fileURLWithPath: config.dataDir).appendingPathComponent("indexes").path
        self.indexCatalog = try? IndexCatalog(dir: idxDir)
        let catalogPath = URL(fileURLWithPath: config.dataDir).appendingPathComponent("system_catalog.json").path
        self.systemCatalog = try? SystemCatalog(path: catalogPath)
        
        // Initialize multi-database catalog system
        self.multiDatabaseCatalog = MultiDatabaseCatalog(database: self)
        self.catalogManager = CatalogManager(database: self)
        
        // Initialize catalog system
        try? self.catalogManager?.initializeCatalog()
        
        bootstrapSystemCatalogTables()
        bootstrapSystemCatalogRoles()
        bootstrapSystemCatalogConfigurations()
        if let defs = indexCatalog?.list() {
            for def in defs { try? restoreIndex(from: def) }
        }
        // Replay DB WAL to recover
        try? replayDBWAL()
        bootstrapMVCCState()
        if config.autoCompactionEnabled {
            startVacuum(intervalSeconds: config.autoCompactionIntervalSeconds, pagesPerRun: config.autoCompactionPagesPerRun)
        }
    }

    private func bootstrapSystemCatalogRoles() {
        guard let catalog = systemCatalog else { return }
        _ = catalog.registerRole(name: "admin", kind: .user, members: [], privileges: ["ALL"], metadata: ["builtIn": "true"])
        _ = catalog.registerRole(name: "dba", kind: .group, members: ["admin"], privileges: ["MANAGE_DB", "MANAGE_SECURITY"], metadata: ["builtIn": "true"])
    }

    private func bootstrapSystemCatalogConfigurations() {
        guard let catalog = systemCatalog else { return }
        _ = catalog.registerConfiguration(scope: "global", key: "storageEngine", value: config.storageEngine)
        _ = catalog.registerConfiguration(scope: "global", key: "indexImplementation", value: config.indexImplementation)
        _ = catalog.registerConfiguration(scope: "maintenance", key: "autoCompactionEnabled", value: String(config.autoCompactionEnabled))
        _ = catalog.registerConfiguration(scope: "maintenance", key: "autoCompactionIntervalSeconds", value: String(config.autoCompactionIntervalSeconds))
    }
}

extension Database {
    private func bootstrapSystemCatalogTables() {
        guard let catalog = systemCatalog else { return }
        let tablesDir = URL(fileURLWithPath: config.dataDir).appendingPathComponent("tables")
        guard let urls = try? FileManager.default.contentsOfDirectory(at: tablesDir, includingPropertiesForKeys: nil, options: [.skipsHiddenFiles]) else { return }
        for url in urls where url.pathExtension.lowercased() == "dat" {
            let name = url.deletingPathExtension().lastPathComponent
            catalog.registerTable(name: name,
                                  schema: nil,
                                  storage: config.storageEngine,
                                  physicalPath: url.path,
                                  pageSize: config.pageSizeBytes,
                                  inMemory: false)
        }
    }

    private func bootstrapMVCCState() {
        for (name, table) in tablesMem {
            if let rows = try? table.scan() {
                for (rid, row) in rows {
                    mvcc.registerInsert(table: name, rid: rid, row: row, tid: nil)
                }
            }
        }
        for (name, table) in tablesFile {
            if let rows = try? table.scan() {
                for (rid, row) in rows {
                    mvcc.registerInsert(table: name, rid: rid, row: row, tid: nil)
                }
            }
        }
    }
    
    // MARK: - Multi-Database Catalog Access
    
    /// Gets the multi-database catalog
    public func getMultiDatabaseCatalog() -> MultiDatabaseCatalog? {
        return multiDatabaseCatalog
    }
    
    /// Gets the catalog manager
    public func getCatalogManager() -> CatalogManager? {
        return catalogManager
    }
    
    /// Creates a new database in the catalog
    public func createDatabase(_ name: String, owner: String? = nil) throws {
        try multiDatabaseCatalog?.createDatabase(name, owner: owner)
    }
    
    /// Drops a database from the catalog
    public func dropDatabase(_ name: String, cascade: Bool = false) throws {
        try multiDatabaseCatalog?.dropDatabase(name, cascade: cascade)
    }
    
    /// Lists all databases
    public func listDatabases() throws -> [DatabaseEntry] {
        return try multiDatabaseCatalog?.listDatabases() ?? []
    }
    
    /// Checks if a database exists
    public func databaseExists(_ name: String) throws -> Bool {
        return try multiDatabaseCatalog?.databaseExists(name) ?? false
    }
    
    /// Creates a table in the specified database
    public func createTable(_ name: String, in database: String, schema: CatalogTableSchema) throws {
        try multiDatabaseCatalog?.createTable(name, in: database, schema: schema)
    }
    
    /// Drops a table from the specified database
    public func dropTable(_ name: String, in database: String) throws {
        try multiDatabaseCatalog?.dropTable(name, in: database)
    }
    
    /// Lists all tables in the specified database
    public func listTables(in database: String) throws -> [TableEntry] {
        return try multiDatabaseCatalog?.listTables(in: database) ?? []
    }
    
    /// Checks if a table exists in the specified database
    public func tableExists(_ name: String, in database: String) throws -> Bool {
        return try multiDatabaseCatalog?.tableExists(name, in: database) ?? false
    }
    
    /// Creates an index on the specified table
    public func createIndex(_ name: String, on table: String, in database: String, 
                           columns: [String], type: IndexType, options: IndexOptions? = nil) throws {
        try multiDatabaseCatalog?.createIndex(name, on: table, in: database, columns: columns, type: type, options: options)
    }
    
    /// Drops an index from the specified table
    public func dropIndex(_ name: String, on table: String, in database: String) throws {
        try multiDatabaseCatalog?.dropIndex(name, on: table, in: database)
    }
    
    /// Lists all indexes on the specified table
    public func listIndexes(on table: String, in database: String) throws -> [IndexEntry] {
        return try multiDatabaseCatalog?.listIndexes(on: table, in: database) ?? []
    }
    
    /// Checks if an index exists on the specified table
    public func indexExists(_ name: String, on table: String, in database: String) throws -> Bool {
        return try multiDatabaseCatalog?.indexExists(name, on: table, in: database) ?? false
    }
    
    /// Creates a view in the specified database
    public func createView(_ name: String, in database: String, definition: String) throws {
        try multiDatabaseCatalog?.createView(name, in: database, definition: definition)
    }
    
    /// Drops a view from the specified database
    public func dropView(_ name: String, in database: String) throws {
        try multiDatabaseCatalog?.dropView(name, in: database)
    }
    
    /// Lists all views in the specified database
    public func listViews(in database: String) throws -> [ViewEntry] {
        return try multiDatabaseCatalog?.listViews(in: database) ?? []
    }
    
    /// Checks if a view exists in the specified database
    public func viewExists(_ name: String, in database: String) throws -> Bool {
        return try multiDatabaseCatalog?.viewExists(name, in: database) ?? false
    }
    
    /// Creates a sequence in the specified database
    public func createSequence(_ name: String, in database: String, options: SequenceOptions) throws {
        try multiDatabaseCatalog?.createSequence(name, in: database, options: options)
    }
    
    /// Drops a sequence from the specified database
    public func dropSequence(_ name: String, in database: String) throws {
        try multiDatabaseCatalog?.dropSequence(name, in: database)
    }
    
    /// Lists all sequences in the specified database
    public func listSequences(in database: String) throws -> [SequenceEntry] {
        return try multiDatabaseCatalog?.listSequences(in: database) ?? []
    }
    
    /// Checks if a sequence exists in the specified database
    public func sequenceExists(_ name: String, in database: String) throws -> Bool {
        return try multiDatabaseCatalog?.sequenceExists(name, in: database) ?? false
    }
    
    /// Updates table statistics
    public func updateTableStatistics(_ table: String, in database: String) throws {
        try multiDatabaseCatalog?.updateTableStatistics(table, in: database)
    }
}
