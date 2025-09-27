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

/// Coordinatore principale del motore: istanzia storage, indici, WAL, MVCC,
/// policy e cataloghi, offrendo un'unica facciata ai comandi della CLI e agli
/// operatori di query. Ogni metodo adotta lock/MVCC/WAL in modo coerente così
/// che le estensioni future (planner, server remoto) possano delegare qui.
public final class Database {
    /// Configurazione runtime (pagina, buffer, isolamento, policy, ecc.).
    public let config: DBConfig

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
    var cachedTableStats: [String: HeapFragmentationStats] = [:]
    var tableStatistics: [String: TableStatistics] = [:]
    var indexStatistics: [String: IndexStatistics] = [:]
    var lastIndexCompaction: [String: Date] = [:]
    var materializedViewCache: [String: [[String: Value]]] = [:]
    let materializedViewLock = NSLock()

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
}
