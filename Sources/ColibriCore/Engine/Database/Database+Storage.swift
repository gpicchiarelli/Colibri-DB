//
//  Database+Storage.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Storage wing provisioning heap and index files.

import Foundation
import Dispatch
// MARK: - Storage (Tables)

extension Database {
    /// Ensures that the configured data directory exists.
    public func ensureDataDir() throws {
        let path = config.dataDir
        try FileManager.default.createDirectory(atPath: path, withIntermediateDirectories: true)
    }

    /// Creates a new heap table with the given name.
    /// In-memory or file-backed depending on `config.storageEngine`.
    public func createTable(_ name: String) throws {
        let ddlHandle = try lockManager.lock(.ddl("table:\(name)"), mode: .exclusive, tid: 0, timeout: config.lockTimeoutSeconds)
        let tableHandle = try lockManager.lock(.table(name), mode: .exclusive, tid: 0, timeout: config.lockTimeoutSeconds)
        defer {
            lockManager.unlock(tableHandle)
            lockManager.unlock(ddlHandle)
        }
        if config.storageEngine == "InMemory" {
            guard tablesMem[name] == nil else { throw DBError.conflict("Table exists: \(name)") }
            tablesMem[name] = HeapTable()
            systemCatalog?.registerTable(name: name,
                                         schema: nil,
                                         storage: config.storageEngine,
                                         physicalPath: nil,
                                         pageSize: nil,
                                         inMemory: true)
            return
        }
        let dir = URL(fileURLWithPath: config.dataDir).appendingPathComponent("tables")
        try FileManager.default.createDirectory(at: dir, withIntermediateDirectories: true)
        let path = dir.appendingPathComponent("\(name).dat").path
        guard tablesFile[name] == nil else { throw DBError.conflict("Table exists: \(name)") }
        let qos = DispatchQoS.fromConfig(config.bufferFlushQoS)
        tablesFile[name] = try FileHeapTable(path: path,
                                             pageSize: config.pageSizeBytes,
                                             capacityPages: config.dataBufferPoolPages,
                                             flushQoS: qos,
                                             sequentialReadHint: config.ioSequentialReadHint,
                                             pageCompression: config.pageFlushCompression)
        systemCatalog?.registerTable(name: name,
                                     schema: nil,
                                     storage: config.storageEngine,
                                     physicalPath: path,
                                     pageSize: config.pageSizeBytes,
                                     inMemory: false)
    }

    /// Lists all known table names (in-memory and file-backed).
    public func listTables() -> [String] {
        let names: Set<Dictionary<String, HeapTable>.Keys.Element> = Set(tablesMem.keys).union(tablesFile.keys)
        return Array(names).sorted()
    }

    /// Scans a table and returns an array of (RID, Row) visible to the caller.
    public func scan(_ name: String, tid: UInt64? = nil) throws -> [(RID, Row)] {
        try assertTableRegistered(name)
        let handle = try lockManager.lock(.table(name), mode: .shared, tid: tid ?? 0, timeout: config.lockTimeoutSeconds)
        defer { if tid == nil { lockManager.unlock(handle) } }
        let cutoff = tid.flatMap { txContexts[$0]?.snapshotCutoff }
        let snapshot = mvcc.snapshot(for: tid, isolationCutoff: cutoff)
        // With MVCC tombstone support, rely solely on MVCC for visibility.
        let results = mvcc.visibleRows(table: name, snapshot: snapshot, readerTID: tid)
            .sorted { lhs, rhs in
                if lhs.key.pageId == rhs.key.pageId { return lhs.key.slotId < rhs.key.slotId }
                return lhs.key.pageId < rhs.key.pageId
            }
            .map { ($0.key, $0.value) }
        return results
    }

    /// Reads a single row by RID from a table.
    public func readRow(table: String, rid: RID) throws -> Row {
        if let mem = tablesMem[table] {
            return try mem.read(rid)
        }
        if let file = tablesFile[table] {
            return try file.read(rid)
        }
        throw DBError.notFound("Table \(table)")
    }
}
