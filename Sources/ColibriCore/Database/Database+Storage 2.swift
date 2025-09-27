//
//  Database+Storage.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrìDB — BSD 3-Clause License
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
        let handle = try lockManager.lock(.table(name), mode: .shared, tid: tid ?? 0, timeout: config.lockTimeoutSeconds)
        defer { if tid == nil { lockManager.unlock(handle) } }
        let cutoff = tid.flatMap { txContexts[$0]?.snapshotCutoff }
        let snapshot = mvcc.snapshot(for: tid, isolationCutoff: cutoff)
        let raw: [(RID, Row)]
        if let t = tablesMem[name] {
            raw = Array(try t.scan())
        } else if let ft = tablesFile[name] {
            raw = Array(try ft.scan())
        } else {
            throw DBError.notFound("Table \(name)")
        }

        var visible = mvcc.visibleRows(table: name, snapshot: snapshot, readerTID: tid)
        var results: [(RID, Row)] = []
        results.reserveCapacity(max(visible.count, raw.count))
        var seen = Set<RID>()
        for (rid, row) in visible {
            results.append((rid, row))
            seen.insert(rid)
        }

        let knownVersions = mvcc.allVersions(for: name)
        for (rid, row) in raw where !seen.contains(rid) {
            if knownVersions[rid] != nil {
                // Already tracked by MVCC but not visible for this snapshot.
                continue
            }
            mvcc.registerInsert(table: name, rid: rid, row: row, tid: nil)
            visible[rid] = row
            results.append((rid, row))
            seen.insert(rid)
        }

        results.sort { lhs, rhs in
            if lhs.0.pageId == rhs.0.pageId { return lhs.0.slotId < rhs.0.slotId }
            return lhs.0.pageId < rhs.0.pageId
        }
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
    
    /// Drops a table and all its associated indexes.
    public func dropTable(_ name: String) throws {
        let ddlHandle = try lockManager.lock(.ddl("table:\(name)"), mode: .exclusive, tid: 0, timeout: config.lockTimeoutSeconds)
        let tableHandle = try lockManager.lock(.table(name), mode: .exclusive, tid: 0, timeout: config.lockTimeoutSeconds)
        defer {
            lockManager.unlock(tableHandle)
            lockManager.unlock(ddlHandle)
        }
        
        // Check if table exists
        guard tablesMem[name] != nil || tablesFile[name] != nil else {
            throw DBError.notFound("Table \(name)")
        }
        
        // Drop all indexes for this table
        if let tableIndexes = indexes[name] {
            for (indexName, _) in tableIndexes {
                try dropIndex(table: name, name: indexName)
            }
        }
        
        // Remove from memory tables
        tablesMem.removeValue(forKey: name)
        
        // Remove from file tables and delete physical files
        if tablesFile[name] != nil {
            // For now, just remove from memory - file cleanup would need filePath property
            tablesFile.removeValue(forKey: name)
        }
        
        // Note: System catalog and MVCC cleanup would need additional methods
    }
    
    /// Alters a table (basic implementation for MVP).
    public func alterTable(_ name: String, operation: AlterTableOperation) throws {
        let ddlHandle = try lockManager.lock(.ddl("table:\(name)"), mode: .exclusive, tid: 0, timeout: config.lockTimeoutSeconds)
        let tableHandle = try lockManager.lock(.table(name), mode: .exclusive, tid: 0, timeout: config.lockTimeoutSeconds)
        defer {
            lockManager.unlock(tableHandle)
            lockManager.unlock(ddlHandle)
        }
        
        // Check if table exists
        guard tablesMem[name] != nil || tablesFile[name] != nil else {
            throw DBError.notFound("Table \(name)")
        }
        
        switch operation {
        case .renameTo(let newName):
            try renameTable(from: name, to: newName)
        case .addColumn(let columnName, let columnType):
            // For MVP, we'll just log this - actual schema changes require more complex implementation
            print("Note: ADD COLUMN \(columnName) \(columnType) not yet implemented in MVP")
        case .dropColumn(let columnName):
            // For MVP, we'll just log this - actual schema changes require more complex implementation
            print("Note: DROP COLUMN \(columnName) not yet implemented in MVP")
        }
    }
    
    /// Renames a table.
    private func renameTable(from oldName: String, to newName: String) throws {
        // Check if new name already exists
        guard tablesMem[newName] == nil && tablesFile[newName] == nil else {
            throw DBError.conflict("Table \(newName) already exists")
        }
        
        // Rename in memory tables
        if let memTable = tablesMem[oldName] {
            tablesMem[newName] = memTable
            tablesMem.removeValue(forKey: oldName)
        }
        
        // Rename in file tables
        if let fileTable = tablesFile[oldName] {
            // For now, just rename in memory - file renaming would need filePath property
            tablesFile[newName] = fileTable
            tablesFile.removeValue(forKey: oldName)
        }
        
        // Rename indexes
        if let tableIndexes = indexes[oldName] {
            indexes[newName] = tableIndexes
            indexes.removeValue(forKey: oldName)
        }
        
        // Note: System catalog update would need additional methods
    }
}

/// Operations supported by ALTER TABLE
public enum AlterTableOperation {
    case renameTo(String)
    case addColumn(String, String) // (columnName, columnType)
    case dropColumn(String)
}
