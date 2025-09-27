//
//  Database+Indexes.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Index desk registering, restoring, and managing backends.

import Foundation
import Dispatch
// MARK: - Indexes

extension Database {
    /// Lists index names defined for a table.
    /// - Parameter table: Table name.
    /// - Returns: Sorted list of index names.
    public func listIndexes(table: String) -> [String] {
        return (indexes[table]?.keys.map { $0 } ?? []).sorted()
    }

    /// Creates an index on one or more columns.
    /// - Parameters:
    ///   - name: Index name.
    ///   - table: Table name.
    ///   - columns: Column list (single or composite for B+Tree).
    ///   - kind: Index kind (e.g. "BTree", in‑memory kinds). Composite supported only for B+Tree.
    /// - Throws: `DBError.notFound`, `DBError.conflict`, `DBError.invalidArgument`.
    public func createIndex(name: String, on table: String, columns: [String], using kind: String) throws {
        try assertTableRegistered(table)
        let ddlHandle = try lockManager.lock(.ddl("index:\(table).\(name)"), mode: .exclusive, tid: 0, timeout: config.lockTimeoutSeconds)
        let indexHandle = try lockManager.lock(.index(table: table, name: name), mode: .exclusive, tid: 0, timeout: config.lockTimeoutSeconds)
        let tableHandle = try lockManager.lock(.table(table), mode: .exclusive, tid: 0, timeout: config.lockTimeoutSeconds)
        defer {
            lockManager.unlock(tableHandle)
            lockManager.unlock(indexHandle)
            lockManager.unlock(ddlHandle)
        }
        guard tablesMem[table] != nil || tablesFile[table] != nil else { throw DBError.notFound("Table \(table)") }
        var map = indexes[table] ?? [:]
        guard map[name] == nil else { throw DBError.conflict("Index exists: \(name)") }
        if ["btree","b+tree","b-tree"].contains(kind.lowercased()) {
            let dir = URL(fileURLWithPath: config.dataDir).appendingPathComponent("indexes")
            try FileManager.default.createDirectory(at: dir, withIntermediateDirectories: true)
            let path = dir.appendingPathComponent("\(table)__\(name).bt").path
            let qos = DispatchQoS.fromConfig(config.bufferFlushQoS)
            let idx = try FileBPlusTreeIndex(path: path,
                                             pageSize: config.pageSizeBytes,
                                             capacityPages: config.indexBufferPoolPages,
                                             flushQoS: qos,
                                             ioHintsEnabled: config.ioSequentialReadHint,
                                             walFullSyncEnabled: config.walFullFSyncEnabled)
            // Apply WAL no-cache hint if requested
            if config.walNoCache { IOHints.setNoCache(fd: idx.walFH.fileDescriptor, enabled: true) }
            map[name] = (columns: columns, backend: .persistentBTree(idx))
            try indexCatalog?.add(IndexDef(name: name, table: table, column: nil, columns: columns, kind: "BTree"))
            systemCatalog?.registerIndex(name: name,
                                          table: table,
                                          kind: "BTree",
                                          physicalPath: path,
                                          columns: columns)
            systemCatalog?.registerStructurePreference(table: table, columns: columns, structure: "btree")
        } else {
            guard columns.count == 1 else { throw DBError.invalidArgument("In-memory indexes support one column only") }
            map[name] = (columns: columns, backend: .anyString(AnyStringIndex(kind: kind)))
            try indexCatalog?.add(IndexDef(name: name, table: table, column: columns.first, columns: columns, kind: kind))
            systemCatalog?.registerIndex(name: name,
                                          table: table,
                                          kind: kind,
                                          physicalPath: nil,
                                          columns: columns)
            systemCatalog?.registerStructurePreference(table: table, columns: columns, structure: kind.lowercased())
        }
        indexes[table] = map
    }

    /// Drops an index and removes all catalog metadata and on-disk structures.
    /// - Parameters:
    ///   - table: Table name.
    ///   - name: Index name.
    public func dropIndex(table: String, name: String) throws {
        try assertTableRegistered(table)
        try assertIndexRegistered(name, table: table)
        let ddlHandle = try lockManager.lock(.ddl("index:\(table).\(name)"), mode: .exclusive, tid: 0, timeout: config.lockTimeoutSeconds)
        let indexHandle = try lockManager.lock(.index(table: table, name: name), mode: .exclusive, tid: 0, timeout: config.lockTimeoutSeconds)
        let tableHandle = try lockManager.lock(.table(table), mode: .exclusive, tid: 0, timeout: config.lockTimeoutSeconds)
        defer {
            lockManager.unlock(tableHandle)
            lockManager.unlock(indexHandle)
            lockManager.unlock(ddlHandle)
        }
        guard var map = indexes[table], let entry = map[name] else { throw DBError.notFound("Index \(name)") }
        switch entry.backend {
        case .anyString:
            break
        case .persistentBTree(let index):
            index.close()
            let fm = FileManager.default
            try? fm.removeItem(atPath: index.path)
            try? fm.removeItem(atPath: index.path + ".wal")
        }
        map.removeValue(forKey: name)
        if map.isEmpty { indexes.removeValue(forKey: table) } else { indexes[table] = map }
        try indexCatalog?.remove(name: name, table: table)
        systemCatalog?.removeIndex(name: name, table: table)
        indexStatistics.removeValue(forKey: "\(table).\(name)")
        lastIndexCompaction.removeValue(forKey: "\(table).\(name)")
    }

    func updateIndexes(table: String, row: Row, rid: RID) {
        guard var map = indexes[table] else { return }
        let allowed: Set<String>
        if let sc = systemCatalog {
            let objs = sc.logicalObjects(kind: .index).filter { $0.parentName == table }
            allowed = Set(objs.map { $0.name })
        } else {
            allowed = Set(map.keys)
        }
        for (name, pair) in map where allowed.contains(name) {
            let cols = pair.columns
            switch pair.backend {
            case .anyString(var idx):
                guard let c = cols.first, let v = row[c] else { continue }
                let s = stringFromValue(v)
                idx.insert(key: s, ref: rid)
                map[name] = (columns: cols, backend: .anyString(idx))
            case .persistentBTree(let f):
                if cols.count == 1 {
                    if let v = row[cols[0]] { try? f.insert(key: v, rid: rid) }
                } else {
                    var values: [Value] = []
                    var ok = true
                    for c in cols { guard let v = row[c] else { ok = false; break }; values.append(v) }
                    if ok { try? f.insert(composite: values, rid: rid) }
                }
                map[name] = (columns: cols, backend: .persistentBTree(f))
            }
        }
        indexes[table] = map
    }

    func removeFromIndexes(table: String, row: Row, rid: RID, skipIndexName: String? = nil) {
        guard var map = indexes[table] else { return }
        let allowed: Set<String>
        if let sc = systemCatalog {
            let objs = sc.logicalObjects(kind: .index).filter { $0.parentName == table }
            allowed = Set(objs.map { $0.name })
        } else {
            allowed = Set(map.keys)
        }
        for (name, pair) in map where allowed.contains(name) {
            if let skip = skipIndexName, skip == name { continue }
            let cols = pair.columns
            switch pair.backend {
            case .anyString(var idx):
                guard let c = cols.first, let v = row[c] else { continue }
                let s = stringFromValue(v)
                idx.remove(key: s, ref: rid)
                map[name] = (columns: cols, backend: .anyString(idx))
            case .persistentBTree(let f):
                if cols.count == 1 {
                    if let v = row[cols[0]] { try? f.remove(key: v, rid: rid) }
                } else {
                    var values: [Value] = []
                    var ok = true
                    for c in cols { guard let v = row[c] else { ok = false; break }; values.append(v) }
                    if ok { try? f.remove(composite: values, rid: rid) }
                }
                map[name] = (columns: cols, backend: .persistentBTree(f))
            }
        }
        indexes[table] = map
    }

    // Search helpers
    /// Searches an index for equality on a single typed value (or first component).
    /// - Parameters:
    ///   - table: Table name.
    ///   - index: Index name.
    ///   - value: Value to match.
    /// - Returns: Matching RIDs.
    /// - Throws: `DBError.notFound` if index not found.
    public func indexSearchEqualsTyped(table: String, index: String, value: Value) throws -> [RID] {
        try assertTableRegistered(table)
        try assertIndexRegistered(index, table: table)
        guard let map = indexes[table], let pair = map[index] else { throw DBError.notFound("Index \(index)") }
        switch pair.backend {
        case .anyString(let idx):
            return idx.searchEquals(stringFromValue(value))
        case .persistentBTree(let f):
            if pair.columns.count == 1 { return f.searchEquals(value) }
            else { return f.searchEquals(composite: [value]) }
        }
    }

    /// Searches an index for equality on one or more values (composite).
    /// - Parameters:
    ///   - table: Table name.
    ///   - index: Index name.
    ///   - values: Value list (must match index arity for composite).
    /// - Returns: Matching RIDs.
    /// - Throws: `DBError.notFound`, `DBError.invalidArgument` for unsupported combos.
    public func indexSearchEqualsValues(table: String, index: String, values: [Value]) throws -> [RID] {
        try assertTableRegistered(table)
        try assertIndexRegistered(index, table: table)
        guard let map = indexes[table], let pair = map[index] else { throw DBError.notFound("Index \(index)") }
        switch pair.backend {
        case .anyString:
            throw DBError.invalidArgument("Composite equality not supported for in-memory indexes")
        case .persistentBTree(let f):
            if values.count == 1 { return f.searchEquals(values[0]) }
            return f.searchEquals(composite: values)
        }
    }

    /// Range query on a single-value index (or first component).
    /// - Parameters:
    ///   - table: Table name.
    ///   - index: Index name.
    ///   - lo: Lower bound (inclusive) or nil.
    ///   - hi: Upper bound (inclusive) or nil.
    /// - Returns: RIDs within the range.
    /// - Throws: `DBError.notFound` if index not found.
    public func indexRangeTyped(table: String, index: String, lo: Value?, hi: Value?) throws -> [RID] {
        try assertTableRegistered(table)
        try assertIndexRegistered(index, table: table)
        guard let map = indexes[table], let pair = map[index] else { throw DBError.notFound("Index \(index)") }
        switch pair.backend {
        case .anyString(let idx):
            return idx.range(lo.map { stringFromValue($0) }, hi.map { stringFromValue($0) })
        case .persistentBTree(let f):
            if pair.columns.count == 1 { return f.range(lo, hi) }
            else { return f.range(compositeLo: lo.map { [$0] }, compositeHi: hi.map { [$0] }) }
        }
    }

    /// Range query on a composite index.
    /// - Parameters:
    ///   - table: Table name.
    ///   - index: Index name.
    ///   - lo: Optional lower bound values.
    ///   - hi: Optional upper bound values.
    /// - Returns: RIDs within the range.
    /// - Throws: `DBError.notFound`, `DBError.invalidArgument` if unsupported for index kind.
    public func indexRangeValues(table: String, index: String, lo: [Value]?, hi: [Value]?) throws -> [RID] {
        try assertTableRegistered(table)
        try assertIndexRegistered(index, table: table)
        guard let map = indexes[table], let pair = map[index] else { throw DBError.notFound("Index \(index)") }
        switch pair.backend {
        case .anyString:
            throw DBError.invalidArgument("Composite range not supported for in-memory indexes")
        case .persistentBTree(let f):
            if (lo?.count ?? 0) <= 1 && (hi?.count ?? 0) <= 1 {
                return f.range(lo?.first, hi?.first)
            }
            return f.range(compositeLo: lo, compositeHi: hi)
        }
    }

    // Validate: scans table and checks each row is indexed
    /// Validates that all table rows are present in the index.
    /// - Parameters:
    ///   - table: Table name.
    ///   - index: Index name.
    /// - Returns: Tuple with total rows, indexed rows, and missing count.
    /// - Throws: `DBError.notFound` if index not found.
    public func validateIndex(table: String, index: String) throws -> (total: Int, indexed: Int, missing: Int) {
        try assertTableRegistered(table)
        try assertIndexRegistered(index, table: table)
        guard let pair = indexes[table]?[index] else { throw DBError.notFound("Index \(index)") }
        let rows = try scan(table)
        var indexed = 0
        for (_, row) in rows {
            let cols = pair.columns
            let hits: [RID]
            switch pair.backend {
            case .anyString(let idx):
                guard let c = cols.first, let v = row[c] else { continue }
                hits = idx.searchEquals(stringFromValue(v))
            case .persistentBTree(let f):
                if cols.count == 1 { if let v = row[cols[0]] { hits = f.searchEquals(v) } else { hits = [] } }
                else {
                    var vs: [Value] = []
                    var ok = true
                    for c in cols { guard let v = row[c] else { ok = false; break }; vs.append(v) }
                    hits = ok ? f.searchEquals(composite: vs) : []
                }
            }
            if !hits.isEmpty { indexed += 1 }
        }
        let total = rows.count
        return (total, indexed, total - indexed)
    }

    // Rebuild: drops and rebuilds persistent BTree from table scan
    /// Rebuilds a persistent B+Tree index by scanning the table.
    /// - Parameters:
    ///   - table: Table name.
    ///   - index: Index name.
    /// - Throws: `DBError.notFound`, `DBError.notImplemented` for in‑memory kinds.
    public func rebuildIndex(table: String, index: String) throws {
        try assertTableRegistered(table)
        try assertIndexRegistered(index, table: table)
        let ddlHandle = try lockManager.lock(.ddl("index:\(table).\(index)"), mode: .exclusive, tid: 0, timeout: config.lockTimeoutSeconds)
        let indexHandle = try lockManager.lock(.index(table: table, name: index), mode: .exclusive, tid: 0, timeout: config.lockTimeoutSeconds)
        let tableHandle = try lockManager.lock(.table(table), mode: .exclusive, tid: 0, timeout: config.lockTimeoutSeconds)
        defer {
            lockManager.unlock(tableHandle)
            lockManager.unlock(indexHandle)
            lockManager.unlock(ddlHandle)
        }
        guard var map = indexes[table], let pair = map[index] else { throw DBError.notFound("Index \(index)") }
        switch pair.backend {
        case .anyString:
            throw DBError.notImplemented("Rebuild not supported for in-memory indexes")
        case .persistentBTree(_):
            let dir = URL(fileURLWithPath: config.dataDir).appendingPathComponent("indexes")
            let path = dir.appendingPathComponent("\(table)__\(index).bt").path
            try? FileManager.default.removeItem(atPath: path)
            let qos = DispatchQoS.fromConfig(config.bufferFlushQoS)
            let idx = try FileBPlusTreeIndex(path: path,
                                             pageSize: config.pageSizeBytes,
                                             capacityPages: config.indexBufferPoolPages,
                                             flushQoS: qos,
                                             ioHintsEnabled: config.ioSequentialReadHint,
                                             walFullSyncEnabled: config.walFullFSyncEnabled)
            let cols = pair.columns
            for (rid, row) in try scan(table) {
                if cols.count == 1 {
                    if let v = row[cols[0]] { try? idx.insert(key: v, rid: rid) }
                } else {
                    var vs: [Value] = []
                    var ok = true
                    for c in cols { guard let v = row[c] else { ok = false; break }; vs.append(v) }
                    if ok { try? idx.insert(composite: vs, rid: rid) }
                }
            }
            map[index] = (columns: cols, backend: .persistentBTree(idx))
            indexes[table] = map
        }
    }

    /// Bulk rebuild of a persistent B+Tree index using sorted key lists.
    /// - Parameters:
    ///   - table: Table name.
    ///   - index: Index name.
    /// - Throws: `DBError.notFound`, `DBError.notImplemented` for in‑memory kinds.
    public func rebuildIndexBulk(table: String, index: String) throws {
        try assertTableRegistered(table)
        try assertIndexRegistered(index, table: table)
        let ddlHandle = try lockManager.lock(.ddl("index:\(table).\(index)"), mode: .exclusive, tid: 0, timeout: config.lockTimeoutSeconds)
        let indexHandle = try lockManager.lock(.index(table: table, name: index), mode: .exclusive, tid: 0, timeout: config.lockTimeoutSeconds)
        let tableHandle = try lockManager.lock(.table(table), mode: .exclusive, tid: 0, timeout: config.lockTimeoutSeconds)
        defer {
            lockManager.unlock(tableHandle)
            lockManager.unlock(indexHandle)
            lockManager.unlock(ddlHandle)
        }
        guard var map = indexes[table], let pair = map[index] else { throw DBError.notFound("Index \(index)") }
        switch pair.backend {
        case .anyString:
            throw DBError.notImplemented("Bulk build available only for persistent BTree")
        case .persistentBTree(let f):
            f.setIOHints(enabled: config.ioSequentialReadHint)
            f.setFullFSync(enabled: config.walFullFSyncEnabled)
            let cols = pair.columns
            // Collect (encodedKey, rid)
            var flat: [(Data, RID)] = []
            for (rid, row) in try scan(table) {
                if cols.count == 1, let v = row[cols[0]] {
                    flat.append((KeyBytes.fromValue(v).bytes, rid))
                } else {
                    var vs: [Value] = []
                    var ok = true
                    for c in cols { guard let v = row[c] else { ok = false; break }; vs.append(v) }
                    if ok { flat.append((KeyBytes.fromValues(vs).bytes, rid)) }
                }
            }
            // Sort by key
            flat.sort { $0.0.lexicographicallyPrecedes($1.0) }
            // Group into unique keys and rid lists
            var keys: [Data] = []
            var lists: [[RID]] = []
            var i = 0
            while i < flat.count {
                let key = flat[i].0
                var rids: [RID] = []
                while i < flat.count && flat[i].0 == key { rids.append(flat[i].1); i += 1 }
                keys.append(key); lists.append(rids)
            }
            try f.bulkBuildEncoded(keys: keys, ridLists: lists)
            map[index] = (columns: cols, backend: .persistentBTree(f))
            indexes[table] = map
        }
    }

    /// Validates internal B+Tree structure and returns a detailed report.
    /// - Parameters:
    ///   - table: Table name.
    ///   - index: Index name.
    /// - Returns: Human‑readable validation report.
    /// - Throws: `DBError.notFound`.
    public func validateIndexDeep(table: String, index: String) throws -> String {
        try assertTableRegistered(table)
        try assertIndexRegistered(index, table: table)
        guard let pair = indexes[table]?[index] else { throw DBError.notFound("Index \(index)") }
        switch pair.backend {
        case .anyString:
            return "(not supported for in-memory indexes)"
        case .persistentBTree(let f):
            return f.validateDeep().description
        }
    }

    /// Dumps index header (and optional page) information.
    /// - Parameters:
    ///   - table: Table name.
    ///   - index: Index name.
    ///   - pageId: Optional page id to target.
    /// - Returns: Summary string.
    /// - Throws: `DBError.notFound`.
    public func indexDumpHeader(table: String, index: String, pageId: UInt64?) throws -> String {
        try assertTableRegistered(table)
        try assertIndexRegistered(index, table: table)
        guard let pair = indexes[table]?[index] else { throw DBError.notFound("Index \(index)") }
        switch pair.backend {
        case .anyString:
            return "(not supported for in-memory indexes)"
        case .persistentBTree(let f):
            return f.dumpHeader(pageId: pageId)
        }
    }

    /// Dumps the first N leaf pages of the index.
    /// - Parameters:
    ///   - table: Table name.
    ///   - index: Index name.
    ///   - count: Number of leaf pages to dump (>= 1).
    /// - Returns: Multi‑line string with page dumps.
    /// - Throws: `DBError.notFound`.
    public func indexDumpFirstLeaves(table: String, index: String, count: Int) throws -> String {
        try assertTableRegistered(table)
        try assertIndexRegistered(index, table: table)
        guard let pair = indexes[table]?[index] else { throw DBError.notFound("Index \(index)") }
        switch pair.backend {
        case .anyString:
            return "(not supported for in-memory indexes)"
        case .persistentBTree(let f):
            return f.dumpFirstLeaves(count: max(1, count)).joined(separator: "\n")
        }
    }

    /// Flushes index buffer pool to disk.
    /// - Parameters:
    ///   - table: Table name.
    ///   - index: Index name.
    /// - Throws: `DBError.notFound`.
    public func flushIndex(_ table: String, _ index: String, fullSync: Bool = false) throws {
        Signpost.event(.flush, name: "DBFlushIndex", message: "\(table).\(index) full=\(fullSync ? 1 : 0)")
        try assertTableRegistered(table)
        try assertIndexRegistered(index, table: table)
        guard let pair = indexes[table]?[index] else { throw DBError.notFound("Index \(index)") }
        switch pair.backend {
        case .anyString:
            return
        case .persistentBTree(let f):
            try f.flushBuffers(fullSync: fullSync)
        }
    }

    /// Compacts a persistent B+Tree index file by rewriting used pages.
    /// - Parameters:
    ///   - table: Table name.
    ///   - index: Index name.
    /// - Throws: `DBError.notFound`, `DBError.notImplemented` for in‑memory kinds.
    public func compactIndex(table: String, index: String) throws {
        try assertTableRegistered(table)
        try assertIndexRegistered(index, table: table)
        guard let pair = indexes[table]?[index] else { throw DBError.notFound("Index \(index)") }
        switch pair.backend {
        case .anyString:
            throw DBError.notImplemented("Compaction only for persistent BTree")
        case .persistentBTree(let f):
            try f.compactPhysical()
        }
    }

    // Restore index from catalog
    func restoreIndex(from def: IndexDef) throws {
        var map = indexes[def.table] ?? [:]
        if let existing = map[def.name] {
            if case .persistentBTree(let tree) = existing.backend {
                tree.setIOHints(enabled: config.ioSequentialReadHint)
                tree.setFullFSync(enabled: config.walFullFSyncEnabled)
            }
            systemCatalog?.registerIndex(name: def.name,
                                          table: def.table,
                                          kind: def.kind,
                                          physicalPath: physicalPath(for: def),
                                          columns: def.columns ?? (def.column.map { [$0] } ?? []))
            return
        }
        if def.kind.lowercased() == "btree" || def.kind.lowercased() == "b+tree" || def.kind.lowercased() == "b-tree" {
            let path = URL(fileURLWithPath: config.dataDir).appendingPathComponent("indexes").appendingPathComponent("\(def.table)__\(def.name).bt").path
            let qos = DispatchQoS.fromConfig(config.bufferFlushQoS)
            let idx = try FileBPlusTreeIndex(path: path,
                                             pageSize: config.pageSizeBytes,
                                             capacityPages: config.indexBufferPoolPages,
                                             flushQoS: qos,
                                             ioHintsEnabled: config.ioSequentialReadHint,
                                             walFullSyncEnabled: config.walFullFSyncEnabled)
            let cols = def.columns ?? (def.column.map { [$0] } ?? [])
            map[def.name] = (columns: cols, backend: .persistentBTree(idx))
            systemCatalog?.registerIndex(name: def.name,
                                          table: def.table,
                                          kind: def.kind,
                                          physicalPath: path,
                                          columns: cols)
        } else {
            let cols = def.columns ?? (def.column.map { [$0] } ?? [])
            map[def.name] = (columns: cols, backend: .anyString(AnyStringIndex(kind: def.kind)))
            systemCatalog?.registerIndex(name: def.name,
                                          table: def.table,
                                          kind: def.kind,
                                          physicalPath: nil,
                                          columns: cols)
        }
        indexes[def.table] = map
    }

    private func physicalPath(for def: IndexDef) -> String? {
        if def.kind.lowercased() == "btree" || def.kind.lowercased() == "b+tree" || def.kind.lowercased() == "b-tree" {
            return URL(fileURLWithPath: config.dataDir).appendingPathComponent("indexes").appendingPathComponent("\(def.table)__\(def.name).bt").path
        }
        return nil
    }
}
