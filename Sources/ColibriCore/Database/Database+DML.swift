//
//  Database+DML.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: DML conduit implementing insert, update, and delete plumbing.

import Foundation
// MARK: - DML (Insert/Delete)

extension Database {
    /// Inserts a row into a table.
    /// - Parameters:
    ///   - name: Table name.
    ///   - row: Row values by column name.
    /// - Returns: RID of the inserted row.
    /// - Throws: `DBError.notFound` if table does not exist.
    public func insert(into name: String, row: Row) throws -> RID { try insert(into: name, row: row, tid: nil) }

    /// Inserts a row into a table within an optional transaction.
    /// - Parameters:
    ///   - name: Table name.
    ///   - row: Row values by column name.
    ///   - tid: Optional transaction id; when present, operations are logged as transactional.
    /// - Returns: RID of the inserted row.
    /// - Throws: `DBError.notFound` if table does not exist.
    public func insert(into name: String, row: Row, tid: UInt64?) throws -> RID {
        try assertTableRegistered(name)
        let tableHandle = try lockManager.lock(.table(name), mode: .exclusive, tid: tid ?? 0, timeout: config.lockTimeoutSeconds)
        defer { if tid == nil { lockManager.unlock(tableHandle) } }
        if var t = tablesMem[name] {
            let rid = try t.insert(row)
            tablesMem[name] = t
            mvcc.registerInsert(table: name, rid: rid, row: row, tid: tid)
            updateIndexes(table: name, row: row, rid: rid)
            if let tid = tid {
                var state = txStates[tid] ?? TxState()
                state.ops.append(TxOp(kind: .insert, table: name, rid: rid, row: row))
                txStates[tid] = state
            }
            return rid
        }
        if let ft = tablesFile[name] {
            var rid: RID
            if let tid = tid, let w = wal {
                _ = try? w.appendInsertPre(tid: tid, table: name, row: row, prevLSN: txLastLSN[tid] ?? 0)
                rid = try ft.insert(row) // pageLSN left as is for MVP
                let l = (try? w.appendInsertDone(tid: tid, table: name, rid: rid, prevLSN: txLastLSN[tid] ?? 0)) ?? 0
                txLastLSN[tid] = l
                // DPT recLSN
                if dpt[rid.pageId] == nil { dpt[rid.pageId] = lastDBLSN }
                var state = txStates[tid] ?? TxState()
                state.ops.append(TxOp(kind: .insert, table: name, rid: rid, row: row))
                txStates[tid] = state
            } else {
                // Autocommit: write row, then log insertDone to enable idempotent REDO by RID
                rid = try ft.insert(row)
                if let w = wal { _ = try? w.appendInsertDone(tid: 0, table: name, rid: rid) }
            }
            mvcc.registerInsert(table: name, rid: rid, row: row, tid: tid)
            updateIndexes(table: name, row: row, rid: rid)
            return rid
        }
        throw DBError.notFound("Table \(name)")
    }

    /// MVP: Updates rows where `matchColumn == matchValue`, setting columns from `set`.
    /// Returns number of rows updated (append-only update semantics).
    public func updateEquals(table: String,
                             matchColumn: String,
                             matchValue: Value,
                             set newValues: [String: Value],
                             tid: UInt64?) throws -> Int {
        let handle = try lockManager.lock(.table(table), mode: .exclusive, tid: tid ?? 0, timeout: config.lockTimeoutSeconds)
        defer { if tid == nil { lockManager.unlock(handle) } }
        var updated = 0
        for (rid, row) in try scan(table, tid: tid) {
            if row[matchColumn] == matchValue {
                var updatedRow = row
                for (k, v) in newValues { updatedRow[k] = v }
                // Append-only update: insert new row, leave old for GC
                _ = try insert(into: table, row: updatedRow, tid: tid)
                updated += 1
            }
        }
        return updated
    }

    /// Deletes rows where `column == value`.
    /// - Parameters:
    ///   - table: Table name.
    ///   - column: Column name to compare.
    ///   - value: Value to match.
    /// - Returns: Number of rows deleted.
    /// - Throws: `DBError.notFound` if table does not exist.
    public func deleteEquals(table: String, column: String, value: Value) throws -> Int {
        try deleteEquals(table: table, column: column, value: value, tid: nil)
    }

    /// Transaction-aware delete where `column == value`.
    /// If `tid` is provided, logs a before-image and defers pageLSN.
    /// - Parameters:
    ///   - table: Table name.
    ///   - column: Column name to compare.
    ///   - value: Value to match.
    ///   - tid: Optional transaction id.
    /// - Returns: Number of rows deleted.
    /// - Throws: `DBError.notFound` if table does not exist.
    public func deleteEquals(table: String, column: String, value: Value, tid: UInt64?) throws -> Int {
        try assertTableRegistered(table)
        let handle = try lockManager.lock(.table(table), mode: .exclusive, tid: tid ?? 0, timeout: config.lockTimeoutSeconds)
        defer { if tid == nil { lockManager.unlock(handle) } }
        // Try to use an index on the given column (prefer persistent BTree)
        var ridsFromIndex: [RID] = []
        var skipIndexName: String? = nil
        if let tableMap = indexes[table] {
            // Gate by system catalog: only consider indexes registered for this table
            let allowed: Set<String>
            if let sc = systemCatalog {
                let objs = sc.logicalObjects(kind: .index).filter { $0.parentName == table }
                allowed = Set(objs.map { $0.name })
            } else {
                allowed = Set(tableMap.keys)
            }
            // Find best index: single-column index on 'column'
            var best: (name: String, def: (columns: [String], backend: IndexBackend))? = nil
            for (name, def) in tableMap where allowed.contains(name) {
                guard def.columns.count == 1, def.columns[0] == column else { continue }
                if case .persistentBTree = def.backend { best = (name, def); break }
                if best == nil { best = (name, def) }
            }
            if let sel = best {
                skipIndexName = sel.name
                switch sel.def.backend {
                case .anyString(let idx):
                    ridsFromIndex = idx.searchEquals(stringFromValue(value))
                case .persistentBTree(let f):
                    ridsFromIndex = f.searchEquals(value)
                    // Optimize: remove entire key from predicate index in one shot
                    _ = try? f.removeAll(key: value)
                }
            } else {
                // Try composite persistent BTree with leading column = predicate
                for (name, def) in tableMap where allowed.contains(name) {
                    guard def.columns.count > 1, def.columns.first == column else { continue }
                    if case .persistentBTree(let f) = def.backend {
                        skipIndexName = name
                        ridsFromIndex = f.rangePrefixedBy([value])
                        break
                    }
                }
            }
        }

        var deleted = 0
        if !ridsFromIndex.isEmpty {
            // Fast path via index: dedup and remove by RID
            var seen = Set<RID>()
            for rid in ridsFromIndex {
                if seen.contains(rid) { continue }
                seen.insert(rid)
                // Read row to update other indexes correctly
                let row: Row
                if var t = tablesMem[table] {
                    do { row = try t.read(rid) } catch { continue }
                    // remove from storage
                    try t.remove(rid)
                    tablesMem[table] = t
                    mvcc.registerDelete(table: table, rid: rid, row: row, tid: tid)
                } else if let ft = tablesFile[table] {
                    do { row = try ft.read(rid) } catch { continue }
                    var lsn: UInt64 = 0
                    if let tid = tid, let w = wal {
                        _ = try? w.appendDelete(tid: tid, table: table, rid: rid, row: row)
                        try ft.remove(rid)
                        var state = txStates[tid] ?? TxState()
                        state.ops.append(TxOp(kind: .delete, table: table, rid: rid, row: row))
                        txStates[tid] = state
                        if dpt[rid.pageId] == nil { dpt[rid.pageId] = lastDBLSN }
                        mvcc.registerDelete(table: table, rid: rid, row: row, tid: tid)
                    } else {
                        if let w = wal { lsn = (try? w.appendDelete(table: table, rid: rid)) ?? 0; lastDBLSN = max(lastDBLSN, lsn) }
                        if lsn != 0, dpt[rid.pageId] == nil { dpt[rid.pageId] = lsn }
                        if lsn != 0 { try ft.remove(rid, pageLSN: lsn) } else { try ft.remove(rid) }
                        mvcc.registerDelete(table: table, rid: rid, row: row, tid: nil)
                    }
                } else {
                    continue
                }
                // Update all indexes for this row
                removeFromIndexes(table: table, row: row, rid: rid, skipIndexName: skipIndexName)
                deleted += 1
            }
            return deleted
        }

        // Fallback: scan table
        let rows = try scan(table, tid: tid)
        for (rid, row) in rows {
            if let v = row[column], v == value {
                if var t = tablesMem[table] {
                    try t.remove(rid)
                    tablesMem[table] = t
                    mvcc.registerDelete(table: table, rid: rid, row: row, tid: tid)
                } else if let ft = tablesFile[table] {
                    var lsn: UInt64 = 0
                    if let tid = tid, let w = wal {
                        _ = try? w.appendDelete(tid: tid, table: table, rid: rid, row: row)
                        try ft.remove(rid)
                        var state = txStates[tid] ?? TxState()
                        state.ops.append(TxOp(kind: .delete, table: table, rid: rid, row: row))
                        txStates[tid] = state
                        if dpt[rid.pageId] == nil { dpt[rid.pageId] = lastDBLSN }
                        mvcc.registerDelete(table: table, rid: rid, row: row, tid: tid)
                    } else {
                        if let w = wal, let payload = try? JSONSerialization.data(withJSONObject: ["op":"delete","table":table,"rid":[rid.pageId,Int(rid.slotId)]], options: []) {
                            lsn = (try? w.append(record: payload)) ?? 0
                            lastDBLSN = max(lastDBLSN, lsn)
                        }
                        if lsn != 0, dpt[rid.pageId] == nil { dpt[rid.pageId] = lsn }
                        if lsn != 0 { try ft.remove(rid, pageLSN: lsn) } else { try ft.remove(rid) }
                        mvcc.registerDelete(table: table, rid: rid, row: row, tid: nil)
                    }
                }
                removeFromIndexes(table: table, row: row, rid: rid)
                deleted += 1
            }
        }
        return deleted
    }

    /// Deletes rows matching multiple equality predicates (AND semantics).
    /// - Parameters:
    ///   - table: Table name.
    ///   - predicates: Array of (column, value) pairs.
    /// - Returns: Number of rows deleted.
    /// - Throws: `DBError.notFound` if table does not exist.
    public func deleteEqualsMulti(table: String, predicates: [(String, Value)]) throws -> Int { try deleteEqualsMulti(table: table, predicates: predicates, tid: nil) }

    /// Transaction-aware multi-predicate delete (AND semantics).
    /// - Parameters:
    ///   - table: Table name.
    ///   - predicates: Array of (column, value) pairs.
    ///   - tid: Optional transaction id.
    /// - Returns: Number of rows deleted.
    /// - Throws: `DBError.notFound` if table does not exist.
    public func deleteEqualsMulti(table: String, predicates: [(String, Value)], tid: UInt64?) throws -> Int {
        guard !predicates.isEmpty else { return 0 }
        let handle = try lockManager.lock(.table(table), mode: .exclusive, tid: tid ?? 0, timeout: config.lockTimeoutSeconds)
        defer { if tid == nil { lockManager.unlock(handle) } }
        // Build lookup for convenience
        var predMap: [String: Value] = [:]
        let predCols: [String] = predicates.map { k, _ in k }
        for (k, v) in predicates { predMap[k] = v }

        // Try index-based strategies in order: exact composite BTree, prefixed composite BTree, single-column
        var rids: [RID] = []
        var skipIndexName: String? = nil
        if let tableMap = indexes[table] {
            let allowed: Set<String>
            if let sc = systemCatalog {
                let objs = sc.logicalObjects(kind: .index).filter { $0.parentName == table }
                allowed = Set(objs.map { $0.name })
            } else {
                allowed = Set(tableMap.keys)
            }
            // Exact composite BTree match (all columns present, any order)
            for (name, def) in tableMap where allowed.contains(name) {
                guard case .persistentBTree(let f) = def.backend else { continue }
                guard def.columns.count == predCols.count else { continue }
                var values: [Value] = []
                var ok = true
                for c in def.columns { guard let v = predMap[c] else { ok = false; break }; values.append(v) }
                if ok {
                    rids = f.searchEquals(composite: values)
                    _ = try? f.removeAll(composite: values) // bulk remove on predicate index
                    skipIndexName = name
                    break
                }
            }
            // Prefixed composite BTree (leading columns present in order)
            if rids.isEmpty {
                for (name, def) in tableMap where allowed.contains(name) {
                    guard case .persistentBTree(let f) = def.backend else { continue }
                    guard def.columns.count > predCols.count else { continue }
                    var prefixValues: [Value] = []
                    var ok = true
                    for i in 0..<predicates.count {
                        let col = def.columns[i]
                        guard let v = predMap[col] else { ok = false; break }
                        prefixValues.append(v)
                    }
                    if ok {
                        rids = f.rangePrefixedBy(prefixValues)
                        break
                    }
                }
            }
            // Single-column index (use first predicate that has an index)
            if rids.isEmpty {
                for (name, def) in tableMap where allowed.contains(name) {
                    guard def.columns.count == 1, let v = predMap[def.columns[0]] else { continue }
                    switch def.backend {
                    case .anyString(let idx):
                        rids = idx.searchEquals(stringFromValue(v)); skipIndexName = name
                        break
                    case .persistentBTree(let f):
                        rids = f.searchEquals(v); skipIndexName = name
                        break
                    }
                }
            }
        }

        var deleted = 0
        if !rids.isEmpty {
            var seen = Set<RID>()
            for rid in rids {
                if seen.contains(rid) { continue }
                seen.insert(rid)
                // Read row and check predicates
                let row: Row
                if var t = tablesMem[table] {
                    guard let r = try? t.read(rid) else { continue }
                    row = r
                    // verify
                    var match = true
                    for (k, v) in predicates { if row[k] != v { match = false; break } }
                    if !match { continue }
                    mvcc.registerDelete(table: table, rid: rid, row: row, tid: tid)
                    try t.remove(rid)
                    tablesMem[table] = t
                } else if let ft = tablesFile[table] {
                    guard let r = try? ft.read(rid) else { continue }
                    row = r
                    var match = true
                    for (k, v) in predicates { if row[k] != v { match = false; break } }
                    if !match { continue }
                    var lsn: UInt64 = 0
                    if let tid = tid, let w = wal {
                        _ = try? w.appendDelete(tid: tid, table: table, rid: rid, row: row)
                        try ft.remove(rid)
                        var state = txStates[tid] ?? TxState()
                        state.ops.append(TxOp(kind: .delete, table: table, rid: rid, row: row))
                        txStates[tid] = state
                        mvcc.registerDelete(table: table, rid: rid, row: row, tid: tid)
                    } else {
                        if let w = wal, let payload = try? JSONSerialization.data(withJSONObject: ["op":"delete","table":table,"rid":[rid.pageId,Int(rid.slotId)]], options: []) {
                            lsn = (try? w.append(record: payload)) ?? 0
                            lastDBLSN = max(lastDBLSN, lsn)
                        }
                        if lsn != 0 { try ft.remove(rid, pageLSN: lsn) } else { try ft.remove(rid) }
                        mvcc.registerDelete(table: table, rid: rid, row: row, tid: nil)
                    }
                } else { continue }
                // Update indexes (skip predicate index if bulk-removed)
                removeFromIndexes(table: table, row: row, rid: rid, skipIndexName: skipIndexName)
                deleted += 1
            }
            return deleted
        }

        // Fallback: full scan
        for (rid, row) in try scan(table, tid: tid) {
            var match = true
            for (k, v) in predicates { if row[k] != v { match = false; break } }
            if !match { continue }
            if var t = tablesMem[table] {
                mvcc.registerDelete(table: table, rid: rid, row: row, tid: tid)
                try t.remove(rid)
                tablesMem[table] = t
            } else if let ft = tablesFile[table] {
                var lsn: UInt64 = 0
                if let tid = tid, let w = wal {
                    _ = try? w.appendDelete(tid: tid, table: table, rid: rid, row: row)
                    try ft.remove(rid)
                        var state = txStates[tid] ?? TxState()
                        state.ops.append(TxOp(kind: .delete, table: table, rid: rid, row: row))
                        txStates[tid] = state
                    mvcc.registerDelete(table: table, rid: rid, row: row, tid: tid)
                } else {
                    if let w = wal, let payload = try? JSONSerialization.data(withJSONObject: ["op":"delete","table":table,"rid":[rid.pageId,Int(rid.slotId)]], options: []) {
                        lsn = (try? w.append(record: payload)) ?? 0
                        lastDBLSN = max(lastDBLSN, lsn)
                    }
                    if lsn != 0 { try ft.remove(rid, pageLSN: lsn) } else { try ft.remove(rid) }
                    mvcc.registerDelete(table: table, rid: rid, row: row, tid: nil)
                }
            }
            removeFromIndexes(table: table, row: row, rid: rid)
            deleted += 1
        }
        return deleted
    }
}

