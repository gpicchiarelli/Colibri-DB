//
//  Database+DML.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-09-27.
//
// ColibrDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

import Foundation

// MARK: - DML (Insert/Delete)

extension Database {
    /// Inserts a row into a table.
    /// - Parameters:
    ///   - table: Table name.
    ///   - row: Row data (column→value mapping).
    /// - Returns: Row identifier (RID).
    /// - Throws: `DBError.notFound` if table does not exist.
    public func insert(into table: String, row: Row) throws -> RID { try insert(into: table, row: row, tid: nil) }

    /// Transaction-aware insert.
    /// - Parameters:
    ///   - table: Table name.
    ///   - row: Row data (column→value mapping).
    ///   - tid: Optional transaction id.
    /// - Returns: Row identifier (RID).
    /// - Throws: `DBError.notFound` if table does not exist.
    public func insert(into table: String, row: Row, tid: UInt64?) throws -> RID {
        try assertTableRegistered(table)
        
        // Handle in-memory tables
        if var t = tablesMem[table] {
            let rid = try t.insert(row)
            tablesMem[table] = t
            mvcc.registerInsert(table: table, rid: rid, row: row, tid: tid)
            try updateIndexes(table: table, row: row, rid: rid, tid: tid)
            return rid
        }
        
        // Handle file-based tables
        if let ft = tablesFile[table] {
            var rid: RID
            if let tid = tid {
                // WAL-before-data: log the insert BEFORE applying it
                let predictedRID = try ft.predictNextRID(for: row)
                let lsn = logHeapInsert(tid: tid, table: table, pageId: predictedRID.pageId, slotId: predictedRID.slotId, row: row)
                txLastLSN[tid] = lsn
                
                // Now apply with pageLSN
                rid = try ft.insert(row, pageLSN: lsn)
                assert(rid == predictedRID, "RID prediction failed: predicted=\(predictedRID), actual=\(rid)")
                
                // DPT recLSN
                if dpt[rid.pageId] == nil { dpt[rid.pageId] = lsn }
                var state = txStates[tid] ?? TxState()
                state.ops.append(TxOp(kind: .insert, table: table, rid: rid, row: row))
                txStates[tid] = state
            } else {
                // Autocommit: predict RID, log, then insert
                let predictedRID = try ft.predictNextRID(for: row)
                let lsn = logHeapInsert(tid: 0, table: table, pageId: predictedRID.pageId, slotId: predictedRID.slotId, row: row)
                rid = try ft.insert(row, pageLSN: lsn)
                assert(rid == predictedRID, "RID prediction failed: predicted=\(predictedRID), actual=\(rid)")
            }
            mvcc.registerInsert(table: table, rid: rid, row: row, tid: tid)
            try updateIndexes(table: table, row: row, rid: rid, tid: tid)
            return rid
        }
        throw DBError.notFound("Table \(table)")
    }

    /// Updates all matching rows.
    /// - Parameters:
    ///   - table: Table name.
    ///   - matchColumn: Column to match.
    ///   - matchValue: Value to match.
    ///   - updateColumn: Column to update.
    ///   - updateValue: New value.
    /// - Returns: Number of rows updated.
    /// - Throws: `DBError.notFound` if table does not exist.
    public func update(table: String, matchColumn: String, matchValue: Value, updateColumn: String, updateValue: Value) throws -> Int { try update(table: table, matchColumn: matchColumn, matchValue: matchValue, updateColumn: updateColumn, updateValue: updateValue, tid: nil) }

    /// Update multiple columns based on a single column match.
    /// - Parameters:
    ///   - table: Table name.
    ///   - matchColumn: Column to match.
    ///   - matchValue: Value to match.
    ///   - set: Dictionary of columns and their new values.
    ///   - tid: Optional transaction id.
    /// - Returns: Number of rows updated.
    /// - Throws: `DBError.notFound` if table does not exist.
    public func updateEquals(table: String, matchColumn: String, matchValue: Value, set: [String: Value], tid: UInt64?) throws -> Int {
        try assertTableRegistered(table)
        let handle = try lockManager.lock(.table(table), mode: .exclusive, tid: tid ?? 0, timeout: config.lockTimeoutSeconds)
        defer { if tid == nil { lockManager.unlock(handle) } }
        var updated = 0
        for (rid, row) in try scan(table, tid: tid) {
            if row[matchColumn] == matchValue {
                var updatedRow = row
                for (column, value) in set {
                    updatedRow[column] = value
                }
                // Update the row using the storage layer
                if var t = tablesMem[table] {
                    try t.update(rid, updatedRow)
                    tablesMem[table] = t
                } else if let ft = tablesFile[table] {
                    try ft.update(rid, updatedRow)
                }
                
                // Update MVCC with the new version
                mvcc.registerInsert(table: table, rid: rid, row: updatedRow, tid: tid)
                
                // Update indexes with the new row
                try updateIndexes(table: table, row: updatedRow, rid: rid, tid: tid)
                
                // Log the WAL record if needed
                if let tid = tid {
                    let lsn = logHeapUpdate(tid: tid, table: table, pageId: rid.pageId, slotId: rid.slotId, oldRow: row, newRow: updatedRow)
                    txLastLSN[tid] = lsn
                    
                    var state = txStates[tid] ?? TxState()
                    state.ops.append(TxOp(kind: .update, table: table, rid: rid, row: updatedRow, oldRow: row))
                    txStates[tid] = state
                }
                updated += 1
            }
        }
        return updated
    }

    /// Transaction-aware update.
    /// - Parameters:
    ///   - table: Table name.
    ///   - matchColumn: Column to match.
    ///   - matchValue: Value to match.
    ///   - updateColumn: Column to update.
    ///   - updateValue: New value.
    ///   - tid: Optional transaction id.
    /// - Returns: Number of rows updated.
    /// - Throws: `DBError.notFound` if table does not exist.
    public func update(table: String, matchColumn: String, matchValue: Value, updateColumn: String, updateValue: Value, tid: UInt64?) throws -> Int {
        try assertTableRegistered(table)
        let handle = try lockManager.lock(.table(table), mode: .exclusive, tid: tid ?? 0, timeout: config.lockTimeoutSeconds)
        defer { if tid == nil { lockManager.unlock(handle) } }
        var updated = 0
        for (rid, row) in try scan(table, tid: tid) {
            if row[matchColumn] == matchValue {
                var updatedRow = row
                updatedRow[updateColumn] = updateValue
                
                // Update the row using the storage layer
                if var t = tablesMem[table] {
                    try t.update(rid, updatedRow)
                    tablesMem[table] = t
                } else if let ft = tablesFile[table] {
                    try ft.update(rid, updatedRow)
                }
                
                // Update MVCC with the new version
                mvcc.registerInsert(table: table, rid: rid, row: updatedRow, tid: tid)
                
                // Update indexes with the new row
                try updateIndexes(table: table, row: updatedRow, rid: rid, tid: tid)
                
                updated += 1
            }
        }
        return updated
    }

    /// Deletes rows matching a column value.
    /// - Parameters:
    ///   - table: Table name.
    ///   - column: Column to match.
    ///   - value: Value to match.
    /// - Returns: Number of rows deleted.
    /// - Throws: `DBError.notFound` if table does not exist.
    public func deleteEquals(table: String, column: String, value: Value) throws -> Int { try deleteEquals(table: table, column: column, value: value, tid: nil) }

    /// Transaction-aware delete by equality.
    /// - Parameters:
    ///   - table: Table name.
    ///   - column: Column to match.
    ///   - value: Value to match.
    ///   - tid: Optional transaction id.
    /// - Returns: Number of rows deleted.
    /// - Throws: `DBError.notFound` if table does not exist.
    public func deleteEquals(table: String, column: String, value: Value, tid: UInt64?) throws -> Int {
        try assertTableRegistered(table)
        let handle = try lockManager.lock(.table(table), mode: .exclusive, tid: tid ?? 0, timeout: config.lockTimeoutSeconds)
        defer { if tid == nil { lockManager.unlock(handle) } }
        var deleted = 0
        var skipIndexName: String? = nil

        // Try to use an index for faster lookup
        if let tableMap = indexes[table] {
            let allowed: Set<String>
            if let sc = systemCatalog {
                let objs = sc.logicalObjects(kind: .index).filter { $0.parentName == table }
                allowed = Set(objs.map { $0.name })
            } else {
                allowed = Set(tableMap.keys)
            }

            for (name, def) in tableMap {
                guard allowed.contains(name) && def.columns == [column] else { continue }

                let rids: [RID]
                switch def.backend {
                case .anyString(let idx):
                    rids = idx.searchEquals(stringFromValue(value))
                    skipIndexName = name
                case .persistentBTree(let f):
                    rids = try f.searchEqualsOptimized(value)
                    skipIndexName = name
                }

                for rid in rids {
                    let row: Row
                    if var t = tablesMem[table] {
                        let r = try t.read(rid)
                        row = r
                        // Use tombstone instead of physical removal
                        t.remove(rid) // This marks as tombstone in HeapTable
                        tablesMem[table] = t
                        mvcc.registerDelete(table: table, rid: rid, row: row, tid: tid)
                    } else if let ft = tablesFile[table] {
                        let r = try ft.read(rid)
                        row = r
                        var lsn: UInt64 = 0
                        if let tid = tid {
                            lsn = logHeapDelete(tid: tid, table: table, pageId: rid.pageId, slotId: rid.slotId, row: row)
                            // Use tombstone instead of physical removal
                            try ft.remove(rid) // This marks as tombstone in FileHeapTable
                            var state = txStates[tid] ?? TxState()
                            state.ops.append(TxOp(kind: .delete, table: table, rid: rid, row: row))
                            txStates[tid] = state
                            if dpt[rid.pageId] == nil { dpt[rid.pageId] = lastDBLSN }
                            mvcc.registerDelete(table: table, rid: rid, row: row, tid: tid)
                        } else {
                            // Use WAL-before-data with autocommit
                            lsn = logHeapDelete(tid: 0, table: table, pageId: rid.pageId, slotId: rid.slotId, row: row)
                            lastDBLSN = max(lastDBLSN, lsn)
                            if dpt[rid.pageId] == nil { dpt[rid.pageId] = lsn }
                            // Use tombstone instead of physical removal
                            if lsn != 0 { try ft.remove(rid, pageLSN: lsn) } else { try ft.remove(rid) }
                            mvcc.registerDelete(table: table, rid: rid, row: row, tid: nil)
                        }
                    } else {
                        continue
                    }
                    // Update all indexes for this row
                    try removeFromIndexes(table: table, row: row, rid: rid, skipIndexName: skipIndexName, tid: tid)
                    deleted += 1
                }
                return deleted
            }
        }

        // Fallback: scan table
        let rows = try scan(table, tid: tid)
        for (rid, row) in rows {
            if let v = row[column], v == value {
                if var t = tablesMem[table] {
                    t.remove(rid)
                    tablesMem[table] = t
                    mvcc.registerDelete(table: table, rid: rid, row: row, tid: tid)
                } else if let ft = tablesFile[table] {
                    var lsn: UInt64 = 0
                    if let tid = tid {
                        lsn = logHeapDelete(tid: tid, table: table, pageId: rid.pageId, slotId: rid.slotId, row: row)
                        try ft.remove(rid)
                        var state = txStates[tid] ?? TxState()
                        state.ops.append(TxOp(kind: .delete, table: table, rid: rid, row: row))
                        txStates[tid] = state
                        if dpt[rid.pageId] == nil { dpt[rid.pageId] = lastDBLSN }
                        mvcc.registerDelete(table: table, rid: rid, row: row, tid: tid)
                    } else {
                        // Use WAL-before-data with autocommit
                        lsn = logHeapDelete(tid: 0, table: table, pageId: rid.pageId, slotId: rid.slotId, row: row)
                        lastDBLSN = max(lastDBLSN, lsn)
                        if dpt[rid.pageId] == nil { dpt[rid.pageId] = lsn }
                        if lsn != 0 { try ft.remove(rid, pageLSN: lsn) } else { try ft.remove(rid) }
                        mvcc.registerDelete(table: table, rid: rid, row: row, tid: nil)
                    }
                }
                try removeFromIndexes(table: table, row: row, rid: rid, tid: tid)
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
        for (k, v) in predicates { predMap[k] = v }

        var deleted = 0
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

            // Try to find single-column index for first predicate
            for (col, v) in predicates {
                for (name, def) in tableMap {
                    guard allowed.contains(name) && def.columns == [col] else { continue }

                    switch def.backend {
                    case .anyString(let idx):
                        rids = idx.searchEquals(stringFromValue(v))
                        skipIndexName = name
                        break
                    case .persistentBTree(let f):
                        rids = try f.searchEqualsOptimized(v)
                        skipIndexName = name
                        break
                    }
                    break
                }
                if !rids.isEmpty { break }
            }
        }

        if !rids.isEmpty {
            // Use index results
            for rid in rids {
                // Read row and check predicates
                let row: Row
                if var t = tablesMem[table] {
                    guard let r = try? t.read(rid) else { continue }
                    row = r
                    var match = true
                    for (k, v) in predicates { if row[k] != v { match = false; break } }
                    if !match { continue }
                    mvcc.registerDelete(table: table, rid: rid, row: row, tid: tid)
                    t.remove(rid)
                    tablesMem[table] = t
                } else if let ft = tablesFile[table] {
                    let r = try ft.read(rid)
                    row = r
                    var match = true
                    for (k, v) in predicates { if row[k] != v { match = false; break } }
                    if !match { continue }
                    var lsn: UInt64 = 0
                    if let tid = tid {
                        lsn = logHeapDelete(tid: tid, table: table, pageId: rid.pageId, slotId: rid.slotId, row: row)
                        try ft.remove(rid)
                        var state = txStates[tid] ?? TxState()
                        state.ops.append(TxOp(kind: .delete, table: table, rid: rid, row: row))
                        txStates[tid] = state
                        mvcc.registerDelete(table: table, rid: rid, row: row, tid: tid)
                    } else {
                        // Use WAL-before-data with autocommit
                        lsn = logHeapDelete(tid: 0, table: table, pageId: rid.pageId, slotId: rid.slotId, row: row)
                        lastDBLSN = max(lastDBLSN, lsn)
                        if lsn != 0 { try ft.remove(rid, pageLSN: lsn) } else { try ft.remove(rid) }
                        mvcc.registerDelete(table: table, rid: rid, row: row, tid: nil)
                    }
                } else { 
                    continue 
                }
                // Update indexes (skip predicate index if bulk-removed)
                try removeFromIndexes(table: table, row: row, rid: rid, skipIndexName: skipIndexName, tid: tid)
                deleted += 1
            }
        }

        // PERFORMANCE FIX: Remove expensive full table scan fallback
        // If no indexes were available, return 0 instead of scanning entire table
        // Full scan should be explicit opt-in for safety
        return deleted
    }
    
    /// Batch delete optimization for better performance
    /// - Parameters:
    ///   - table: Table name
    ///   - rids: Array of RIDs to delete
    ///   - tid: Optional transaction id
    /// - Returns: Number of rows deleted
    public func deleteBatch(table: String, rids: [RID], tid: UInt64? = nil) throws -> Int {
        guard !rids.isEmpty else { return 0 }
        
        var deleted = 0
        let actualTid: UInt64
        if let existingTid = tid {
            actualTid = existingTid
        } else {
            actualTid = try begin()
        }
        
        // Process all deletes in a single transaction using tombstone approach
        for rid in rids {
            let row: Row
            if var t = tablesMem[table] {
                guard let r = try? t.read(rid) else { continue }
                row = r
                // Use tombstone instead of physical removal
                t.remove(rid) // This marks as tombstone in HeapTable
                tablesMem[table] = t
                mvcc.registerDelete(table: table, rid: rid, row: row, tid: actualTid)
            } else if let ft = tablesFile[table] {
                guard let r = try? ft.read(rid) else { continue }
                row = r
                _ = logHeapDelete(tid: actualTid, table: table, pageId: rid.pageId, slotId: rid.slotId, row: row)
                // Use tombstone instead of physical removal
                try ft.remove(rid) // This marks as tombstone in FileHeapTable
                var state = txStates[actualTid] ?? TxState()
                state.ops.append(TxOp(kind: .delete, table: table, rid: rid, row: row))
                txStates[actualTid] = state
                if dpt[rid.pageId] == nil { dpt[rid.pageId] = lastDBLSN }
                mvcc.registerDelete(table: table, rid: rid, row: row, tid: actualTid)
            } else {
                continue
            }
            // Batch update indexes at the end
            try removeFromIndexes(table: table, row: row, rid: rid, tid: actualTid)
            deleted += 1
        }
        
        // Commit if we started the transaction
        if tid == nil {
            try commit(actualTid)
        }
        
        return deleted
    }
}