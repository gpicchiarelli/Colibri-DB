//
//  Database+GlobalWAL.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-27.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Global WAL integration helpers for Database operations

import Foundation

extension Database {
    
    // MARK: - Global WAL Helper Methods
    
    /// Helper to log transaction begin to global WAL
    func logTransactionBegin(tid: UInt64, isolationLevel: IsolationLevel) -> UInt64 {
        guard let wal = globalWAL else { return 0 }
        
        let record = WALBeginRecord(
            dbId: wal.dbId,
            txId: tid,
            isolationLevel: isolationLevel
        )
        
        return (try? wal.append(record)) ?? 0
    }
    
    /// Helper to log transaction commit to global WAL
    func logTransactionCommit(tid: UInt64, preparedLSN: UInt64? = nil) -> UInt64 {
        guard let wal = globalWAL else { return 0 }
        
        let record = WALCommitRecord(
            dbId: wal.dbId,
            txId: tid,
            preparedLSN: preparedLSN
        )
        
        return (try? wal.append(record)) ?? 0
    }
    
    /// Helper to log transaction abort to global WAL
    func logTransactionAbort(tid: UInt64, reason: String? = nil) -> UInt64 {
        guard let wal = globalWAL else { return 0 }
        
        let record = WALAbortRecord(
            dbId: wal.dbId,
            txId: tid,
            reason: reason
        )
        
        return (try? wal.append(record)) ?? 0
    }
    
    /// Helper to log heap insert to global WAL
    func logHeapInsert(tid: UInt64, table: String, pageId: UInt64, slotId: UInt16, row: Row) -> UInt64 {
        guard let wal = globalWAL else { return 0 }
        
        do {
            let rowData = try JSONEncoder().encode(row)
            let record = WALHeapInsertRecord(
                dbId: wal.dbId,
                txId: tid,
                tableId: table,
                pageId: pageId,
                slotId: slotId,
                rowData: rowData
            )
            
            return try wal.append(record)
        } catch {
            return 0
        }
    }
    
    /// Helper to log heap update to global WAL
    func logHeapUpdate(tid: UInt64, table: String, pageId: UInt64, slotId: UInt16, oldRow: Row, newRow: Row) -> UInt64 {
        guard let wal = globalWAL else { return 0 }
        
        do {
            let oldRowData = try JSONEncoder().encode(oldRow)
            let newRowData = try JSONEncoder().encode(newRow)
            let record = WALHeapUpdateRecord(
                dbId: wal.dbId,
                txId: tid,
                tableId: table,
                pageId: pageId,
                slotId: slotId,
                oldRowData: oldRowData,
                newRowData: newRowData
            )
            
            return try wal.append(record)
        } catch {
            return 0
        }
    }
    
    /// Helper to log heap delete to global WAL
    func logHeapDelete(tid: UInt64, table: String, pageId: UInt64, slotId: UInt16, row: Row) -> UInt64 {
        guard let wal = globalWAL else { return 0 }
        
        do {
            let rowData = try JSONEncoder().encode(row)
            let record = WALHeapDeleteRecord(
                dbId: wal.dbId,
                txId: tid,
                tableId: table,
                pageId: pageId,
                slotId: slotId,
                rowData: rowData
            )
            
            return try wal.append(record)
        } catch {
            return 0
        }
    }
    
    /// Helper to log index insert to global WAL
    func logIndexInsert(tid: UInt64, indexId: String, table: String, keyBytes: Data, rid: RID) -> UInt64 {
        guard let wal = globalWAL else { return 0 }
        
        let record = WALIndexInsertRecord(
            dbId: wal.dbId,
            txId: tid,
            indexId: indexId,
            tableId: table,
            keyBytes: keyBytes,
            ridPageId: rid.pageId,
            ridSlotId: rid.slotId
        )
        
        return (try? wal.append(record)) ?? 0
    }
    
    /// Helper to log index delete to global WAL
    func logIndexDelete(tid: UInt64, indexId: String, table: String, keyBytes: Data, rid: RID) -> UInt64 {
        guard let wal = globalWAL else { return 0 }
        
        let record = WALIndexDeleteRecord(
            dbId: wal.dbId,
            txId: tid,
            indexId: indexId,
            tableId: table,
            keyBytes: keyBytes,
            ridPageId: rid.pageId,
            ridSlotId: rid.slotId
        )
        
        return (try? wal.append(record)) ?? 0
    }
    
    /// Helper to log CLR (Compensation Log Record) for undo operations
    func logCLRUndoInsert(tid: UInt64, table: String, rid: RID, nextUndoLSN: UInt64) -> UInt64 {
        guard let wal = globalWAL else { return 0 }
        
        let record = WALCLRRecord(
            dbId: wal.dbId,
            txId: tid,
            undoNextLSN: nextUndoLSN,
            undoneOperationLSN: txLastLSN[tid] ?? 0,
            undoAction: .heapInsert(pageId: rid.pageId, slotId: rid.slotId)
        )
        
        return (try? wal.append(record)) ?? 0
    }
    
    /// Helper to log CLR for undo delete
    func logCLRUndoDelete(tid: UInt64, table: String, row: Row, nextUndoLSN: UInt64) -> UInt64 {
        guard let wal = globalWAL else { return 0 }
        
        do {
            let rowData = try JSONEncoder().encode(row)
            let record = WALCLRRecord(
                dbId: wal.dbId,
                txId: tid,
                undoNextLSN: nextUndoLSN,
                undoneOperationLSN: txLastLSN[tid] ?? 0,
                undoAction: .heapDelete(pageId: 0, slotId: 0, rowData: rowData)  // Page/slot determined at undo time
            )
            
            return try wal.append(record)
        } catch {
            return 0
        }
    }
    
    /// Helper to log CLR for undo update operation
    func logCLRUndoUpdate(tid: UInt64, table: String, rid: RID, oldRow: Row, newRow: Row, nextUndoLSN: UInt64) -> UInt64 {
        guard let wal = globalWAL else { return 0 }
        
        do {
            let oldRowData = try JSONEncoder().encode(oldRow)
            
            let record = WALCLRRecord(
                dbId: wal.dbId,
                txId: tid,
                undoNextLSN: nextUndoLSN,
                undoneOperationLSN: txLastLSN[tid] ?? 0,
                undoAction: .heapUpdate(pageId: rid.pageId, slotId: rid.slotId, originalData: oldRowData)
            )
            
            return try wal.append(record)
        } catch {
            return 0
        }
    }

    /// Helper to flush pending WAL records
    func flushWAL() throws {
        try globalWAL?.groupCommitSync()
    }
    
    /// Get current flushed LSN from global WAL
    var walFlushedLSN: UInt64 {
        return globalWAL?.flushedLSN ?? 0
    }
    
    /// Flush WAL up to specific LSN
    func flushWAL(upTo lsn: UInt64) throws {
        try globalWAL?.flush(upTo: lsn)
    }
}
