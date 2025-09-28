//
//  Database+GlobalWALRecovery.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-27.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Global WAL recovery implementation using typed records

import Foundation

extension Database {
    
    // MARK: - Global WAL ARIES Recovery
    
    /// Performs ARIES-style recovery using typed WAL records from global WAL
    func replayGlobalWAL() throws {
        guard let globalWAL = globalWAL else { return }
        
        print("Starting Global WAL Recovery...")
        
        // Phase 1: Analysis - scan WAL to build ATT and DPT
        let (att, dpt, lastLSN) = try analysisPhase(globalWAL: globalWAL)
        print("Analysis complete. ATT: \(att.count) transactions, DPT: \(dpt.count) pages, lastLSN: \(lastLSN)")
        
        // Phase 2: REDO - replay all operations idempotently
        try redoPhase(globalWAL: globalWAL, dpt: dpt, lastLSN: lastLSN)
        print("REDO phase complete.")
        
        // Phase 3: UNDO - rollback uncommitted transactions
        try undoPhase(globalWAL: globalWAL, att: att)
        print("UNDO phase complete.")
        
        // Update database state
        self.lastDBLSN = lastLSN
        print("Global WAL Recovery completed successfully.")
    }
    
    // MARK: - Analysis Phase
    
    private func analysisPhase(globalWAL: FileWALManager) throws -> (att: [UInt64: UInt64], dpt: [UInt64: UInt64], lastLSN: UInt64) {
        var activeTransactionTable: [UInt64: UInt64] = [:]  // txId -> lastLSN
        var dirtyPageTable: [UInt64: UInt64] = [:]  // pageId -> recLSN
        var lastLSN: UInt64 = 0
        
        let records = try globalWAL.iterate(from: 1)
        
        for record in records {
            lastLSN = max(lastLSN, record.lsn)
            
            switch record {
            case let beginRecord as WALBeginRecord:
                activeTransactionTable[beginRecord.txId] = beginRecord.lsn
                
            case let commitRecord as WALCommitRecord:
                activeTransactionTable.removeValue(forKey: commitRecord.txId)
                
            case let abortRecord as WALAbortRecord:
                activeTransactionTable.removeValue(forKey: abortRecord.txId)
                
            case let heapRecord as WALHeapInsertRecord:
                activeTransactionTable[heapRecord.txId] = heapRecord.lsn
                if dirtyPageTable[heapRecord.recordPageId] == nil {
                    dirtyPageTable[heapRecord.recordPageId] = heapRecord.lsn
                }
                
            case let heapRecord as WALHeapUpdateRecord:
                activeTransactionTable[heapRecord.txId] = heapRecord.lsn
                if dirtyPageTable[heapRecord.recordPageId] == nil {
                    dirtyPageTable[heapRecord.recordPageId] = heapRecord.lsn
                }
                
            case let heapRecord as WALHeapDeleteRecord:
                activeTransactionTable[heapRecord.txId] = heapRecord.lsn
                if dirtyPageTable[heapRecord.recordPageId] == nil {
                    dirtyPageTable[heapRecord.recordPageId] = heapRecord.lsn
                }
                
            case let indexRecord as WALIndexInsertRecord:
                activeTransactionTable[indexRecord.txId] = indexRecord.lsn
                if dirtyPageTable[indexRecord.ridPageId] == nil {
                    dirtyPageTable[indexRecord.ridPageId] = indexRecord.lsn
                }
                
            case let indexRecord as WALIndexDeleteRecord:
                activeTransactionTable[indexRecord.txId] = indexRecord.lsn
                if dirtyPageTable[indexRecord.ridPageId] == nil {
                    dirtyPageTable[indexRecord.ridPageId] = indexRecord.lsn
                }
                
            case let clrRecord as WALCLRRecord:
                activeTransactionTable[clrRecord.txId] = clrRecord.lsn
                if let pageId = clrRecord.pageId {
                    if dirtyPageTable[pageId] == nil {
                        dirtyPageTable[pageId] = clrRecord.lsn
                    }
                }
                
            default:
                // Handle other record types as needed
                break
            }
        }
        
        return (att: activeTransactionTable, dpt: dirtyPageTable, lastLSN: lastLSN)
    }
    
    // MARK: - REDO Phase
    
    private func redoPhase(globalWAL: FileWALManager, dpt: [UInt64: UInt64], lastLSN: UInt64) throws {
        let records = try globalWAL.iterate(from: 1)
        
        for record in records {
            // Skip if this change was already applied (idempotency check)
            if !shouldRedo(record: record, dpt: dpt) {
                continue
            }
            
            try applyRedoOperation(record: record)
        }
    }
    
    private func shouldRedo(record: WALRecord, dpt: [UInt64: UInt64]) -> Bool {
        guard let pageId = record.pageId else { return true }
        
        // Check if page is in DPT (was dirty at crash)
        guard dpt[pageId] != nil else { return false }
        
        // Check PageLSN to avoid duplicate redo
        switch record {
        case let heapRecord as WALHeapInsertRecord:
            if let ft = tablesFile[heapRecord.tableId] {
                if let pageLSN = ft.getPageLSN(pageId) {
                    return pageLSN < record.lsn
                }
            }
        case let heapRecord as WALHeapUpdateRecord:
            if let ft = tablesFile[heapRecord.tableId] {
                if let pageLSN = ft.getPageLSN(pageId) {
                    return pageLSN < record.lsn
                }
            }
        case let heapRecord as WALHeapDeleteRecord:
            if let ft = tablesFile[heapRecord.tableId] {
                if let pageLSN = ft.getPageLSN(pageId) {
                    return pageLSN < record.lsn
                }
            }
        default:
            break
        }
        
        return true
    }
    
    private func applyRedoOperation(record: WALRecord) throws {
        switch record {
        case let heapRecord as WALHeapInsertRecord:
            try redoHeapInsert(record: heapRecord)
            
        case let heapRecord as WALHeapUpdateRecord:
            try redoHeapUpdate(record: heapRecord)
            
        case let heapRecord as WALHeapDeleteRecord:
            try redoHeapDelete(record: heapRecord)
            
        case let indexRecord as WALIndexInsertRecord:
            try redoIndexInsert(record: indexRecord)
            
        case let indexRecord as WALIndexDeleteRecord:
            try redoIndexDelete(record: indexRecord)
            
        case let clrRecord as WALCLRRecord:
            try redoCLR(record: clrRecord)
            
        default:
            // Skip transaction control records during REDO
            break
        }
    }
    
    private func redoHeapInsert(record: WALHeapInsertRecord) throws {
        guard let ft = tablesFile[record.tableId] else { return }
        
        let row = try JSONDecoder().decode(Row.self, from: record.rowData)
        let rid = RID(pageId: record.recordPageId, slotId: record.slotId)
        
        // Idempotent insert - check if already exists
        if (try? ft.read(rid)) != nil {
            return  // Already inserted
        }
        
        _ = try ft.insert(row, pageLSN: record.lsn)
    }
    
    private func redoHeapUpdate(record: WALHeapUpdateRecord) throws {
        guard let ft = tablesFile[record.tableId] else { return }
        
        let newRow = try JSONDecoder().decode(Row.self, from: record.newRowData)
        let rid = RID(pageId: record.recordPageId, slotId: record.slotId)
        
        // For MVP: update as delete + insert
        try ft.remove(rid)
        _ = try ft.insert(newRow, pageLSN: record.lsn)
    }
    
    private func redoHeapDelete(record: WALHeapDeleteRecord) throws {
        let rid = RID(pageId: record.recordPageId, slotId: record.slotId)
        if let ft = tablesFile[record.tableId] {
            try ft.remove(rid, pageLSN: record.lsn)
        }
        if let row = try? JSONDecoder().decode(Row.self, from: record.rowData), tablesMem[record.tableId] != nil || tablesFile[record.tableId] != nil {
            mvcc.registerDelete(table: record.tableId, rid: rid, row: row, tid: record.txId)
        }
    }
    
    private func redoIndexInsert(record: WALIndexInsertRecord) throws {
        guard let tableMap = indexes[record.tableId],
              let indexDef = tableMap[record.indexId] else { return }
        
        let rid = RID(pageId: record.ridPageId, slotId: record.ridSlotId)
        
        switch indexDef.backend {
        case .persistentBTree(let f):
            if indexDef.columns.count == 1 {
                if let value = KeyBytes.toSingleValue(record.keyBytes) {
                    try? f.insert(key: value, rid: rid)
                }
            } else {
                if let values = KeyBytes.toValues(record.keyBytes, count: indexDef.columns.count) {
                    try? f.insert(composite: values, rid: rid)
                }
            }
        default:
            // In-memory indexes rebuilt from heap
            break
        }
    }
    
    private func redoIndexDelete(record: WALIndexDeleteRecord) throws {
        guard let tableMap = indexes[record.tableId],
              let indexDef = tableMap[record.indexId] else { return }
        
        let rid = RID(pageId: record.ridPageId, slotId: record.ridSlotId)
        
        switch indexDef.backend {
        case .persistentBTree(let f):
            if indexDef.columns.count == 1 {
                if let value = KeyBytes.toSingleValue(record.keyBytes) {
                    try? f.remove(key: value, rid: rid)
                }
            } else {
                if let values = KeyBytes.toValues(record.keyBytes, count: indexDef.columns.count) {
                    try? f.remove(composite: values, rid: rid)
                }
            }
        default:
            break
        }
    }
    
    private func redoCLR(record: WALCLRRecord) throws {
        // CLR records are idempotent - they represent completed undo operations
        // Apply the undo action described in the CLR
        switch record.undoAction {
        case .heapInsert(let pageId, let slotId):
            // Undo of insert = mark tombstone
            let rid = RID(pageId: pageId, slotId: slotId)
            for (_, ft) in tablesFile {
                try? ft.remove(rid, pageLSN: record.lsn)
            }
            
        case .heapDelete(let pageId, let slotId, let rowData, let isTombstone):
            // Undo of delete = restore slot or reinstate tombstone flag
            let row = try JSONDecoder().decode(Row.self, from: rowData)
            let rid = RID(pageId: pageId, slotId: slotId)
            for (name, ft) in tablesFile {
                if isTombstone {
                    try? ft.clearTombstone(rid, pageLSN: record.lsn)
                }
                _ = try? ft.restore(rid, row: row, pageLSN: record.lsn)
            }
            if var tableEntry = tablesMem[record.tableId] {
                tableEntry.register(row: row, rid: rid, isTombstone: isTombstone)
                tablesMem[record.tableId] = tableEntry
            }
            
        case .heapUpdate(let pageId, let slotId, let originalData):
            // Undo of update = restore original
            let originalRow = try JSONDecoder().decode(Row.self, from: originalData)
            let rid = RID(pageId: pageId, slotId: slotId)
            for (_, ft) in tablesFile {
                try? ft.remove(rid)
                _ = try? ft.insert(originalRow, pageLSN: record.lsn)
            }
            
        case .indexInsert(let indexId, let keyBytes, let ridPageId, let ridSlotId):
            // Undo of index insert = delete
            let rid = RID(pageId: ridPageId, slotId: ridSlotId)
            for (_, tableMap) in indexes {
                if let indexDef = tableMap[indexId] {
                    switch indexDef.backend {
                    case .persistentBTree(let f):
                        if indexDef.columns.count == 1 {
                            if let value = KeyBytes.toSingleValue(keyBytes) {
                                try? f.remove(key: value, rid: rid)
                            }
                        }
                    case .anyString(var idx):
                        if let value = KeyBytes.toString(keyBytes) {
                            idx.remove(key: value, ref: rid)
                            tableMap[indexId] = (columns: indexDef.columns, backend: .anyString(idx))
                        }
                    default:
                        break
                    }
                }
            }
            
        case .indexDelete(let indexId, let keyBytes, let ridPageId, let ridSlotId):
            // Undo of index delete = insert
            let rid = RID(pageId: ridPageId, slotId: ridSlotId)
            for (_, tableMap) in indexes {
                if let indexDef = tableMap[indexId] {
                    switch indexDef.backend {
                    case .persistentBTree(let f):
                        if indexDef.columns.count == 1 {
                            if let value = KeyBytes.toSingleValue(keyBytes) {
                                try? f.insert(key: value, rid: rid)
                            }
                        }
                    case .anyString(var idx):
                        if let value = KeyBytes.toString(keyBytes) {
                            idx.insert(key: value, ref: rid)
                            tableMap[indexId] = (columns: indexDef.columns, backend: .anyString(idx))
                        }
                    default:
                        break
                    }
                }
            }
        }
    }
    
    // MARK: - UNDO Phase
    
    private func undoPhase(globalWAL: FileWALManager, att: [UInt64: UInt64]) throws {
        for (txId, lastLSN) in att {
            print("Rolling back transaction \(txId) from LSN \(lastLSN)")
            try undoTransaction(globalWAL: globalWAL, txId: txId, fromLSN: lastLSN)
        }
    }
    
    private func undoTransaction(globalWAL: FileWALManager, txId: UInt64, fromLSN: UInt64) throws {
        // Walk backwards through transaction's operations and undo them
        _ = fromLSN  // Starting LSN for undo
        let records = try globalWAL.iterate(from: 1)
        
        // Collect all records for this transaction
        var txRecords: [WALRecord] = []
        for record in records {
            switch record {
            case let heapRecord as WALHeapInsertRecord where heapRecord.txId == txId:
                txRecords.append(heapRecord)
            case let heapRecord as WALHeapUpdateRecord where heapRecord.txId == txId:
                txRecords.append(heapRecord)
            case let heapRecord as WALHeapDeleteRecord where heapRecord.txId == txId:
                txRecords.append(heapRecord)
            case let indexRecord as WALIndexInsertRecord where indexRecord.txId == txId:
                txRecords.append(indexRecord)
            case let indexRecord as WALIndexDeleteRecord where indexRecord.txId == txId:
                txRecords.append(indexRecord)
            default:
                continue
            }
        }
        
        // Undo in reverse order
        for record in txRecords.reversed() {
            try undoOperation(record: record)
        }
    }
    
    private func undoOperation(record: WALRecord) throws {
        switch record {
        case let heapRecord as WALHeapInsertRecord:
            // Undo insert = delete
            let rid = RID(pageId: heapRecord.recordPageId, slotId: heapRecord.slotId)
            if let ft = tablesFile[heapRecord.tableId] {
                try? ft.remove(rid)
            }
            
        case let heapRecord as WALHeapDeleteRecord:
            // Undo delete = insert
            let row = try JSONDecoder().decode(Row.self, from: heapRecord.rowData)
            if let ft = tablesFile[heapRecord.tableId] {
                _ = try? ft.insert(row)
            }
            
        case let heapRecord as WALHeapUpdateRecord:
            // Undo update = restore original
            let originalRow = try JSONDecoder().decode(Row.self, from: heapRecord.oldRowData)
            let rid = RID(pageId: heapRecord.recordPageId, slotId: heapRecord.slotId)
            if let ft = tablesFile[heapRecord.tableId] {
                try? ft.remove(rid)
                _ = try? ft.insert(originalRow)
            }
            
        case let indexRecord as WALIndexInsertRecord:
            // Undo index insert = delete
            let rid = RID(pageId: indexRecord.ridPageId, slotId: indexRecord.ridSlotId)
            if let tableMap = indexes[indexRecord.tableId],
               let indexDef = tableMap[indexRecord.indexId] {
                switch indexDef.backend {
                case .persistentBTree(let f):
                    if indexDef.columns.count == 1 {
                        if let value = KeyBytes.toSingleValue(indexRecord.keyBytes) {
                            try? f.remove(key: value, rid: rid)
                        }
                    }
                default:
                    break
                }
            }
            
        case let indexRecord as WALIndexDeleteRecord:
            // Undo index delete = insert
            let rid = RID(pageId: indexRecord.ridPageId, slotId: indexRecord.ridSlotId)
            if let tableMap = indexes[indexRecord.tableId],
               let indexDef = tableMap[indexRecord.indexId] {
                switch indexDef.backend {
                case .persistentBTree(let f):
                    if indexDef.columns.count == 1 {
                        if let value = KeyBytes.toSingleValue(indexRecord.keyBytes) {
                            try? f.insert(key: value, rid: rid)
                        }
                    }
                default:
                    break
                }
            }
            
        default:
            break
        }
    }
}
