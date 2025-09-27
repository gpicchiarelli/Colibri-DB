//
//  Database+WALRecovery.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrìDB — BSD 3-Clause License

// Theme: WAL recovery ward replaying and healing crash damage.

import Foundation
// MARK: - WAL Recovery

extension Database {
    private enum WALTxStatus { case inProgress, committed, aborted }

    private enum WALRedoKind {
        case autoInsert(table: String, row: Row)
        case autoDelete(table: String, rid: RID)
        case insert(table: String, row: Row, rid: RID)
        case delete(table: String, rid: RID, row: Row)
        case clrUndoInsert(table: String, rid: RID)
        case clrUndoDelete(table: String, row: Row)
    }

    private struct WALTrackedOp {
        let lsn: UInt64
        let tid: UInt64
        let kind: WALRedoKind
        let pageId: UInt64?
    }

    // MARK: - ARIES-style replay
    func replayDBWAL() throws {
        guard let w = wal else { return }
        let records = try w.readAll()
        guard !records.isEmpty else { return }

        var txStatus: [UInt64: WALTxStatus] = [:]
        var txOps: [UInt64: [WALTrackedOp]] = [:]
        var redoOps: [WALTrackedOp] = []
        var preInsert: [UInt64: [(String, Row)]] = [:]
        var dptFromLog: [UInt64: UInt64] = [:]
        var committed: Set<UInt64> = []
        var aborted: Set<UInt64> = []
        var lastLSNByTx: [UInt64: UInt64] = [:]

        let decoder = JSONDecoder()

        func decodeString(from data: Data, offset: inout Int) -> String? {
            let len = Int(VarInt.decode(data, offset: &offset))
            guard len >= 0, offset + len <= data.count else { return nil }
            let slice = data.subdata(in: offset..<(offset + len))
            offset += len
            return String(data: slice, encoding: .utf8)
        }

        func decodeRow(from data: Data, offset: inout Int) -> Row? {
            let len = Int(VarInt.decode(data, offset: &offset))
            guard len >= 0, offset + len <= data.count else { return nil }
            let slice = data.subdata(in: offset..<(offset + len))
            offset += len
            return try? decoder.decode(Row.self, from: slice)
        }

        func registerDPT(pageId: UInt64, lsn: UInt64) {
            if let rec = dptFromLog[pageId] {
                if lsn < rec { dptFromLog[pageId] = lsn }
            } else {
                dptFromLog[pageId] = lsn
            }
        }

        for rec in records {
            lastDBLSN = max(lastDBLSN, rec.lsn)
            switch rec.type {
            case .insertRow:
                var offset = 0
                guard let table = decodeString(from: rec.payload, offset: &offset),
                      let row = decodeRow(from: rec.payload, offset: &offset) else { continue }
                redoOps.append(WALTrackedOp(lsn: rec.lsn, tid: 0, kind: .autoInsert(table: table, row: row), pageId: nil))
            case .deleteRid:
                var offset = 0
                guard let table = decodeString(from: rec.payload, offset: &offset),
                      offset + 10 <= rec.payload.count else { continue }
                let pid = rec.payload.subdata(in: offset..<(offset+8)).withUnsafeBytes { $0.load(as: UInt64.self) }.bigEndian
                offset += 8
                let sid = rec.payload.subdata(in: offset..<(offset+2)).withUnsafeBytes { $0.load(as: UInt16.self) }.bigEndian
                let rid = RID(pageId: pid, slotId: sid)
                redoOps.append(WALTrackedOp(lsn: rec.lsn, tid: 0, kind: .autoDelete(table: table, rid: rid), pageId: pid))
                registerDPT(pageId: pid, lsn: rec.lsn)
            case .begin:
                var offset = 0
                let tid = VarInt.decode(rec.payload, offset: &offset)
                txStatus[tid] = .inProgress
                lastLSNByTx[tid] = rec.lsn
            case .commit:
                var offset = 0
                let tid = VarInt.decode(rec.payload, offset: &offset)
                txStatus[tid] = .committed
                committed.insert(tid)
                lastLSNByTx[tid] = rec.lsn
            case .abort:
                var offset = 0
                let tid = VarInt.decode(rec.payload, offset: &offset)
                txStatus[tid] = .aborted
                aborted.insert(tid)
                lastLSNByTx[tid] = rec.lsn
            case .insertPre:
                var offset = 0
                let tid = VarInt.decode(rec.payload, offset: &offset)
                guard let table = decodeString(from: rec.payload, offset: &offset),
                      let row = decodeRow(from: rec.payload, offset: &offset) else { continue }
                preInsert[tid, default: []].append((table, row))
                lastLSNByTx[tid] = rec.lsn
            case .insertDone:
                var offset = 0
                let tid = VarInt.decode(rec.payload, offset: &offset)
                guard let table = decodeString(from: rec.payload, offset: &offset), offset + 10 <= rec.payload.count,
                      var stack = preInsert[tid], let (t, row) = stack.popLast(), t == table else { continue }
                let pid = rec.payload.subdata(in: offset..<(offset+8)).withUnsafeBytes { $0.load(as: UInt64.self) }.bigEndian
                offset += 8
                let sid = rec.payload.subdata(in: offset..<(offset+2)).withUnsafeBytes { $0.load(as: UInt16.self) }.bigEndian
                preInsert[tid] = stack
                let rid = RID(pageId: pid, slotId: sid)
                let op = WALTrackedOp(lsn: rec.lsn, tid: tid, kind: .insert(table: table, row: row, rid: rid), pageId: pid)
                txOps[tid, default: []].append(op)
                registerDPT(pageId: pid, lsn: rec.lsn)
                lastLSNByTx[tid] = rec.lsn
            case .deleteRow:
                var offset = 0
                let tid = VarInt.decode(rec.payload, offset: &offset)
                guard let table = decodeString(from: rec.payload, offset: &offset), offset + 10 <= rec.payload.count else { continue }
                let pid = rec.payload.subdata(in: offset..<(offset+8)).withUnsafeBytes { $0.load(as: UInt64.self) }.bigEndian
                offset += 8
                let sid = rec.payload.subdata(in: offset..<(offset+2)).withUnsafeBytes { $0.load(as: UInt16.self) }.bigEndian
                offset += 2
                guard let row = decodeRow(from: rec.payload, offset: &offset) else { continue }
                let rid = RID(pageId: pid, slotId: sid)
                let op = WALTrackedOp(lsn: rec.lsn, tid: tid, kind: .delete(table: table, rid: rid, row: row), pageId: pid)
                txOps[tid, default: []].append(op)
                registerDPT(pageId: pid, lsn: rec.lsn)
                lastLSNByTx[tid] = rec.lsn
            case .clr:
                guard !rec.payload.isEmpty else { continue }
                let kindByte = rec.payload[0]
                var offset = 1
                let tid = VarInt.decode(rec.payload, offset: &offset)
                guard let table = decodeString(from: rec.payload, offset: &offset) else { continue }
                switch kindByte {
                case 1:
                    guard offset + 10 <= rec.payload.count else { continue }
                    let pid = rec.payload.subdata(in: offset..<(offset+8)).withUnsafeBytes { $0.load(as: UInt64.self) }.bigEndian
                    offset += 8
                    let sid = rec.payload.subdata(in: offset..<(offset+2)).withUnsafeBytes { $0.load(as: UInt16.self) }.bigEndian
                    offset += 2
                    txOps[tid] = txOps[tid]?.filter { op in
                        if case let .insert(_, _, rid) = op.kind { return rid != RID(pageId: pid, slotId: sid) }
                        return true
                    }
                    let clrOp = WALTrackedOp(lsn: rec.lsn, tid: tid, kind: .clrUndoInsert(table: table, rid: RID(pageId: pid, slotId: sid)), pageId: pid)
                    redoOps.append(clrOp)
                    registerDPT(pageId: pid, lsn: rec.lsn)
                    lastLSNByTx[tid] = rec.lsn
                    txStatus[tid] = txStatus[tid] ?? .inProgress
                case 2:
                    guard rec.payload.count >= offset + 8 else { continue }
                    let limit = rec.payload.count - 8
                    var localOffset = offset
                    guard let row = decodeRow(from: rec.payload.subdata(in: offset..<limit), offset: &localOffset) else { continue }
                    _ = rec.payload.subdata(in: limit..<rec.payload.count).withUnsafeBytes { $0.load(as: UInt64.self) }
                    let clrOp = WALTrackedOp(lsn: rec.lsn, tid: tid, kind: .clrUndoDelete(table: table, row: row), pageId: nil)
                    redoOps.append(clrOp)
                    if var ops = txOps[tid] {
                        if let idx = ops.lastIndex(where: {
                            if case let .delete(_, _, existingRow) = $0.kind { return existingRow == row }
                            return false
                        }) {
                            ops.remove(at: idx)
                            txOps[tid] = ops
                        }
                    }
                    lastLSNByTx[tid] = rec.lsn
                    txStatus[tid] = txStatus[tid] ?? .inProgress
                default:
                    continue
                }
            case .checkpoint:
                continue
            }
        }

        // Persist dirty page table and transaction last LSNs
        self.dpt = dptFromLog
        self.txLastLSN = lastLSNByTx

        // Phase 2: REDO
        let redoStart = dptFromLog.values.min() ?? (records.first?.lsn ?? 0)
        var aggregatedRedo = redoOps
        for tid in committed {
            if let ops = txOps[tid] { aggregatedRedo.append(contentsOf: ops) }
        }
        aggregatedRedo.sort { $0.lsn < $1.lsn }
        for op in aggregatedRedo where op.lsn >= redoStart {
            applyRedo(op)
        }

        // Phase 3: UNDO
        let losers = Set(txStatus.filter { $0.value != .committed }.map { $0.key })
        for tid in losers {
            guard let ops = txOps[tid], !ops.isEmpty else {
                mvcc.rollback(tid: tid)
                continue
            }
            let descending = ops.sorted { $0.lsn > $1.lsn }
            for op in descending {
                undoDuringRecovery(op, tid: tid)
            }
            if let abortLSN = try? w.appendAbort(tid: tid, prevLSN: txLastLSN[tid] ?? 0) {
                txLastLSN[tid] = abortLSN
            }
            mvcc.rollback(tid: tid)
        }

        activeTIDs.removeAll()
        txStates.removeAll()
        
        // Flush any pending WAL records
        try? wal?.flushPending()
    }

    private func applyRedo(_ op: WALTrackedOp) {
        switch op.kind {
        case .autoInsert(let table, let row):
            _ = try? applyInsertFromWAL(table: table, row: row, lsn: op.lsn)
        case .autoDelete(let table, let rid):
            _ = try? applyDeleteFromWAL(table: table, rid: rid, lsn: op.lsn)
        case .insert(let table, let row, let rid):
            if shouldRedo(pageId: rid.pageId, lsn: op.lsn, table: table) {
                _ = try? applyInsertFromWAL(table: table, row: row, lsn: op.lsn)
                mvcc.registerInsert(table: table, rid: rid, row: row, tid: nil)
            }
        case .delete(let table, let rid, let row):
            if shouldRedo(pageId: rid.pageId, lsn: op.lsn, table: table) {
                _ = try? applyDeleteFromWAL(table: table, rid: rid, lsn: op.lsn)
                mvcc.registerDelete(table: table, rid: rid, row: row, tid: nil)
            }
        case .clrUndoInsert(let table, let rid):
            _ = try? applyDeleteFromWAL(table: table, rid: rid, lsn: op.lsn)
        case .clrUndoDelete(let table, let row):
            _ = try? applyInsertFromWAL(table: table, row: row, lsn: op.lsn)
        }
    }

    private func shouldRedo(pageId: UInt64, lsn: UInt64, table: String) -> Bool {
        if let ft = tablesFile[table], let pageLSN = ft.getPageLSN(pageId) {
            return pageLSN < lsn
        }
        return true
    }

    private func undoDuringRecovery(_ op: WALTrackedOp, tid: UInt64) {
        switch op.kind {
        case .insert(let table, let row, let rid):
            let txOp = TxOp(kind: .insert, table: table, rid: rid, row: row)
            undo(op: txOp, tid: tid)
        case .delete(let table, let rid, let row):
            let txOp = TxOp(kind: .delete, table: table, rid: rid, row: row)
            undo(op: txOp, tid: tid)
        default:
            break
        }
    }

    // Existing helpers reused by redo/undo
    func applyInsertFromWAL(table: String, row: Row, lsn: UInt64) throws {
        if var t = tablesMem[table] {
            let rid = try t.insert(row)
            tablesMem[table] = t
            updateIndexes(table: table, row: row, rid: rid)
            mvcc.registerInsert(table: table, rid: rid, row: row, tid: nil)
            return
        }
        guard let ft = tablesFile[table] else { return }
        for (rid, r) in try ft.scan() { if r == row { mvcc.registerInsert(table: table, rid: rid, row: row, tid: nil); return } }
        let rid = try ft.insert(row, pageLSN: lsn)
        updateIndexes(table: table, row: row, rid: rid)
        mvcc.registerInsert(table: table, rid: rid, row: row, tid: nil)
    }

    func applyDeleteFromWAL(table: String, rid: RID, lsn: UInt64) throws {
        if var t = tablesMem[table] {
            if let row = try? t.read(rid) {
                try t.remove(rid)
                tablesMem[table] = t
                removeFromIndexes(table: table, row: row, rid: rid)
                mvcc.registerDelete(table: table, rid: rid, row: row, tid: nil)
            }
            return
        }
        guard let ft = tablesFile[table] else { return }
        if let pageLSN = ft.getPageLSN(rid.pageId), pageLSN >= lsn { return }
        if let row = try? ft.read(rid) {
            try ft.remove(rid, pageLSN: lsn)
            removeFromIndexes(table: table, row: row, rid: rid)
            mvcc.registerDelete(table: table, rid: rid, row: row, tid: nil)
        }
    }
}

