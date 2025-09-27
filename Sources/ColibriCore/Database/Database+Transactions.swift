//
//  Database+Transactions.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Transaction bureau orchestrating begin, commit, and rollback flows.

import Foundation
// MARK: - Transactions

extension Database {
    // MARK: - Transactions (MVP)
    /// Begins a new transaction and returns its transaction ID (TID).
    /// - Returns: Newly allocated transaction identifier.
    /// - Throws: Never in the current MVP; reserved for future errors.
    public func begin(isolation: IsolationLevel? = nil) throws -> UInt64 {
        let tid = nextTID; nextTID &+= 1
        activeTIDs.insert(tid)
        mvcc.begin(tid: tid)
        let level = isolation ?? config.defaultIsolationLevel
        let lsn = logTransactionBegin(tid: tid, isolationLevel: level)
        txLastLSN[tid] = lsn
        let cutoff = level.usesStableSnapshot ? tid : UInt64.max
        let clockTS = serialClock.next()
        txContexts[tid] = TransactionContext(isolation: level, snapshotCutoff: cutoff, clockTimestamp: clockTS)
        return tid
    }

    /// Convenience overload using the configured default isolation level.
    public func begin() throws -> UInt64 { try begin(isolation: nil) }

    /// Commits a transaction, finalizing its effects.
    /// - Parameter tid: Transaction ID to commit.
    /// - Throws: Never in the current MVP; reserved for future errors.
    public func commit(_ tid: UInt64) throws {
        guard activeTIDs.contains(tid) else { return }
        let lsn = logTransactionCommit(tid: tid)
        txLastLSN[tid] = lsn
        activeTIDs.remove(tid)
        txStates.removeValue(forKey: tid)
        mvcc.commit(tid: tid)
        lockManager.unlockAll(for: tid)
        lastCommittedClockTimestamp = serialClock.next()
        txContexts.removeValue(forKey: tid)
        preparedTransactions.remove(tid)
    }

    /// Rolls back a transaction, undoing its recorded operations.
    /// - Parameter tid: Transaction ID to roll back.
    /// - Throws: Never in the current MVP; reserved for future errors.
    public func rollback(_ tid: UInt64) throws {
        guard activeTIDs.contains(tid) else { return }
        // Undo in reverse order
        let ops = (txStates[tid]?.ops ?? []).reversed()
        for op in ops { undo(op: op, tid: tid) }
        let lsn = logTransactionAbort(tid: tid)
        txLastLSN[tid] = lsn
        activeTIDs.remove(tid)
        txStates.removeValue(forKey: tid)
        mvcc.rollback(tid: tid)
        lockManager.unlockAll(for: tid)
        txContexts.removeValue(forKey: tid)
        preparedTransactions.remove(tid)
    }

    /// Creates a named savepoint within the given transaction.
    public func savepoint(_ name: String, tid: UInt64) throws {
        guard activeTIDs.contains(tid) else { throw DBError.invalidArgument("Transaction \(tid) not active") }
        var state = txStates[tid] ?? TxState()
        state.savepoints[name] = state.ops.count
        txStates[tid] = state
    }

    /// Rolls back a transaction to a previously defined savepoint (partial rollback).
    public func rollback(toSavepoint name: String, tid: UInt64) throws {
        guard activeTIDs.contains(tid) else { throw DBError.invalidArgument("Transaction \(tid) not active") }
        guard var state = txStates[tid] else { return }
        guard let target = state.savepoints[name] else { throw DBError.notFound("Savepoint \(name) not found for TID \(tid)") }
        let total = state.ops.count
        guard target < total else { return }
        let tail = Array(state.ops[target..<total])
        for op in tail.reversed() { undo(op: op, tid: tid) }
        state.ops.removeLast(total - target)
        state.savepoints = state.savepoints.filter { $0.value <= target }
        txStates[tid] = state
    }

    /// Prepares a transaction for two-phase commit by forcing WAL and data buffers to disk.
    public func prepareTransaction(_ tid: UInt64) throws {
        guard activeTIDs.contains(tid) else { throw DBError.notFound("Transaction \(tid) not active") }
        if globalWAL != nil {
            let targetLSN = txLastLSN[tid] ?? lastDBLSN
            try flushWAL(upTo: targetLSN)
        }
        flushAll()
        preparedTransactions.insert(tid)
    }

    /// Commits a previously prepared transaction (used during the commit phase of 2PC).
    public func commitPrepared(_ tid: UInt64) throws {
        guard preparedTransactions.contains(tid) else { throw DBError.invalidArgument("Transaction \(tid) not prepared") }
        try commit(tid)
    }

    /// Aborts a previously prepared transaction (used when 2PC voting fails).
    public func abortPrepared(_ tid: UInt64) throws {
        guard preparedTransactions.contains(tid) else { throw DBError.invalidArgument("Transaction \(tid) not prepared") }
        try rollback(tid)
    }

    /// Wraps the current database transaction as a TwoPhaseCommitParticipant.
    public func make2PCParticipant(tid: UInt64) -> TwoPhaseCommitParticipant {
        TwoPhaseCommitParticipant(
            id: "db:\(tid)",
            prepare: { [weak self] in
                guard let self = self else { return false }
                try self.prepareTransaction(tid)
                return true
            },
            commit: { [weak self] in
                guard let self = self else { return }
                try self.commitPrepared(tid)
            },
            abort: { [weak self] in
                guard let self = self else { return }
                try self.abortPrepared(tid)
            }
        )
    }

    func undo(op: TxOp, tid: UInt64) {
        switch op.kind {
        case .insert:
            let clr = logCLRUndoInsert(tid: tid, table: op.table, rid: op.rid, nextUndoLSN: txLastLSN[tid] ?? 0)
            if clr > 0 { txLastLSN[tid] = clr }
            if var t = tablesMem[op.table] {
                try? t.remove(op.rid); tablesMem[op.table] = t
            } else if let ft = tablesFile[op.table] {
                try? ft.remove(op.rid)
            }
            removeFromIndexes(table: op.table, row: op.row, rid: op.rid)
            mvcc.undoInsert(table: op.table, rid: op.rid, tid: tid)
        case .delete:
            let clr = logCLRUndoDelete(tid: tid, table: op.table, rid: op.rid, row: op.row, nextUndoLSN: txLastLSN[tid] ?? 0)
            if clr > 0 { txLastLSN[tid] = clr }
            if var t = tablesMem[op.table] {
                t.restore(op.rid, row: op.row)
                tablesMem[op.table] = t
                updateIndexes(table: op.table, row: op.row, rid: op.rid)
            } else if let ft = tablesFile[op.table] {
                try? ft.restore(op.rid, row: op.row)
                updateIndexes(table: op.table, row: op.row, rid: op.rid)
            }
            mvcc.undoDelete(table: op.table, rid: op.rid, tid: tid)
        case .update:
            // For update: restore original row
            guard let originalRow = op.oldRow else {
                print("Warning: Cannot undo update operation - original row not tracked")
                return
            }
            let clr = logCLRUndoUpdate(tid: tid, table: op.table, rid: op.rid, oldRow: op.row, newRow: originalRow, nextUndoLSN: txLastLSN[tid] ?? 0)
            if clr > 0 { txLastLSN[tid] = clr }
            if var t = tablesMem[op.table] {
                try? t.update(op.rid, originalRow)
                tablesMem[op.table] = t
            } else if let ft = tablesFile[op.table] {
                try? ft.update(op.rid, originalRow)
            }
            // Note: MVCC might need update handling too, but for now we'll skip it
        }
    }
}

