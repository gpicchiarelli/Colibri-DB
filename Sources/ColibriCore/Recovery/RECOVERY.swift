/*
 * RECOVERY.swift
 * ColibrìDB - ARIES Recovery Algorithm (Core Module)
 *
 * Based on TLA+ specification: RECOVERY.tla
 *
 * Implements complete ARIES (Algorithm for Recovery and Isolation Exploiting Semantics):
 *
 * Three phases:
 * 1. Analysis: Scan WAL forward from last checkpoint, build ATT and DPT
 * 2. Redo: Replay all logged operations from oldest recLSN in DPT
 * 3. Undo: Rollback uncommitted transactions using undo records
 *
 * References:
 * [1] Mohan, C., Haderle, D., Lindsay, B., Pirahesh, H., & Schwarz, P. (1992).
 *     "ARIES: A Transaction Recovery Method Supporting Fine-Granularity Locking
 *     and Partial Rollbacks Using Write-Ahead Logging"
 *     ACM Transactions on Database Systems (TODS), 17(1), 94-162.
 *
 * Key Properties:
 * - Idempotence: Recovery can run multiple times safely
 * - Completeness: All committed transactions restored
 * - Consistency: Database in consistent state after recovery
 * - No Force: Don't need to flush pages at commit
 * - Steal: Can evict dirty pages before commit
 *
 * Author: ColibrìDB Team
 * Date: 2025-10-19
 */

import Foundation

// MARK: - Recovery Phase

// RecoveryPhase is defined in ARIESRecoveryManager.swift

// MARK: - Transaction Status

/// Status in Active Transaction Table
public enum ATTStatus: String, Codable {
    case active     // Transaction active
    case prepared   // Transaction prepared (2PC)
    case committed  // Transaction committed
    case aborted    // Transaction aborted
}

// MARK: - Active Transaction Table Entry

// ATTEntry is defined in ARIESRecoveryManager.swift

// MARK: - Undo Record

// UndoRecord is defined in ARIESRecoveryManager.swift

// MARK: - WAL Record (simplified)

/// WAL record for recovery
public struct RecoveryWALRecord: Codable {
    public let lsn: UInt64
    public let txId: String
    public let kind: String
    public let pageId: Int
    public let prevLSN: UInt64
    public let undoNextLSN: UInt64?  // For CLRs
    
    public init(lsn: UInt64, txId: String, kind: String, pageId: Int,
                prevLSN: UInt64 = 0, undoNextLSN: UInt64? = nil) {
        self.lsn = lsn
        self.txId = txId
        self.kind = kind
        self.pageId = pageId
        self.prevLSN = prevLSN
        self.undoNextLSN = undoNextLSN
    }
}

// MARK: - ARIES Recovery

// ARIESRecoveryManager is defined in ARIESRecoveryManager.swift

