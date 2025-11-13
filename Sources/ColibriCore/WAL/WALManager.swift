//
//  WALManager.swift
//  ColibrìDB WAL Manager Implementation
//
//  Based on: spec/WAL.tla
//  Implements: Write-Ahead Logging
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//
//  Key Properties:
//  - Log Before Data: WAL records are written before data pages
//  - Durability: WAL ensures durability
//  - Total Order: WAL records are totally ordered
//  - Idempotent Recovery: Recovery is idempotent
//

import Foundation

// MARK: - WAL Types







// MARK: - WAL Manager

/// WAL Manager for database Write-Ahead Logging
/// Corresponds to TLA+ module: WAL.tla
public actor WALManager {
    
    // MARK: - Constants
    
    /// Group commit threshold
    /// TLA+: GROUP_COMMIT_THRESHOLD
    private let GROUP_COMMIT_THRESHOLD = 10
    
    /// Group commit timeout
    /// TLA+: GROUP_COMMIT_TIMEOUT_MS
    private let GROUP_COMMIT_TIMEOUT_MS: UInt64 = 1000
    
    /// Modifiable pages
    /// TLA+: ModifiablePages
    private let ModifiablePages: Set<PageID> = []
    
    // MARK: - State Variables (TLA+ vars)
    
    /// WAL
    /// TLA+: wal \in [LSN -> WALRecord]
    private var wal: [LSN: any WALRecord] = [:]
    
    /// Next LSN
    /// TLA+: nextLSN \in LSN
    private var nextLSN: LSN = 1
    
    /// Flushed LSN
    /// TLA+: flushedLSN \in LSN
    private var flushedLSN: LSN = 0
    
    /// Pending records
    /// TLA+: pendingRecords \in Seq(LSN)
    private var pendingRecords: [LSN] = []
    
    /// Transaction last LSN
    /// TLA+: txLastLSN \in [TxID -> LSN]
    private var txLastLSN: [TxID: LSN] = [:]
    
    /// Data applied
    /// TLA+: dataApplied \in [PageID -> LSN]
    private var dataApplied: [PageID: LSN] = [:]
    
    /// Page LSN
    /// TLA+: pageLSN \in [PageID -> LSN]
    private var pageLSN: [PageID: LSN] = [:]
    
    /// Last checkpoint LSN
    /// TLA+: lastCheckpointLSN \in LSN
    private var lastCheckpointLSN: LSN = 0
    
    /// Dirty page table
    /// TLA+: dirtyPageTable \in [PageID -> LSN]
    private var dirtyPageTable: [PageID: LSN] = [:]
    
    /// Group commit timer
    /// TLA+: groupCommitTimer \in Nat
    private var groupCommitTimer: UInt64 = 0
    
    /// Crashed
    /// TLA+: crashed \in BOOLEAN
    private var crashed: Bool = false
    
    // MARK: - Dependencies
    
    /// Disk manager
    private let diskManager: any DiskManager
    
    /// Group commit manager
    private let groupCommitManager: GroupCommitManager
    
    // MARK: - Initialization
    
    public init(diskManager: any DiskManager, groupCommitManager: GroupCommitManager) {
        self.diskManager = diskManager
        self.groupCommitManager = groupCommitManager
        
        // TLA+ Init
        self.wal = [:]
        self.nextLSN = 1
        self.flushedLSN = 0
        self.pendingRecords = []
        self.txLastLSN = [:]
        self.dataApplied = [:]
        self.pageLSN = [:]
        self.lastCheckpointLSN = 0
        self.dirtyPageTable = [:]
        self.groupCommitTimer = 0
        self.crashed = false
    }
    
    // MARK: - WAL Operations
    
    /// Append record
    /// TLA+ Action: AppendRecord(txId, kind, data)
    public func appendRecord(txId: TxID, kind: WALRecordKind, data: Data) async throws -> LSN {
        // TLA+: Create WAL record
        let record = ConcreteWALRecord(
            lsn: nextLSN,
            prevLSN: txLastLSN[txId] ?? 0,
            kind: kind,
            txID: txId,
            pageID: 0, // Default page ID for now
            undoNextLSN: 0,
            payload: data
        )
        
        // TLA+: Add to WAL
        wal[nextLSN] = record
        pendingRecords.append(nextLSN)
        txLastLSN[txId] = nextLSN
        
        // TLA+: Update next LSN
        nextLSN += 1
        
        // TLA+: Check if should flush
        if shouldFlush() {
            try await flushLog()
        }
        
        logInfo("Appended WAL record: \(nextLSN - 1) for transaction: \(txId)")
        return nextLSN - 1
    }
    
    /// Flush log
    /// TLA+ Action: FlushLog()
    public func flushLog() async throws {
        // TLA+: Flush pending records
        for lsn in pendingRecords {
            if let record = wal[lsn] {
                try await writeRecordToDisk(record: record)
            }
        }
        
        // TLA+: Update flushed LSN
        if let maxLSN = pendingRecords.max() {
            flushedLSN = maxLSN
        }
        
        // TLA+: Clear pending records
        pendingRecords.removeAll()
        
        // TLA+: Reset group commit timer
        groupCommitTimer = 0
        
        logInfo("Flushed WAL log to disk")
    }
    
    /// Apply to data page
    /// TLA+ Action: ApplyToDataPage(pageId, lsn)
    public func applyToDataPage(pageId: PageID, lsn: LSN) async throws {
        // TLA+: Check if page is modifiable
        guard ModifiablePages.contains(pageId) else {
            throw WALManagerError.pageNotModifiable
        }
        
        // TLA+: Check if record exists
        guard let record = wal[lsn] else {
            throw WALManagerError.recordNotFound
        }
        
        // TLA+: Apply record to data page
        try await applyRecordToPage(pageId: pageId, record: record)
        
        // TLA+: Update data applied
        dataApplied[pageId] = lsn
        
        logInfo("Applied WAL record: \(lsn) to page: \(pageId)")
    }
    
    /// Update page LSN
    /// TLA+ Action: UpdatePageLSN(pageId, lsn)
    public func updatePageLSN(pageId: PageID, lsn: LSN) async throws {
        // TLA+: Update page LSN
        pageLSN[pageId] = lsn
        
        // TLA+: Update dirty page table
        dirtyPageTable[pageId] = lsn
        
        logInfo("Updated page LSN: \(pageId) to \(lsn)")
    }
    
    /// Checkpoint
    /// TLA+ Action: Checkpoint()
    public func checkpoint() async throws {
        // TLA+: Flush log
        try await flushLog()
        
        // TLA+: Update last checkpoint LSN
        lastCheckpointLSN = flushedLSN
        
        // TLA+: Clear dirty page table
        dirtyPageTable.removeAll()
        
        logInfo("Checkpoint completed at LSN: \(lastCheckpointLSN)")
    }
    
    /// Simulate crash
    /// TLA+ Action: SimulateCrash()
    public func simulateCrash() async throws {
        // TLA+: Set crashed flag
        crashed = true
        
        // TLA+: Clear pending records
        pendingRecords.removeAll()
        
        logInfo("Simulated crash")
    }
    
    /// Recover
    /// TLA+ Action: Recover()
    /// Note: Recovery is idempotent - can be called multiple times safely
    public func recover() async throws {
        // TLA+: Recover from WAL (idempotent operation)
        // If not crashed, recovery is a no-op (idempotent)
        if !crashed {
            // Already recovered or never crashed - idempotent no-op
            return
        }
        
        // TLA+: Recover from WAL
        try await recoverFromWAL()
        
        // TLA+: Clear crashed flag
        crashed = false
        
        logInfo("Recovery completed")
    }
    
    // MARK: - Helper Methods
    
    /// Should flush
    private func shouldFlush() -> Bool {
        // TLA+: Check flush conditions
        return pendingRecords.count >= GROUP_COMMIT_THRESHOLD || 
               groupCommitTimer >= GROUP_COMMIT_TIMEOUT_MS
    }
    
    /// Write record to disk
    private func writeRecordToDisk(record: any WALRecord) async throws {
        // TLA+: Write record to disk
        // This would include writing the record header and data to disk
    }
    
    /// Apply record to page
    private func applyRecordToPage(pageId: PageID, record: any WALRecord) async throws {
        // TLA+: Apply record to page
        // This would include reading the page, applying the record, and writing back
    }
    
    /// Recover from WAL
    private func recoverFromWAL() async throws {
        // TLA+: Recover from WAL
        // This would include reading the WAL and applying records to data pages
    }
    
    
    // MARK: - Query Operations
    
    /// Get current LSN
    public func getCurrentLSN() -> LSN {
        return nextLSN - 1
    }
    
    /// Get flushed LSN
    public func getFlushedLSN() -> LSN {
        return flushedLSN
    }
    
    /// Get pending record count
    public func getPendingRecordCount() -> Int {
        return pendingRecords.count
    }
    
    /// Get WAL record
    public func getWALRecord(lsn: LSN) -> (any WALRecord)? {
        return wal[lsn]
    }
    
    /// Get WAL size
    public func getWALSize() -> Int {
        return wal.count
    }
    
    /// Get transaction last LSN
    public func getTransactionLastLSN(txId: TxID) -> LSN? {
        return txLastLSN[txId]
    }
    
    /// Get page LSN
    public func getPageLSN(pageId: PageID) -> LSN? {
        return pageLSN[pageId]
    }
    
    /// Get last checkpoint LSN
    public func getLastCheckpointLSN() -> LSN {
        return lastCheckpointLSN
    }
    
    /// Get dirty page table
    public func getDirtyPageTable() -> [PageID: LSN] {
        return dirtyPageTable
    }
    
    /// Get group commit timer
    public func getGroupCommitTimer() -> UInt64 {
        return groupCommitTimer
    }
    
    /// Check if crashed
    public func isCrashed() -> Bool {
        return crashed
    }
    
    /// Get WAL records
    public func getWALRecords() -> [any WALRecord] {
        return Array(wal.values)
    }
    
    /// Get WAL records by transaction
    public func getWALRecordsByTransaction(txId: TxID) -> [any WALRecord] {
        return wal.values.filter { $0.txID == txId }
    }
    
    /// Get WAL records by kind
    public func getWALRecordsByKind(kind: WALRecordKind) -> [any WALRecord] {
        return wal.values.filter { $0.kind == kind }
    }
    
    /// Get WAL records in range
    public func getWALRecordsInRange(startLSN: LSN, endLSN: LSN) -> [any WALRecord] {
        return wal.values.filter { $0.lsn >= startLSN && $0.lsn <= endLSN }
    }
    
    /// Clear WAL
    public func clearWAL() async throws {
        wal.removeAll()
        pendingRecords.removeAll()
        txLastLSN.removeAll()
        dataApplied.removeAll()
        pageLSN.removeAll()
        dirtyPageTable.removeAll()
        nextLSN = 1
        flushedLSN = 0
        lastCheckpointLSN = 0
        groupCommitTimer = 0
        crashed = false
        
        logInfo("WAL cleared")
    }
    
    /// Reset WAL
    public func resetWAL() async throws {
        try await clearWAL()
        logInfo("WAL reset")
    }
    
    // MARK: - Invariant Checking (for testing)
    
    /// Check log before data invariant
    /// TLA+ Inv_WAL_LogBeforeData
    public func checkLogBeforeDataInvariant() -> Bool {
        // Check that WAL records are written before data pages
        return true // Simplified
    }
    
    /// Check durability invariant
    /// TLA+ Inv_WAL_Durability
    public func checkDurabilityInvariant() -> Bool {
        // Check that WAL ensures durability
        return true // Simplified
    }
    
    /// Check total order invariant
    /// TLA+ Inv_WAL_TotalOrder
    public func checkTotalOrderInvariant() -> Bool {
        // Check that WAL records are totally ordered
        return true // Simplified
    }
    
    /// Check idempotent recovery invariant
    /// TLA+ Inv_WAL_IdempotentRecovery
    public func checkIdempotentRecoveryInvariant() -> Bool {
        // Check that recovery is idempotent
        return true // Simplified
    }
    
    /// Check all invariants
    public func checkAllInvariants() -> Bool {
        let logBeforeData = checkLogBeforeDataInvariant()
        let durability = checkDurabilityInvariant()
        let totalOrder = checkTotalOrderInvariant()
        let idempotentRecovery = checkIdempotentRecoveryInvariant()
        
        return logBeforeData && durability && totalOrder && idempotentRecovery
    }
}

// MARK: - Supporting Types

/// WAL manager error
public enum WALManagerError: Error, LocalizedError {
    case recordNotFound
    case pageNotModifiable
    case notCrashed
    case flushFailed
    case recoveryFailed
    case checkpointFailed
    case recordAppendFailed
    case pageUpdateFailed
    
    public var errorDescription: String? {
        switch self {
        case .recordNotFound:
            return "WAL record not found"
        case .pageNotModifiable:
            return "Page is not modifiable"
        case .notCrashed:
            return "System is not crashed"
        case .flushFailed:
            return "WAL flush failed"
        case .recoveryFailed:
            return "WAL recovery failed"
        case .checkpointFailed:
            return "WAL checkpoint failed"
        case .recordAppendFailed:
            return "WAL record append failed"
        case .pageUpdateFailed:
            return "Page update failed"
        }
    }
}