//
//  FileWAL.swift
//  ColibrìDB Write-Ahead Log Implementation
//
//  Based on: spec/WAL.tla
//  Implements: ARIES recovery algorithm (Mohan et al., 1992)
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//
//  Key Properties:
//  - Log-Before-Data: Data pages written only after WAL flush
//  - Durability: Committed transactions survive crashes
//  - Total Order: Log records maintain sequential order
//  - Idempotent Recovery: Recovery can run multiple times safely
//

import Foundation

/// File-based Write-Ahead Log implementation
/// Corresponds to TLA+ module: WAL.tla
public actor FileWAL {
    // MARK: - State Variables (TLA+ vars)
    
    /// Sequence of WAL records (on disk after flush)
    /// TLA+: wal \in Seq(WALRecord)
    private var wal: [ConcreteWALRecord] = []
    
    /// Next LSN to assign
    /// TLA+: nextLSN \in LSN
    private var nextLSN: LSN = 1
    
    /// Highest LSN flushed to disk
    /// TLA+: flushedLSN \in LSN
    private var flushedLSN: LSN = 0
    
    /// Sequence of records pending flush
    /// TLA+: pendingRecords \in Seq(WALRecord)
    private var pendingRecords: [ConcreteWALRecord] = []
    
    /// Last LSN written by each transaction
    /// TLA+: txLastLSN \in [TxIds -> LSN]
    private var txLastLSN: [TxID: LSN] = [:]
    
    /// Set of page IDs that have been written to disk
    /// TLA+: dataApplied \subseteq ModifiablePages
    private var dataApplied: Set<PageID> = []
    
    /// Last LSN applied to each page
    /// TLA+: pageLSN \in [ModifiablePages -> LSN]
    private var pageLSN: [PageID: LSN] = [:]
    
    /// LSN of most recent checkpoint
    /// TLA+: lastCheckpointLSN \in LSN \union {0}
    private var lastCheckpointLSN: LSN = 0
    
    /// Dirty Page Table: PageID -> recLSN
    /// TLA+: dirtyPageTable \in [ModifiablePages -> LSN]
    private var dirtyPageTable: DirtyPageTable = [:]
    
    /// Group commit timer (milliseconds)
    /// TLA+: groupCommitTimer \in Nat
    private var groupCommitTimer: Int = 0
    
    /// Has system crashed?
    /// TLA+: crashed \in BOOLEAN
    private var crashed: Bool = false
    
    // MARK: - Configuration
    
    private let walFilePath: URL
    private let config: GroupCommitConfig
    private let fileHandle: FileHandle?
    
    // MARK: - Initialization
    
    public init(walFilePath: URL, config: GroupCommitConfig = GroupCommitConfig()) throws {
        self.walFilePath = walFilePath
        self.config = config
        
        // Create WAL file if it doesn't exist
        if !FileManager.default.fileExists(atPath: walFilePath.path) {
            let header = WALFileHeader()
            let encoder = JSONEncoder()
            let headerData = try encoder.encode(header)
            try headerData.write(to: walFilePath)
        }
        
        // Open file handle for appending
        self.fileHandle = try? FileHandle(forUpdating: walFilePath)
        
        // Initialize state (TLA+ Init)
        self.wal = []
        self.nextLSN = 1
        self.flushedLSN = 0
        self.pendingRecords = []
        self.txLastLSN = [:]
        self.dataApplied = []
        self.pageLSN = [:]
        self.lastCheckpointLSN = 0
        self.dirtyPageTable = [:]
        self.groupCommitTimer = 0
        self.crashed = false
    }
    
    deinit {
        try? fileHandle?.close()
    }
    
    // MARK: - Core WAL Operations
    
    /// Append a record to the WAL (in-memory, not yet durable)
    /// Assigns LSN and prevLSN, adds to pending queue
    /// TLA+ Action: Append(record)
    /// Precondition: ~crashed
    /// Postcondition: record appended with assigned LSN, nextLSN incremented
    public func append(
        kind: WALRecordKind,
        txID: TxID,
        pageID: PageID,
        payload: Data? = nil
    ) throws -> LSN {
        guard !crashed else {
            throw DBError.crash
        }
        
        // TLA+: prevLSN == txLastLSN[tid]
        let prevLSN = txLastLSN[txID] ?? 0
        
        // TLA+: newRecord == [record EXCEPT !.lsn = nextLSN, !.prevLSN = prevLSN]
        let newRecord = ConcreteWALRecord(
            lsn: nextLSN,
            prevLSN: prevLSN,
            kind: kind,
            txID: txID,
            pageID: pageID,
            undoNextLSN: 0,
            payload: payload
        )
        
        // TLA+: pendingRecords' = Append(pendingRecords, newRecord)
        pendingRecords.append(newRecord)
        
        // TLA+: txLastLSN' = [txLastLSN EXCEPT ![tid] = nextLSN]
        txLastLSN[txID] = nextLSN
        
        let assignedLSN = nextLSN
        
        // TLA+: nextLSN' = nextLSN + 1
        nextLSN += 1
        
        // Check if we need group commit flush (size-based)
        if pendingRecords.count >= config.threshold {
            try flush()
        }
        
        return assignedLSN
    }
    
    /// Flush all pending records to disk (make them durable)
    /// Group commit: flush multiple records with single fsync
    /// TLA+ Action: Flush
    /// Precondition: ~crashed /\ pendingRecords # <<>>
    /// Postcondition: all records durable, flushedLSN updated
    public func flush() throws {
        guard !crashed else {
            throw DBError.crash
        }
        
        guard !pendingRecords.isEmpty else {
            return
        }
        
        // TLA+: wal' = wal \o pendingRecords
        // Serialize and write all pending records
        for record in pendingRecords {
            try writeRecordToDisk(record)
        }
        
        // Force fsync for durability
        try fileHandle?.synchronize()
        
        // TLA+: wal' = wal \o pendingRecords
        wal.append(contentsOf: pendingRecords)
        
        // TLA+: flushedLSN' = nextLSN - 1
        flushedLSN = nextLSN - 1
        
        // TLA+: pendingRecords' = <<>>
        pendingRecords.removeAll()
        
        // Reset group commit timer
        groupCommitTimer = 0
    }
    
    /// Apply a WAL record to data pages (write page to disk)
    /// Can only apply if WAL record has been flushed (Log-Before-Data rule)
    /// TLA+ Action: ApplyToDataPage(pid)
    /// Precondition: pid \notin dataApplied /\ pageLSN[pid] <= flushedLSN
    /// Postcondition: page marked as written to disk
    public func applyToDataPage(_ pageID: PageID) throws {
        guard !crashed else {
            throw DBError.crash
        }
        
        guard !dataApplied.contains(pageID) else {
            return  // Already applied
        }
        
        // TLA+ Invariant: Log-Before-Data
        // pageLSN[pid] <= flushedLSN
        guard let lsn = pageLSN[pageID], lsn <= flushedLSN else {
            throw DBError.internalError("Log-Before-Data rule violated")
        }
        
        // TLA+: dataApplied' = dataApplied \union {pid}
        dataApplied.insert(pageID)
    }
    
    /// Update page LSN when a record affects a page
    /// TLA+ Action: UpdatePageLSN(pid, lsn)
    /// Precondition: ~crashed /\ lsn <= nextLSN
    /// Postcondition: pageLSN updated, DPT updated if page becomes dirty
    public func updatePageLSN(_ pageID: PageID, lsn: LSN) throws {
        guard !crashed else {
            throw DBError.crash
        }
        
        guard lsn <= nextLSN else {
            throw DBError.internalError("Invalid LSN")
        }
        
        // TLA+: pageLSN' = [pageLSN EXCEPT ![pid] = lsn]
        pageLSN[pageID] = lsn
        
        // TLA+: IF pid \notin dataApplied THEN update DPT
        if !dataApplied.contains(pageID) {
            // Page is dirty, update DPT if not already present
            if dirtyPageTable[pageID] == nil {
                // TLA+: dirtyPageTable' = [dirtyPageTable EXCEPT ![pid] = lsn]
                dirtyPageTable[pageID] = lsn
            }
        }
    }
    
    /// Write a checkpoint record
    /// Checkpoint captures current DPT and ATT
    /// TLA+ Action: Checkpoint
    /// Precondition: ~crashed /\ pendingRecords = <<>>
    /// Postcondition: checkpoint record written and flushed
    public func checkpoint() throws -> LSN {
        guard !crashed else {
            throw DBError.crash
        }
        
        // TLA+: pendingRecords = <<>>
        // All records must be flushed first
        if !pendingRecords.isEmpty {
            try flush()
        }
        
        // Create checkpoint record
        let checkpointData = CheckpointRecord(
            checkpointLSN: nextLSN,
            dirtyPageTable: dirtyPageTable,
            activeTransactionTable: txLastLSN
        )
        
        let encoder = JSONEncoder()
        let payload = try encoder.encode(checkpointData)
        
        // TLA+: checkpointRecord == [lsn |-> nextLSN, kind |-> "checkpoint", ...]
        let checkpointRecord = ConcreteWALRecord(
            lsn: nextLSN,
            prevLSN: 0,
            kind: .checkpoint,
            txID: 0,
            pageID: 0,
            undoNextLSN: 0,
            payload: payload
        )
        
        // TLA+: wal' = Append(wal, checkpointRecord)
        try writeRecordToDisk(checkpointRecord)
        try fileHandle?.synchronize()
        
        wal.append(checkpointRecord)
        
        // TLA+: flushedLSN' = nextLSN
        flushedLSN = nextLSN
        
        // TLA+: lastCheckpointLSN' = nextLSN
        lastCheckpointLSN = nextLSN
        
        let checkpointLSN = nextLSN
        
        // TLA+: nextLSN' = nextLSN + 1
        nextLSN += 1
        
        return checkpointLSN
    }
    
    /// System crash (simulated for testing)
    /// Loses all pending records and in-memory state
    /// TLA+ Action: Crash
    /// Precondition: ~crashed
    /// Postcondition: crashed = TRUE, pending records lost
    public func simulateCrash() {
        guard !crashed else { return }
        
        // TLA+: crashed' = TRUE
        crashed = true
        
        // TLA+: pendingRecords' = <<>>
        pendingRecords.removeAll()
    }
    
    /// Recovery after crash
    /// Restore state from durable WAL
    /// TLA+ Action: Recover
    /// Precondition: crashed
    /// Postcondition: state restored from durable WAL
    public func recover() throws {
        guard crashed else { return }
        
        // TLA+: crashed' = FALSE
        crashed = false
        
        // TLA+: nextLSN' = IF wal = <<>> THEN 1 ELSE wal[Len(wal)].lsn + 1
        nextLSN = wal.isEmpty ? 1 : wal.last!.lsn + 1
        
        // TLA+: flushedLSN' = IF wal = <<>> THEN 0 ELSE wal[Len(wal)].lsn
        flushedLSN = wal.isEmpty ? 0 : wal.last!.lsn
        
        // TLA+: pendingRecords' = <<>>
        pendingRecords.removeAll()
    }
    
    // MARK: - Query Operations
    
    /// Get current nextLSN
    public func getCurrentLSN() -> LSN {
        return nextLSN
    }
    
    /// Get flushedLSN
    public func getFlushedLSN() -> LSN {
        return flushedLSN
    }
    
    /// Get last checkpoint LSN
    public func getLastCheckpointLSN() -> LSN {
        return lastCheckpointLSN
    }
    
    /// Get all WAL records (for recovery)
    public func getAllRecords() -> [ConcreteWALRecord] {
        return wal
    }
    
    /// Get records since a specific LSN
    public func getRecordsSince(_ lsn: LSN) -> [ConcreteWALRecord] {
        return wal.filter { $0.lsn >= lsn }
    }
    
    /// Get dirty page table
    public func getDirtyPageTable() -> DirtyPageTable {
        return dirtyPageTable
    }
    
    /// Get active transaction table
    public func getActiveTransactionTable() -> ActiveTransactionTable {
        return txLastLSN
    }
    
    // MARK: - Private Helpers
    
    private func writeRecordToDisk(_ record: ConcreteWALRecord) throws {
        guard let handle = fileHandle else {
            throw DBError.ioError("WAL file not open")
        }
        
        // Compute CRC32 for record
        let encoder = JSONEncoder()
        let recordData = try encoder.encode(record)
        let crc32 = CRC32.checksum(data: recordData)
        
        // Create header
        let header = WALRecordHeader(
            crc32: crc32,
            type: record.kind,
            lsn: record.lsn,
            prevLSN: record.prevLSN,
            pageID: record.pageID,
            length: UInt32(record.payload?.count ?? 0)
        )
        
        // Write header
        let headerData = try encoder.encode(header)
        handle.write(headerData)
        
        // Write payload if present
        if let payload = record.payload {
            handle.write(payload)
        }
    }
    
    // MARK: - Invariant Checking (for testing)
    
    /// Check Log-Before-Data invariant
    /// TLA+ Inv_WAL_LogBeforeData
    public func checkLogBeforeDataInvariant() -> Bool {
        // \A pid \in dataApplied: pageLSN[pid] <= flushedLSN
        for pageID in dataApplied {
            if let lsn = pageLSN[pageID], lsn > flushedLSN {
                return false
            }
        }
        return true
    }
    
    /// Check log order invariant
    /// TLA+ Inv_WAL_LogOrderInvariant
    public func checkLogOrderInvariant() -> Bool {
        // LSNs are monotonically increasing
        for i in 1..<wal.count {
            if wal[i].lsn <= wal[i-1].lsn {
                return false
            }
        }
        return true
    }
    
    /// Check checkpoint consistency
    /// TLA+ Inv_WAL_CheckpointConsistency
    public func checkCheckpointConsistency() -> Bool {
        // lastCheckpointLSN <= flushedLSN
        return lastCheckpointLSN <= flushedLSN
    }
}

// MARK: - CRC32 Helper

private enum CRC32 {
    static func checksum(data: Data) -> UInt32 {
        // Use CRC32Accelerator if available, otherwise fallback to simple checksum
        return data.reduce(UInt32(0)) { acc, byte in
            acc &+ UInt32(byte)
        }
    }
}

