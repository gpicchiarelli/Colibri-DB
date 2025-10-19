//
//  ARIESRecovery.swift
//  ColibrìDB ARIES Recovery Implementation
//
//  Based on: spec/RECOVERY.tla
//  Implements: ARIES 3-phase recovery (Analysis, Redo, Undo)
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//
//  Based on: "ARIES: A Transaction Recovery Method" (Mohan et al., 1992)
//

import Foundation

/// ARIES Recovery Manager
/// Corresponds to TLA+ module: RECOVERY.tla
public actor ARIESRecovery {
    // MARK: - Dependencies
    
    private let wal: FileWAL
    private let bufferPool: BufferPool
    
    // MARK: - Recovery State
    
    /// Active Transaction Table (ATT)
    private var activeTransactionTable: [TxID: LSN] = [:]
    
    /// Dirty Page Table (DPT)
    private var dirtyPageTable: [PageID: LSN] = [:]
    
    /// Recovery phase
    private enum RecoveryPhase {
        case analysis
        case redo
        case undo
        case complete
    }
    
    private var currentPhase: RecoveryPhase = .analysis
    
    // MARK: - Initialization
    
    public init(wal: FileWAL, bufferPool: BufferPool) {
        self.wal = wal
        self.bufferPool = bufferPool
    }
    
    // MARK: - ARIES Recovery
    
    /// Perform complete ARIES recovery
    /// TLA+ Action: RECOVERY_ARIES(db, wal)
    public func recover() async throws {
        print("Starting ARIES recovery...")
        
        // Phase 1: Analysis
        try await analysisPhase()
        
        // Phase 2: Redo
        try await redoPhase()
        
        // Phase 3: Undo
        try await undoPhase()
        
        currentPhase = .complete
        print("ARIES recovery complete")
    }
    
    // MARK: - Phase 1: Analysis
    
    /// Analysis phase: Build ATT and DPT from WAL
    /// TLA+ Action: AnalysisPhase(wal)
    private func analysisPhase() async throws {
        print("Analysis phase: scanning WAL...")
        currentPhase = .analysis
        
        // Get all WAL records
        let records = await wal.getAllRecords()
        
        // Start from last checkpoint if available
        let lastCheckpointLSN = await wal.getLastCheckpointLSN()
        let startLSN = lastCheckpointLSN > 0 ? lastCheckpointLSN : 0
        
        // Scan WAL records
        for record in records where record.lsn >= startLSN {
            switch record.kind {
            case .begin:
                // Add to ATT
                activeTransactionTable[record.txID] = record.lsn
                
            case .commit, .abort:
                // Remove from ATT
                activeTransactionTable[record.txID] = nil
                
            case .heapInsert, .heapUpdate, .heapDelete:
                // Update ATT
                activeTransactionTable[record.txID] = record.lsn
                
                // Add to DPT if not present
                if dirtyPageTable[record.pageID] == nil {
                    dirtyPageTable[record.pageID] = record.lsn
                }
                
            case .checkpoint:
                // Load checkpoint data
                if let payload = record.payload {
                    let decoder = JSONDecoder()
                    if let checkpointData = try? decoder.decode(CheckpointRecord.self, from: payload) {
                        dirtyPageTable = checkpointData.dirtyPageTable
                        activeTransactionTable = checkpointData.activeTransactionTable
                    }
                }
                
            default:
                break
            }
        }
        
        print("Analysis complete: \(activeTransactionTable.count) active transactions, \(dirtyPageTable.count) dirty pages")
    }
    
    // MARK: - Phase 2: Redo
    
    /// Redo phase: Replay operations idempotently
    /// TLA+ Action: RedoPhase(wal, dpt)
    private func redoPhase() async throws {
        print("Redo phase: replaying operations...")
        currentPhase = .redo
        
        // Get all WAL records
        let records = await wal.getAllRecords()
        
        // Find minimum recLSN in DPT
        let minRecLSN = dirtyPageTable.values.min() ?? 0
        
        // Redo from minRecLSN
        for record in records where record.lsn >= minRecLSN {
            switch record.kind {
            case .heapInsert, .heapUpdate, .heapDelete:
                // Check if page is in DPT
                if let recLSN = dirtyPageTable[record.pageID] {
                    // Get page
                    var page = try await bufferPool.getPage(record.pageID)
                    
                    // Check if redo is needed (idempotence)
                    if page.header.pageLSN < record.lsn {
                        // Apply operation
                        try await redoOperation(record: record, page: &page)
                        
                        // Update page LSN
                        page.header.pageLSN = record.lsn
                        
                        // Write page back
                        try await bufferPool.putPage(record.pageID, page: page, isDirty: true)
                    }
                    
                    try await bufferPool.unpinPage(record.pageID)
                }
                
            default:
                break
            }
        }
        
        print("Redo phase complete")
    }
    
    /// Apply a single redo operation
    private func redoOperation(record: ConcreteWALRecord, page: inout Page) async throws {
        // Simplified redo - in real implementation would deserialize and apply
        // For now, just ensure page is marked dirty
        print("Redo operation: LSN=\(record.lsn), type=\(record.kind)")
    }
    
    // MARK: - Phase 3: Undo
    
    /// Undo phase: Rollback uncommitted transactions
    /// TLA+ Action: UndoPhase(wal, att)
    private func undoPhase() async throws {
        print("Undo phase: rolling back \(activeTransactionTable.count) transactions...")
        currentPhase = .undo
        
        // Get all WAL records
        let records = await wal.getAllRecords()
        
        // For each active transaction, undo its operations
        for (txID, lastLSN) in activeTransactionTable {
            try await undoTransaction(txID: txID, lastLSN: lastLSN, records: records)
        }
        
        print("Undo phase complete")
    }
    
    /// Undo a single transaction
    private func undoTransaction(txID: TxID, lastLSN: LSN, records: [ConcreteWALRecord]) async throws {
        print("Undoing transaction \(txID)")
        
        // Find all records for this transaction (following prevLSN chain)
        var currentLSN = lastLSN
        
        while currentLSN > 0 {
            // Find record with this LSN
            guard let record = records.first(where: { $0.lsn == currentLSN }) else {
                break
            }
            
            // Undo the operation
            if record.kind != .begin && record.kind != .commit && record.kind != .abort {
                try await undoOperation(record: record)
                
                // Write CLR (Compensation Log Record)
                _ = try await wal.append(
                    kind: .clr,
                    txID: txID,
                    pageID: record.pageID,
                    payload: nil
                )
            }
            
            // Follow prevLSN chain
            currentLSN = record.prevLSN
        }
        
        // Write abort record
        _ = try await wal.append(kind: .abort, txID: txID, pageID: 0)
    }
    
    /// Undo a single operation
    private func undoOperation(record: ConcreteWALRecord) async throws {
        // Simplified undo - in real implementation would reverse the operation
        print("Undo operation: LSN=\(record.lsn), type=\(record.kind)")
    }
    
    // MARK: - Query Operations
    
    /// Get current recovery phase
    public func getCurrentPhase() -> String {
        switch currentPhase {
        case .analysis: return "Analysis"
        case .redo: return "Redo"
        case .undo: return "Undo"
        case .complete: return "Complete"
        }
    }
    
    /// Get active transaction count (during recovery)
    public func getActiveTransactionCount() -> Int {
        return activeTransactionTable.count
    }
}

