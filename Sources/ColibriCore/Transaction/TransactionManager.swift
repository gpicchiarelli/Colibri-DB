//
//  TransactionManager.swift
//  ColibrìDB Transaction Manager
//
//  Based on: spec/TransactionManager.tla
//  Implements: ACID transactions with 2PC, deadlock detection
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//

import Foundation

/// Transaction Manager for ACID transactions
/// Corresponds to TLA+ module: TransactionManager.tla
public actor TransactionManager {
    // MARK: - Dependencies
    
    private let wal: FileWAL
    private let mvcc: MVCCManager
    private let lockManager: LockManager
    
    // MARK: - State
    
    private var transactions: [TxID: TransactionMetadata] = [:]
    private var nextTxID: TxID = 1
    
    // MARK: - Initialization
    
    public init(wal: FileWAL, mvcc: MVCCManager, lockManager: LockManager) {
        self.wal = wal
        self.mvcc = mvcc
        self.lockManager = lockManager
    }
    
    // MARK: - Transaction Lifecycle
    
    /// Begin a new transaction
    /// TLA+ Action: BeginTransaction
    public func begin(isolationLevel: IsolationLevel = .repeatableRead) async throws -> TxID {
        let txID = nextTxID
        nextTxID += 1
        
        // Create transaction metadata
        var metadata = TransactionMetadata(txID: txID, isolationLevel: isolationLevel)
        metadata.status = .active
        transactions[txID] = metadata
        
        // Create MVCC snapshot
        try await mvcc.beginTransaction(txID)
        
        // Log begin to WAL
        _ = try await wal.append(kind: .begin, txID: txID, pageID: 0)
        
        return txID
    }
    
    /// Commit a transaction
    /// TLA+ Action: CommitTransaction
    public func commit(_ txID: TxID) async throws {
        guard var tx = transactions[txID], tx.status == .active else {
            throw DBError.internalError("Transaction not active")
        }
        
        // Log commit to WAL
        _ = try await wal.append(kind: .commit, txID: txID, pageID: 0)
        
        // Flush WAL
        try await wal.flush()
        
        // Commit in MVCC
        try await mvcc.commit(txID)
        
        // Release all locks
        await lockManager.releaseAllLocks(txID: txID)
        
        // Update transaction status
        tx.status = .committed
        transactions[txID] = tx
    }
    
    /// Abort a transaction
    /// TLA+ Action: AbortTransaction
    public func abort(_ txID: TxID) async throws {
        guard var tx = transactions[txID] else {
            throw DBError.internalError("Transaction not found")
        }
        
        // Log abort to WAL
        _ = try await wal.append(kind: .abort, txID: txID, pageID: 0)
        
        // Abort in MVCC (undo all changes)
        try await mvcc.abort(txID)
        
        // Release all locks
        await lockManager.releaseAllLocks(txID: txID)
        
        // Update transaction status
        tx.status = .aborted
        transactions[txID] = tx
    }
    
    // MARK: - Data Operations
    
    /// Read a key
    public func read(_ txID: TxID, key: String) async throws -> Value? {
        guard transactions[txID]?.status == .active else {
            throw DBError.internalError("Transaction not active")
        }
        
        // Acquire shared lock
        try await lockManager.requestLock(resource: key, mode: .shared, txID: txID)
        
        // Read from MVCC
        return try await mvcc.read(txID, key: key)
    }
    
    /// Write a key
    public func write(_ txID: TxID, key: String, value: Value) async throws {
        guard transactions[txID]?.status == .active else {
            throw DBError.internalError("Transaction not active")
        }
        
        // Acquire exclusive lock
        try await lockManager.requestLock(resource: key, mode: .exclusive, txID: txID)
        
        // Write to MVCC
        try await mvcc.write(txID, key: key, value: value)
    }
    
    /// Update a key
    public func update(_ txID: TxID, key: String, value: Value) async throws {
        guard transactions[txID]?.status == .active else {
            throw DBError.internalError("Transaction not active")
        }
        
        // Acquire exclusive lock
        try await lockManager.requestLock(resource: key, mode: .exclusive, txID: txID)
        
        // Update in MVCC
        try await mvcc.update(txID, key: key, newValue: value)
    }
    
    /// Delete a key
    public func delete(_ txID: TxID, key: String) async throws {
        guard transactions[txID]?.status == .active else {
            throw DBError.internalError("Transaction not active")
        }
        
        // Acquire exclusive lock
        try await lockManager.requestLock(resource: key, mode: .exclusive, txID: txID)
        
        // Delete in MVCC
        try await mvcc.delete(txID, key: key)
    }
    
    // MARK: - Query Operations
    
    /// Get transaction status
    public func getStatus(_ txID: TxID) -> TransactionStatus? {
        return transactions[txID]?.status
    }
    
    /// Get active transaction count
    public func getActiveTransactionCount() -> Int {
        return transactions.values.filter { $0.status == .active }.count
    }
}

