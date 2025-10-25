//
//  TransactionMVCCAdapter.swift
//  ColibrìDB Transaction MVCC Adapter
//
//  Adapter to make MVCCManager compatible with TransactionMVCCManager protocol
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//

import Foundation

/// Adapter that makes MVCCManager compatible with TransactionMVCCManager protocol
public actor TransactionMVCCAdapter: TransactionMVCCManager {
    
    private let mvccManager: MVCCManager
    
    public init(mvccManager: MVCCManager) {
        self.mvccManager = mvccManager
    }
    
    /// Begin a transaction and return a snapshot
    public func beginTransaction(txId: TxID) async throws -> Snapshot {
        let mvccSnapshot = try await mvccManager.beginTransaction(txId: txId)
        
        // Convert MVCCSnapshot to Snapshot
        return Snapshot(
            txID: mvccSnapshot.txId,
            startTS: mvccSnapshot.timestamp,
            xmin: mvccSnapshot.timestamp,
            xmax: mvccSnapshot.timestamp + 1,
            activeTxAtStart: mvccSnapshot.activeTransactions
        )
    }
    
    /// Read a value for a key
    public func read(txId: TxID, key: String) async throws -> String? {
        let value = try await mvccManager.read(txId: txId, key: .string(key))
        if case .string(let str) = value {
            return str
        }
        return nil
    }
    
    /// Write a value for a key
    public func write(txId: TxID, key: String, value: String) async throws {
        try await mvccManager.write(txId: txId, key: .string(key), value: .string(value))
    }
    
    /// Commit a transaction
    public func commit(txId: TxID) async throws {
        try await mvccManager.commit(txId: txId)
    }
    
    /// Abort a transaction
    public func abort(txId: TxID) async throws {
        try await mvccManager.abort(txId: txId)
    }
}

/// Extension to create TransactionMVCCAdapter from MVCCManager
extension MVCCManager {
    /// Create a TransactionMVCCAdapter from this MVCCManager instance
    nonisolated public func asTransactionMVCCManager() -> TransactionMVCCAdapter {
        return TransactionMVCCAdapter(mvccManager: self)
    }
}
