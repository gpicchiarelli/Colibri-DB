//
//  TransactionWALAdapter.swift
//  ColibrìDB Transaction WAL Adapter
//
//  Adapter to make FileWAL compatible with TransactionWALManager protocol
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//

import Foundation

/// Adapter that makes FileWAL compatible with TransactionWALManager protocol
/// Transaction WAL Adapter - bridges FileWAL to TransactionWALManager
/// Also implements WALManagerProtocol for Catalog durability
public actor TransactionWALAdapter: TransactionWALManager, WALManagerProtocol {
    
    private let fileWAL: FileWAL
    
    public init(fileWAL: FileWAL) {
        self.fileWAL = fileWAL
    }
    
    /// Append a record to the WAL
    public func appendRecord(txId: TxID, record: String) async throws {
        // Convert string record to WAL record
        let data = record.data(using: .utf8) ?? Data()
        _ = try await fileWAL.append(
            kind: .heapUpdate,
            txID: txId,
            pageID: 0, // Default page ID for transaction records
            payload: data
        )
    }
    
    /// Flush all pending records to disk
    public func flushLog() async throws {
        try await fileWAL.flush()
    }
    
    // MARK: - WALManagerProtocol Implementation (for Catalog)
    
    /// Append a record to the WAL (WALManagerProtocol signature)
    /// Used by Catalog for DDL operation logging
    public func appendRecord(txId: TxID, kind: String, data: Data) async throws -> LSN {
        // Convert kind string to WALRecordKind
        let recordKind: WALRecordKind
        switch kind.lowercased() {
        case "ddl", "create_table", "drop_table", "alter_table", "create_index", "drop_index":
            recordKind = .heapUpdate // Use heapUpdate for DDL operations
        default:
            recordKind = .heapUpdate
        }
        
        return try await fileWAL.append(
            kind: recordKind,
            txID: txId,
            pageID: 0,
            payload: data
        )
    }
}

/// Extension to create TransactionWALAdapter from FileWAL
extension FileWAL {
    /// Create a TransactionWALAdapter from this FileWAL instance
    nonisolated public func asTransactionWALManager() -> TransactionWALAdapter {
        return TransactionWALAdapter(fileWAL: self)
    }
}
