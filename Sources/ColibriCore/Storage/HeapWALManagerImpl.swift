//
//  HeapWALManagerImpl.swift
//  ColibrìDB Heap WAL Manager Implementation
//
//  Concrete implementation of HeapWALManager protocol
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//

import Foundation

/// Concrete implementation of HeapWALManager protocol
public actor HeapWALManagerImpl: HeapWALManager {
    // MARK: - Properties
    
    private let wal: FileWAL
    
    // MARK: - Initialization
    
    /// Initialize heap WAL manager implementation
    /// - Parameter wal: WAL instance to use
    public init(wal: FileWAL) {
        self.wal = wal
    }
    
    // MARK: - Protocol Implementation
    
    /// Append a record to the WAL
    /// - Parameters:
    ///   - txId: Transaction ID
    ///   - kind: Record kind (insert, update, delete)
    ///   - data: Record data
    /// - Returns: Log sequence number (LSN)
    public func appendRecord(txId: TxID, kind: String, data: Data) async throws -> LSN {
        // Convert string kind to WALRecordKind
        let walKind: WALRecordKind
        switch kind.lowercased() {
        case "insert", "heapinsert":
            walKind = .heapInsert
        case "update", "heapupdate":
            walKind = .heapUpdate
        case "delete", "heapdelete":
            walKind = .heapDelete
        default:
            walKind = .heapUpdate
        }
        
        return try await wal.append(
            kind: walKind,
            txID: txId,
            pageID: PageID(0), // Will be set by caller
            payload: data
        )
    }
    
    /// Flush the WAL to disk
    public func flushLog() async throws {
        try await wal.flush()
    }
}

