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
    private let wal: FileWAL
    
    public init(wal: FileWAL) {
        self.wal = wal
    }
    
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
    
    public func flushLog() async throws {
        try await wal.flush()
    }
}

