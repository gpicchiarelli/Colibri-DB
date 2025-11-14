//
//  HeapWALManager.swift
//  ColibrìDB Heap WAL Manager
//
//  Implements: WAL management for heap tables
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//

import Foundation

/// Heap WAL Manager protocol (matches HeapTableManager requirements)
public protocol HeapWALManager: Sendable {
    func appendRecord(txId: TxID, kind: String, data: Data) async throws -> LSN
    func flushLog() async throws
}

/// Default heap WAL manager implementation
public actor DefaultHeapWALManager: HeapWALManager {
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

