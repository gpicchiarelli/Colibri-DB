//
//  WALProtocols.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-27.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Global WAL protocol definitions for unified Write-Ahead Logging

import Foundation

// MARK: - WAL Record Types

/// Kind of WAL record for type-safe logging
public enum WALKind: UInt8, Codable, CaseIterable {
    case begin = 1
    case commit = 2
    case abort = 3
    case heapInsert = 10
    case heapUpdate = 11
    case heapDelete = 12
    case indexInsert = 20
    case indexDelete = 21
    case catalogCreate = 30
    case catalogDrop = 31
    case catalogUpdate = 32
    case checkpoint = 40
    case clr = 50  // Compensation Log Record (for UNDO)
}

/// Base protocol for all WAL records
public protocol WALRecord: Codable {
    var lsn: UInt64 { get set }
    var dbId: UInt32 { get }
    var kind: WALKind { get }
    var pageId: UInt64? { get }  // Optional page affected by this record
}

// MARK: - Transaction Records

/// Begin transaction record
public struct WALBeginRecord: WALRecord {
    public var lsn: UInt64
    public let dbId: UInt32
    public let txId: UInt64
    public let isolationLevel: IsolationLevel
    public let timestamp: Date
    
    public var kind: WALKind { .begin }
    public var pageId: UInt64? { nil }
    
    public init(lsn: UInt64 = 0, dbId: UInt32, txId: UInt64, isolationLevel: IsolationLevel, timestamp: Date = Date()) {
        self.lsn = lsn
        self.dbId = dbId
        self.txId = txId
        self.isolationLevel = isolationLevel
        self.timestamp = timestamp
    }
}

/// Commit transaction record
public struct WALCommitRecord: WALRecord {
    public var lsn: UInt64
    public let dbId: UInt32
    public let txId: UInt64
    public let commitTimestamp: Date
    public let preparedLSN: UInt64?  // For 2PC
    
    public var kind: WALKind { .commit }
    public var pageId: UInt64? { nil }
    
    public init(lsn: UInt64 = 0, dbId: UInt32, txId: UInt64, commitTimestamp: Date = Date(), preparedLSN: UInt64? = nil) {
        self.lsn = lsn
        self.dbId = dbId
        self.txId = txId
        self.commitTimestamp = commitTimestamp
        self.preparedLSN = preparedLSN
    }
}

/// Abort transaction record
public struct WALAbortRecord: WALRecord {
    public var lsn: UInt64
    public let dbId: UInt32
    public let txId: UInt64
    public let reason: String?
    
    public var kind: WALKind { .abort }
    public var pageId: UInt64? { nil }
    
    public init(lsn: UInt64 = 0, dbId: UInt32, txId: UInt64, reason: String? = nil) {
        self.lsn = lsn
        self.dbId = dbId
        self.txId = txId
        self.reason = reason
    }
}

// MARK: - Heap Records

/// Heap insert record
public struct WALHeapInsertRecord: WALRecord {
    public var lsn: UInt64
    public let dbId: UInt32
    public let txId: UInt64
    public let tableId: String
    public let recordPageId: UInt64
    public let slotId: UInt16
    public let rowData: Data
    
    public var kind: WALKind { .heapInsert }
    public var pageId: UInt64? { recordPageId }
    
    public init(lsn: UInt64 = 0, dbId: UInt32, txId: UInt64, tableId: String, pageId: UInt64, slotId: UInt16, rowData: Data) {
        self.lsn = lsn
        self.dbId = dbId
        self.txId = txId
        self.tableId = tableId
        self.recordPageId = pageId
        self.slotId = slotId
        self.rowData = rowData
    }
}

/// Heap update record
public struct WALHeapUpdateRecord: WALRecord {
    public var lsn: UInt64
    public let dbId: UInt32
    public let txId: UInt64
    public let tableId: String
    public let recordPageId: UInt64
    public let slotId: UInt16
    public let oldRowData: Data
    public let newRowData: Data
    
    public var kind: WALKind { .heapUpdate }
    public var pageId: UInt64? { recordPageId }
    
    public init(lsn: UInt64 = 0, dbId: UInt32, txId: UInt64, tableId: String, pageId: UInt64, slotId: UInt16, oldRowData: Data, newRowData: Data) {
        self.lsn = lsn
        self.dbId = dbId
        self.txId = txId
        self.tableId = tableId
        self.recordPageId = pageId
        self.slotId = slotId
        self.oldRowData = oldRowData
        self.newRowData = newRowData
    }
}

/// Heap delete record
public struct WALHeapDeleteRecord: WALRecord {
    public var lsn: UInt64
    public let dbId: UInt32
    public let txId: UInt64
    public let tableId: String
    public let recordPageId: UInt64
    public let slotId: UInt16
    public let rowData: Data  // For UNDO
    
    public var kind: WALKind { .heapDelete }
    public var pageId: UInt64? { recordPageId }
    
    public init(lsn: UInt64 = 0, dbId: UInt32, txId: UInt64, tableId: String, pageId: UInt64, slotId: UInt16, rowData: Data) {
        self.lsn = lsn
        self.dbId = dbId
        self.txId = txId
        self.tableId = tableId
        self.recordPageId = pageId
        self.slotId = slotId
        self.rowData = rowData
    }
}

// MARK: - Index Records

/// Index insert record
public struct WALIndexInsertRecord: WALRecord {
    public var lsn: UInt64
    public let dbId: UInt32
    public let txId: UInt64
    public let indexId: String
    public let tableId: String
    public let keyBytes: Data
    public let ridPageId: UInt64
    public let ridSlotId: UInt16
    
    public var kind: WALKind { .indexInsert }
    public var pageId: UInt64? { ridPageId }  // Page containing the row being indexed
    
    public init(lsn: UInt64 = 0, dbId: UInt32, txId: UInt64, indexId: String, tableId: String, keyBytes: Data, ridPageId: UInt64, ridSlotId: UInt16) {
        self.lsn = lsn
        self.dbId = dbId
        self.txId = txId
        self.indexId = indexId
        self.tableId = tableId
        self.keyBytes = keyBytes
        self.ridPageId = ridPageId
        self.ridSlotId = ridSlotId
    }
}

/// Index delete record
public struct WALIndexDeleteRecord: WALRecord {
    public var lsn: UInt64
    public let dbId: UInt32
    public let txId: UInt64
    public let indexId: String
    public let tableId: String
    public let keyBytes: Data
    public let ridPageId: UInt64
    public let ridSlotId: UInt16
    
    public var kind: WALKind { .indexDelete }
    public var pageId: UInt64? { ridPageId }
    
    public init(lsn: UInt64 = 0, dbId: UInt32, txId: UInt64, indexId: String, tableId: String, keyBytes: Data, ridPageId: UInt64, ridSlotId: UInt16) {
        self.lsn = lsn
        self.dbId = dbId
        self.txId = txId
        self.indexId = indexId
        self.tableId = tableId
        self.keyBytes = keyBytes
        self.ridPageId = ridPageId
        self.ridSlotId = ridSlotId
    }
}

// MARK: - Catalog Records

/// Catalog operation record (DDL)
public struct WALCatalogRecord: WALRecord {
    public var lsn: UInt64
    public let dbId: UInt32
    public let txId: UInt64
    public let operation: CatalogOperation
    public let objectType: String  // "table", "index", "constraint"
    public let objectName: String
    public let metadata: Data?  // Serialized metadata
    
    public var kind: WALKind { 
        switch operation {
        case .create: return .catalogCreate
        case .drop: return .catalogDrop
        case .update: return .catalogUpdate
        }
    }
    public var pageId: UInt64? { nil }
    
    public enum CatalogOperation: String, Codable {
        case create, drop, update
    }
    
    public init(lsn: UInt64 = 0, dbId: UInt32, txId: UInt64, operation: CatalogOperation, objectType: String, objectName: String, metadata: Data? = nil) {
        self.lsn = lsn
        self.dbId = dbId
        self.txId = txId
        self.operation = operation
        self.objectType = objectType
        self.objectName = objectName
        self.metadata = metadata
    }
}

// MARK: - System Records

/// Checkpoint record
public struct WALCheckpointRecord: WALRecord {
    public var lsn: UInt64
    public let dbId: UInt32
    public let dirtyPageTable: [UInt64: UInt64]  // pageId -> recLSN
    public let activeTransactionTable: [UInt64: UInt64]  // txId -> lastLSN
    public let checkpointTimestamp: Date
    
    public var kind: WALKind { .checkpoint }
    public var pageId: UInt64? { nil }
    
    public init(lsn: UInt64 = 0, dbId: UInt32, dirtyPageTable: [UInt64: UInt64], activeTransactionTable: [UInt64: UInt64], checkpointTimestamp: Date = Date()) {
        self.lsn = lsn
        self.dbId = dbId
        self.dirtyPageTable = dirtyPageTable
        self.activeTransactionTable = activeTransactionTable
        self.checkpointTimestamp = checkpointTimestamp
    }
}

/// Compensation Log Record (for UNDO operations)
public struct WALCLRRecord: WALRecord {
    public var lsn: UInt64
    public let dbId: UInt32
    public let txId: UInt64
    public let undoNextLSN: UInt64  // Next LSN to undo in this transaction
    public let undoneOperationLSN: UInt64  // LSN of the operation being undone
    public let undoAction: UndoAction
    
    public var kind: WALKind { .clr }
    public var pageId: UInt64? { undoAction.pageId }
    
    public enum UndoAction: Codable {
        case heapInsert(pageId: UInt64, slotId: UInt16)
        case heapDelete(pageId: UInt64, slotId: UInt16, rowData: Data)
        case heapUpdate(pageId: UInt64, slotId: UInt16, originalData: Data)
        case indexInsert(indexId: String, keyBytes: Data, ridPageId: UInt64, ridSlotId: UInt16)
        case indexDelete(indexId: String, keyBytes: Data, ridPageId: UInt64, ridSlotId: UInt16)
        
        var pageId: UInt64? {
            switch self {
            case .heapInsert(let pageId, _), .heapDelete(let pageId, _, _), .heapUpdate(let pageId, _, _):
                return pageId
            case .indexInsert(_, _, let ridPageId, _), .indexDelete(_, _, let ridPageId, _):
                return ridPageId
            }
        }
    }
    
    public init(lsn: UInt64 = 0, dbId: UInt32, txId: UInt64, undoNextLSN: UInt64, undoneOperationLSN: UInt64, undoAction: UndoAction) {
        self.lsn = lsn
        self.dbId = dbId
        self.txId = txId
        self.undoNextLSN = undoNextLSN
        self.undoneOperationLSN = undoneOperationLSN
        self.undoAction = undoAction
    }
}

// MARK: - WAL Interfaces

/// WAL writer interface for appending records
public protocol WALWriter {
    /// Appends a record to the WAL and returns its assigned LSN
    @discardableResult func append(_ record: WALRecord) throws -> UInt64
    
    /// Forces synchronization of all pending records to disk
    func groupCommitSync() throws
    
    /// Returns the highest LSN that has been durably written to disk
    var flushedLSN: UInt64 { get }
    
    /// Flushes all records up to and including the specified LSN
    func flush(upTo lsn: UInt64) throws
}

/// WAL reader interface for iterating records
public protocol WALReader {
    /// Creates an iterator starting from the specified LSN
    func iterate(from lsn: UInt64) throws -> AnyIterator<WALRecord>
    
    /// Returns the highest LSN in the WAL
    func lastLSN() throws -> UInt64
    
    /// Reads a specific record by LSN
    func read(lsn: UInt64) throws -> WALRecord?
}

/// WAL checkpointing interface
public protocol WALCheckpointing {
    /// Writes a checkpoint record with current DPT and ATT
    @discardableResult func writeCheckpoint(dpt: [UInt64: UInt64], att: [UInt64: UInt64]) throws -> UInt64
    
    /// Reads the most recent checkpoint
    func readLastCheckpoint() throws -> WALCheckpointRecord?
    
    /// Truncates the WAL up to the specified LSN (after checkpoint)
    func truncate(upTo lsn: UInt64) throws
}

/// Unified WAL manager interface
public protocol WALManager: WALWriter, WALReader, WALCheckpointing {
    /// Database ID this WAL instance serves
    var dbId: UInt32 { get }
    
    /// Configuration for durability and performance
    var durabilityMode: DurabilityMode { get set }
    
    /// Metrics for monitoring
    var metrics: WALMetrics { get }
    
    /// Closes the WAL and flushes pending data
    func close() throws
}

// MARK: - Configuration

/// Durability mode for WAL operations
public enum DurabilityMode: String, Codable {
    case always      // fsync after every record
    case grouped     // group commit with timeout
    case relaxed     // asynchronous, risk of loss on crash
}

/// WAL performance metrics
public struct WALMetrics: Codable {
    public let appendsPerSecond: Double
    public let bytesPerSecond: Double
    public let fsyncsPerSecond: Double
    public let averageBatchSize: Double
    public let p95CommitLatencyMs: Double
    public let currentFlushedLSN: UInt64
    public let queueDepth: Int
    public let compressionRatio: Double?
    
    public init(appendsPerSecond: Double, bytesPerSecond: Double, fsyncsPerSecond: Double, averageBatchSize: Double, p95CommitLatencyMs: Double, currentFlushedLSN: UInt64, queueDepth: Int, compressionRatio: Double? = nil) {
        self.appendsPerSecond = appendsPerSecond
        self.bytesPerSecond = bytesPerSecond
        self.fsyncsPerSecond = fsyncsPerSecond
        self.averageBatchSize = averageBatchSize
        self.p95CommitLatencyMs = p95CommitLatencyMs
        self.currentFlushedLSN = currentFlushedLSN
        self.queueDepth = queueDepth
        self.compressionRatio = compressionRatio
    }
}
