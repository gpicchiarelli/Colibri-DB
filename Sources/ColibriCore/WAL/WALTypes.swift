//
//  WALTypes.swift
//  ColibrìDB WAL Types
//
//  Based on: spec/WAL.tla
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//

import Foundation

// MARK: - WAL Record Implementations

/// Concrete WAL record structure
/// Based on ARIES paper (Mohan et al., 1992)
public struct ConcreteWALRecord: WALRecord {
    public let lsn: LSN
    public let prevLSN: LSN
    public let kind: WALRecordKind
    public let txID: TxID
    public let pageID: PageID
    public let undoNextLSN: LSN
    public let payload: Data?
    
    public init(
        lsn: LSN,
        prevLSN: LSN,
        kind: WALRecordKind,
        txID: TxID,
        pageID: PageID,
        undoNextLSN: LSN = 0,
        payload: Data? = nil
    ) {
        self.lsn = lsn
        self.prevLSN = prevLSN
        self.kind = kind
        self.txID = txID
        self.pageID = pageID
        self.undoNextLSN = undoNextLSN
        self.payload = payload
    }
}

// MARK: - WAL Record Types

/// Transaction begin record
public struct BeginRecord: Codable, Sendable {
    public let txID: TxID
    public let timestamp: Timestamp
    public let isolationLevel: IsolationLevel
    
    public init(txID: TxID, timestamp: Timestamp, isolationLevel: IsolationLevel) {
        self.txID = txID
        self.timestamp = timestamp
        self.isolationLevel = isolationLevel
    }
}

/// Transaction commit record
public struct CommitRecord: Codable, Sendable {
    public let txID: TxID
    public let timestamp: Timestamp
    
    public init(txID: TxID, timestamp: Timestamp) {
        self.txID = txID
        self.timestamp = timestamp
    }
}

/// Transaction abort record
public struct AbortRecord: Codable, Sendable {
    public let txID: TxID
    public let timestamp: Timestamp
    
    public init(txID: TxID, timestamp: Timestamp) {
        self.txID = txID
        self.timestamp = timestamp
    }
}

/// Heap insert record
public struct HeapInsertRecord: Codable, Sendable {
    public let txID: TxID
    public let pageID: PageID
    public let slotID: UInt32
    public let data: Data
    
    public init(txID: TxID, pageID: PageID, slotID: UInt32, data: Data) {
        self.txID = txID
        self.pageID = pageID
        self.slotID = slotID
        self.data = data
    }
}

/// Heap update record
public struct HeapUpdateRecord: Codable, Sendable {
    public let txID: TxID
    public let pageID: PageID
    public let slotID: UInt32
    public let oldData: Data
    public let newData: Data
    
    public init(txID: TxID, pageID: PageID, slotID: UInt32, oldData: Data, newData: Data) {
        self.txID = txID
        self.pageID = pageID
        self.slotID = slotID
        self.oldData = oldData
        self.newData = newData
    }
}

/// Heap delete record
public struct HeapDeleteRecord: Codable, Sendable {
    public let txID: TxID
    public let pageID: PageID
    public let slotID: UInt32
    public let data: Data
    
    public init(txID: TxID, pageID: PageID, slotID: UInt32, data: Data) {
        self.txID = txID
        self.pageID = pageID
        self.slotID = slotID
        self.data = data
    }
}

/// Compensation Log Record (CLR) - for undo operations
/// Based on ARIES paper
public struct CLRRecord: Codable, Sendable {
    public let txID: TxID
    public let undoNextLSN: LSN
    public let pageID: PageID
    public let operation: WALRecordKind
    
    public init(txID: TxID, undoNextLSN: LSN, pageID: PageID, operation: WALRecordKind) {
        self.txID = txID
        self.undoNextLSN = undoNextLSN
        self.pageID = pageID
        self.operation = operation
    }
}

/// Checkpoint record structure
/// Contains Dirty Page Table and Active Transaction Table
public struct CheckpointRecord: Codable, Sendable {
    public let checkpointLSN: LSN
    public let dirtyPageTable: [PageID: LSN]  // PageID -> recLSN
    public let activeTransactionTable: [TxID: LSN]  // TxID -> lastLSN
    
    public init(
        checkpointLSN: LSN,
        dirtyPageTable: [PageID: LSN],
        activeTransactionTable: [TxID: LSN]
    ) {
        self.checkpointLSN = checkpointLSN
        self.dirtyPageTable = dirtyPageTable
        self.activeTransactionTable = activeTransactionTable
    }
}

// MARK: - WAL File Header

/// WAL file header
/// Magic: 'CBDW' (ColibrìDB WAL)
/// Version: 2
public struct WALFileHeader: Codable, Sendable {
    public static let magic: UInt32 = 0x43424457  // 'CBDW'
    public static let version: UInt16 = 2
    
    public let magic: UInt32
    public let version: UInt16
    public let createdAt: Date
    public let pageSize: UInt32
    
    public init(pageSize: UInt32 = UInt32(PAGE_SIZE)) {
        self.magic = Self.magic
        self.version = Self.version
        self.createdAt = Date()
        self.pageSize = pageSize
    }
    
    public var isValid: Bool {
        return magic == Self.magic && version == Self.version
    }
}

// MARK: - WAL Record Header (On-Disk Format)

/// On-disk WAL record header
/// CRC32 | type | LSN | prevLSN | pageID | length | payload
public struct WALRecordHeader: Codable, Sendable {
    public let crc32: UInt32
    public let type: WALRecordKind
    public let lsn: LSN
    public let prevLSN: LSN
    public let pageID: PageID
    public let length: UInt32
    
    public init(
        crc32: UInt32,
        type: WALRecordKind,
        lsn: LSN,
        prevLSN: LSN,
        pageID: PageID,
        length: UInt32
    ) {
        self.crc32 = crc32
        self.type = type
        self.lsn = lsn
        self.prevLSN = prevLSN
        self.pageID = pageID
        self.length = length
    }
    
    public static var size: Int {
        let crc32Size = MemoryLayout<UInt32>.size
        let typeSize = MemoryLayout<UInt8>.size
        let lsnSize = MemoryLayout<LSN>.size
        let prevLsnSize = MemoryLayout<LSN>.size
        let pageIdSize = MemoryLayout<PageID>.size
        let lengthSize = MemoryLayout<UInt32>.size
        
        return crc32Size + typeSize + lsnSize + prevLsnSize + pageIdSize + lengthSize
    }
}

/// Full WAL record with payload (on-disk)
public struct WALRecordWithPayload: Codable, Sendable {
    public let header: WALRecordHeader
    public let payload: Data
    
    public init(header: WALRecordHeader, payload: Data) {
        self.header = header
        self.payload = payload
    }
    
    public var isValid: Bool {
        return header.length == payload.count
    }
}


// MARK: - Dirty Page Table (DPT)

/// Dirty Page Table entry
/// Maps PageID -> recLSN (first LSN that dirtied the page)
public typealias DirtyPageTable = [PageID: LSN]

// MARK: - Active Transaction Table (ATT)

/// Active Transaction Table entry
/// Maps TxID -> lastLSN (last LSN written by transaction)
public typealias ActiveTransactionTable = [TxID: LSN]

