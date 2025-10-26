//
//  WALRecord.swift
//  ColibrìDB WAL Record Format
//
//  Based on: spec/WAL.tla
//  Implements: WAL record structure with header and checksum
//  Author: ColibrìDB Team
//  Date: 2025-10-26
//
//  Key Properties:
//  - Fixed-size header for fast parsing
//  - CRC32 checksum for data integrity
//  - Monotonic LSN assignment
//  - Support for different record types
//

import Foundation

/// WAL Record Type
/// Corresponds to TLA+: WALRecordType
public enum WALRecordType: UInt8, CaseIterable, Sendable {
    case update = 0x01      // Page update record
    case commit = 0x02      // Transaction commit
    case abort = 0x03       // Transaction abort
    case checkpoint = 0x04  // Checkpoint record
    case begin = 0x05       // Transaction begin
    case clr = 0x06         // Compensation Log Record (ARIES)
    case prepare = 0x07     // 2PC prepare
    case rollback = 0x08    // Transaction rollback
    
    /// Human-readable description
    public var description: String {
        switch self {
        case .update: return "UPDATE"
        case .commit: return "COMMIT"
        case .abort: return "ABORT"
        case .checkpoint: return "CHECKPOINT"
        case .begin: return "BEGIN"
        case .clr: return "CLR"
        case .prepare: return "PREPARE"
        case .rollback: return "ROLLBACK"
        }
    }
}

/// WAL Record Header
/// Fixed-size header for all WAL records
/// Corresponds to TLA+: WALRecordHeader
public struct WALRecordHeaderWithChecksum: Sendable {
    /// Record type (1 byte)
    public let type: WALRecordType
    
    /// Transaction ID (8 bytes)
    public let txId: TxID
    
    /// Log Sequence Number (8 bytes)
    public let lsn: LSN
    
    /// Previous LSN for this transaction (8 bytes, 0 if none)
    public let prevLsn: LSN
    
    /// Page ID if applicable (8 bytes, 0 if not applicable)
    public let pageId: PageID
    
    /// Payload length in bytes (4 bytes)
    public let payloadLength: UInt32
    
    /// CRC32 checksum of header + payload (4 bytes)
    public let checksum: UInt32
    
    /// Timestamp when record was created (8 bytes)
    public let timestamp: UInt64
    
    /// Total header size in bytes
    public static let size = 49 // 1 + 8 + 8 + 8 + 8 + 4 + 4 + 8
    
    public init(
        type: WALRecordType,
        txId: TxID,
        lsn: LSN,
        prevLsn: LSN = 0,
        pageId: PageID = 0,
        payloadLength: UInt32,
        checksum: UInt32 = 0,
        timestamp: UInt64 = UInt64(Date().timeIntervalSince1970 * 1000)
    ) {
        self.type = type
        self.txId = txId
        self.lsn = lsn
        self.prevLsn = prevLsn
        self.pageId = pageId
        self.payloadLength = payloadLength
        self.checksum = checksum
        self.timestamp = timestamp
    }
}

/// WAL Record
/// Complete WAL record with header and payload
/// Corresponds to TLA+: WALRecord
public struct WALRecordWithChecksum: Sendable {
    /// Record header
    public let header: WALRecordHeaderWithChecksum
    
    /// Record payload data
    public let payload: Data
    
    /// Total record size in bytes
    public var totalSize: Int {
        return WALRecordHeaderWithChecksum.size + payload.count
    }
    
    public init(header: WALRecordHeaderWithChecksum, payload: Data) {
        self.header = header
        self.payload = payload
    }
    
    /// Create a WAL record with automatic checksum calculation
    /// - Parameters:
    ///   - type: Record type
    ///   - txId: Transaction ID
    ///   - lsn: Log Sequence Number
    ///   - prevLsn: Previous LSN for this transaction
    ///   - pageId: Page ID if applicable
    ///   - payload: Record payload data
    /// - Returns: WAL record with calculated checksum
    public static func create(
        type: WALRecordType,
        txId: TxID,
        lsn: LSN,
        prevLsn: LSN = 0,
        pageId: PageID = 0,
        payload: Data
    ) -> WALRecordWithChecksum {
        let header = WALRecordHeaderWithChecksum(
            type: type,
            txId: txId,
            lsn: lsn,
            prevLsn: prevLsn,
            pageId: pageId,
            payloadLength: UInt32(payload.count)
        )
        
        let record = WALRecord(header: header, payload: payload)
        let checksum = record.calculateChecksum()
        
        let headerWithChecksum = WALRecordHeader(
            type: type,
            txId: txId,
            lsn: lsn,
            prevLsn: prevLsn,
            pageId: pageId,
            payloadLength: UInt32(payload.count),
            checksum: checksum,
            timestamp: header.timestamp
        )
        
        return WALRecordWithChecksum(header: headerWithChecksum, payload: payload)
    }
    
    /// Calculate CRC32 checksum for the entire record
    /// - Returns: CRC32 checksum value
    public func calculateChecksum() -> UInt32 {
        var data = Data()
        
        // Serialize header without checksum
        data.append(contentsOf: [header.type.rawValue])
        data.append(contentsOf: header.txId.littleEndianBytes)
        data.append(contentsOf: header.lsn.littleEndianBytes)
        data.append(contentsOf: header.prevLsn.littleEndianBytes)
        data.append(contentsOf: header.pageId.littleEndianBytes)
        data.append(contentsOf: header.payloadLength.littleEndianBytes)
        data.append(contentsOf: header.timestamp.littleEndianBytes)
        
        // Add payload
        data.append(payload)
        
        return CRC32Accelerator.calculate(data)
    }
    
    /// Verify the record's checksum
    /// - Returns: true if checksum is valid
    public func verifyChecksum() -> Bool {
        return calculateChecksum() == header.checksum
    }
    
    /// Serialize the record to binary format
    /// - Returns: Binary representation of the record
    public func serialize() -> Data {
        var data = Data()
        
        // Serialize header
        data.append(contentsOf: [header.type.rawValue])
        data.append(contentsOf: header.txId.littleEndianBytes)
        data.append(contentsOf: header.lsn.littleEndianBytes)
        data.append(contentsOf: header.prevLsn.littleEndianBytes)
        data.append(contentsOf: header.pageId.littleEndianBytes)
        data.append(contentsOf: header.payloadLength.littleEndianBytes)
        data.append(contentsOf: header.checksum.littleEndianBytes)
        data.append(contentsOf: header.timestamp.littleEndianBytes)
        
        // Add payload
        data.append(payload)
        
        return data
    }
    
    /// Deserialize a record from binary format
    /// - Parameter data: Binary data to deserialize
    /// - Returns: WAL record or nil if deserialization fails
    public static func deserialize(from data: Data) -> WALRecordWithChecksum? {
        guard data.count >= WALRecordHeaderWithChecksum.size else {
            return nil
        }
        
        var offset = 0
        
        // Deserialize header
        guard let type = WALRecordType(rawValue: data[offset]) else {
            return nil
        }
        offset += 1
        
        let txId: TxID
        let lsn: LSN
        let prevLsn: LSN
        let pageId: PageID
        let payloadLength: UInt32
        let checksum: UInt32
        let timestamp: UInt64
        
        data.withUnsafeBytes { bytes in
            let buffer = bytes.bindMemory(to: UInt8.self)
            
            txId = TxID(buffer.load(fromByteOffset: offset, as: UInt64.self))
            offset += 8
            
            lsn = LSN(buffer.load(fromByteOffset: offset, as: UInt64.self))
            offset += 8
            
            prevLsn = LSN(buffer.load(fromByteOffset: offset, as: UInt64.self))
            offset += 8
            
            pageId = PageID(buffer.load(fromByteOffset: offset, as: UInt64.self))
            offset += 8
            
            payloadLength = buffer.load(fromByteOffset: offset, as: UInt32.self)
            offset += 4
            
            checksum = buffer.load(fromByteOffset: offset, as: UInt32.self)
            offset += 4
            
            timestamp = buffer.load(fromByteOffset: offset, as: UInt64.self)
            offset += 8
        }
        
        // Extract payload
        guard data.count >= offset + Int(payloadLength) else {
            return nil
        }
        
        let payload = data.subdata(in: offset..<offset + Int(payloadLength))
        
        let header = WALRecordHeaderWithChecksum(
            type: type,
            txId: txId,
            lsn: lsn,
            prevLsn: prevLsn,
            pageId: pageId,
            payloadLength: payloadLength,
            checksum: checksum,
            timestamp: timestamp
        )
        
        return WALRecordWithChecksum(header: header, payload: payload)
    }
}

// MARK: - Extensions for Binary Conversion

extension TxID {
    /// Convert to little-endian byte array
    var littleEndianBytes: [UInt8] {
        return withUnsafeBytes(of: self.littleEndian) { bytes in
            return Array(bytes)
        }
    }
}

extension LSN {
    /// Convert to little-endian byte array
    var littleEndianBytes: [UInt8] {
        return withUnsafeBytes(of: self.littleEndian) { bytes in
            return Array(bytes)
        }
    }
}

extension PageID {
    /// Convert to little-endian byte array
    var littleEndianBytes: [UInt8] {
        return withUnsafeBytes(of: self.littleEndian) { bytes in
            return Array(bytes)
        }
    }
}

extension UInt32 {
    /// Convert to little-endian byte array
    var littleEndianBytes: [UInt8] {
        return withUnsafeBytes(of: self.littleEndian) { bytes in
            return Array(bytes)
        }
    }
}

extension UInt64 {
    /// Convert to little-endian byte array
    var littleEndianBytes: [UInt8] {
        return withUnsafeBytes(of: self.littleEndian) { bytes in
            return Array(bytes)
        }
    }
}
