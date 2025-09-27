//
//  FileWAL.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Write-ahead log forge preserving transactional history.

import Foundation
#if os(macOS)
import Darwin
#endif
import Dispatch
/// File-based Write-Ahead Log (WAL) with CRC and versioned record format.

public final class FileWAL: WALProtocol {
    // Header: 'CBDW'(4) | ver u16 (=2)
    // v1 Record (legacy): CRC32 u32 | type u8 | LSN u64 | len u32 | payload
    // v2 Record: CRC32 u32 | type u8 | LSN u64 | prevLSN u64 | pageId u64 | len u32 | payload
    public enum RecType: UInt8 { case insertRow = 1, deleteRid = 2, checkpoint = 3, begin = 4, commit = 5, abort = 6, insertPre = 7, insertDone = 8, deleteRow = 9, clr = 10 }
    public enum RecTypeV3: UInt8 { case indexInsert = 21, indexDelete = 22, catalogUpsert = 23 }

    private let url: URL
    private var fh: FileHandle
    private var nextLSN: UInt64 = 1
    private var _flushedLSN: UInt64 = 0
    private let flushedLSNLock = NSLock()
    private var fullFSyncEnabled = false
    private var ioHintsEnabled = false
    private var compressionAlgorithm: CompressionAlgorithm = .none
    
    // Group commit optimization
    private var pendingRecords: [(lsn: UInt64, type: RecType, payload: Data, prevLSN: UInt64, pageId: UInt64)] = []
    private let groupCommitLock = NSLock()
    private let groupCommitThreshold = 8
    private let compressionQueue = DispatchQueue(label: "wal.compression", qos: .utility)
    private var groupCommitTimer: DispatchSourceTimer?
    private var groupCommitIntervalMs: Double = 2.0
    // Metrics
    private var lastFlushBatchSize: Int = 0
    private var lastFlushSyncNs: UInt64 = 0
    private var totalFlushes: Int = 0
    private var totalFlushedRecords: Int = 0
    private var totalSyncNs: UInt64 = 0

    private enum CompressionFlag {
        static let compressed: UInt8 = 0x80
        static let algorithmMask: UInt8 = 0x60
        static let typeMask: UInt8 = 0x1F

        static func encode(_ algorithm: CompressionAlgorithm) -> UInt8 {
            switch algorithm {
            case .none: return 0
            case .lzfse: return 0x20
            case .zlib: return 0x40
            }
        }

        static func decode(_ raw: UInt8) -> CompressionAlgorithm {
            let bits = raw & algorithmMask
            switch bits {
            case 0x20: return .lzfse
            case 0x40: return .zlib
            default: return .none
            }
        }
    }

    /// Opens/creates a WAL at the given path and sets the next LSN.
    public init(path: String) throws {
        self.url = URL(fileURLWithPath: path)
        let fm = FileManager.default
        if !fm.fileExists(atPath: path) { fm.createFile(atPath: path, contents: nil) }
        self.fh = try FileHandle(forUpdating: url)
        try ensureHeader()
        // compute nextLSN
        let records = try readAll()
        self.nextLSN = (records.last?.lsn ?? 0) &+ 1
        try fh.seekToEnd()
        startGroupCommitTimer(intervalMs: groupCommitIntervalMs)
    }

    deinit { try? fh.close() }

    public func setGroupCommit(intervalMs: Double) {
        groupCommitIntervalMs = max(0.0, intervalMs)
        startGroupCommitTimer(intervalMs: groupCommitIntervalMs)
    }

    private func startGroupCommitTimer(intervalMs: Double) {
        groupCommitTimer?.cancel(); groupCommitTimer = nil
        guard intervalMs > 0 else { return }
        let t = DispatchSource.makeTimerSource(queue: DispatchQueue(label: "wal.groupcommit", qos: .userInitiated))
        t.schedule(deadline: .now() + intervalMs/1000.0, repeating: intervalMs/1000.0)
        t.setEventHandler { [weak self] in
            guard let self = self else { return }
            try? self.flushPending()
        }
        t.resume()
        groupCommitTimer = t
    }

    public func setFullFSync(enabled: Bool) {
#if os(macOS)
        fullFSyncEnabled = enabled
#else
        fullFSyncEnabled = false
#endif
    }

    /// Enables best-effort sequential read hints for WAL replay.
    public func setIOHints(enabled: Bool) {
        ioHintsEnabled = enabled
    }

    public func setCompression(_ algorithm: CompressionAlgorithm) {
        compressionAlgorithm = algorithm
    }

    private func ensureHeader() throws {
        try fh.seek(toOffset: 0)
        let d = try fh.read(upToCount: 6) ?? Data()
        if d.count < 6 || String(data: d.prefix(4), encoding: .utf8) != "CBDW" {
            try fh.truncate(atOffset: 0)
            try fh.seek(toOffset: 0)
            var hdr = Data(); hdr.append(Data("CBDW".utf8))
            var ver: UInt16 = 2; hdr.append(Data(bytes: &ver, count: 2))
            try fh.write(contentsOf: hdr)
            try sync()
        }
        try fh.seekToEnd()
    }

    private func append(type: RecType, payload: Data, prevLSN: UInt64 = 0, pageId: UInt64 = 0) throws -> UInt64 {
        groupCommitLock.lock()
        let lsn = nextLSN
        pendingRecords.append((lsn: lsn, type: type, payload: payload, prevLSN: prevLSN, pageId: pageId))
        nextLSN &+= 1
        
        if pendingRecords.count >= groupCommitThreshold {
            let recordsToFlush = pendingRecords
            pendingRecords.removeAll()
            groupCommitLock.unlock()
            try flushGroup(records: recordsToFlush)
        } else {
            groupCommitLock.unlock()
        }
        return lsn
    }
    
    private func flushGroup(records: [(lsn: UInt64, type: RecType, payload: Data, prevLSN: UInt64, pageId: UInt64)]) throws {
        try ensureHeader()
        if FaultInjector.shared.shouldFail(key: "wal.append") { throw DBError.io("fault injection: wal.append") }
        
        var batchData = Data()
        let batchCount = records.count
        for record in records {
            var payloadToWrite = record.payload
            var typeByte = record.type.rawValue
            
            // Async compression for large payloads
            if record.payload.count > 1024 && compressionAlgorithm != .none {
                let payloadCopy = record.payload
                let algo = compressionAlgorithm
                compressionQueue.async {
                    if let _ = CompressionCodec.compress(payloadCopy, algorithm: algo) {
                        // background
                    }
                }
            } else if let compressed = CompressionCodec.compress(record.payload, algorithm: compressionAlgorithm) {
                var original = UInt32(record.payload.count).bigEndian
                var header = Data(capacity: 4)
                header.append(Data(bytes: &original, count: 4))
                payloadToWrite = header + compressed
                typeByte |= CompressionFlag.compressed | CompressionFlag.encode(compressionAlgorithm)
            }

            var rec = Data([typeByte])
            var beLSN = record.lsn.bigEndian
            var bePrev = record.prevLSN.bigEndian
            var bePage = record.pageId.bigEndian
            var len = UInt32(payloadToWrite.count).bigEndian
            rec.append(Data(bytes: &beLSN, count: 8))
            rec.append(Data(bytes: &bePrev, count: 8))
            rec.append(Data(bytes: &bePage, count: 8))
            rec.append(Data(bytes: &len, count: 4))
            rec.append(payloadToWrite)
            let crc = CRC32.compute(rec)
            var beCRC = crc.bigEndian
            batchData.append(Data(bytes: &beCRC, count: 4))
            batchData.append(rec)
        }
        
        try fh.write(contentsOf: batchData)
        let t0 = DispatchTime.now().uptimeNanoseconds
        try sync()
        let t1 = DispatchTime.now().uptimeNanoseconds
        
        // Update flushed LSN after successful sync
        let maxLSN = records.map { $0.lsn }.max() ?? 0
        flushedLSNLock.lock()
        _flushedLSN = max(_flushedLSN, maxLSN)
        flushedLSNLock.unlock()
        
        lastFlushBatchSize = batchCount
        lastFlushSyncNs = t1 &- t0
        totalFlushes &+= 1
        totalFlushedRecords &+= batchCount
        totalSyncNs &+= lastFlushSyncNs
    }
    
    public func flushPending() throws {
        groupCommitLock.lock()
        let recordsToFlush = pendingRecords
        pendingRecords.removeAll()
        groupCommitLock.unlock()
        if !recordsToFlush.isEmpty {
            try flushGroup(records: recordsToFlush)
        }
    }

    public struct Record { public let type: RecType; public let lsn: UInt64; public let payload: Data }

    /// Reads and validates all WAL records from the beginning.
    public func readAll() throws -> [Record] {
        if ioHintsEnabled {
            let length = try fh.seekToEnd()
            if length > 0 {
                IOHints.prepareSequentialRead(handle: fh, length: UInt64(length))
            }
        }
        try fh.seek(toOffset: 0)
        let data = try fh.readToEnd() ?? Data()
        var off = 0
        var res: [Record] = []
        guard data.count >= 6, String(data: data.subdata(in: 0..<4), encoding: .utf8) == "CBDW" else { return [] }
        let ver = data.subdata(in: 4..<6).withUnsafeBytes { $0.load(as: UInt16.self) }.bigEndian
        off = 6
        
        // Try to read records until we encounter corruption or end of file
        while off + 13 <= data.count {
            _ = off
            let crcStored = data.subdata(in: off..<(off+4)).withUnsafeBytes { $0.load(as: UInt32.self) }.bigEndian; off += 4
            let typRaw = data[off]; off += 1
            let algorithm = CompressionFlag.decode(typRaw)
            let isCompressed = (typRaw & CompressionFlag.compressed) != 0
            let typeBase = typRaw & CompressionFlag.typeMask
            let lsn = data.subdata(in: off..<(off+8)).withUnsafeBytes { $0.load(as: UInt64.self) }.bigEndian; off += 8
            if ver >= 2 { off += 8 /*prev*/; off += 8 /*page*/ }
            let len = Int(data.subdata(in: off..<(off+4)).withUnsafeBytes { $0.load(as: UInt32.self) }.bigEndian); off += 4
            
            // Check if we have enough data for the payload
            if off + len > data.count { break }
            
            var payload = data.subdata(in: off..<(off+len))
            let bodyStart = ver >= 2 ? (off - 1 - 8 - 8 - 8 - 4) : (off - 1 - 8 - 4)
            let recBody = data.subdata(in: bodyStart..<(off+len))
            let crcCalc = CRC32.compute(recBody)
            
            // If CRC doesn't match, stop reading but return what we have so far
            if crcCalc != crcStored { break }
            
            if isCompressed {
                guard payload.count > 4 else { break }
                let original = payload.subdata(in: 0..<4).withUnsafeBytes { $0.load(as: UInt32.self) }.bigEndian
                let compressedSlice = payload.subdata(in: 4..<payload.count)
                guard let decoded = try? CompressionCodec.decompress(compressedSlice, algorithm: algorithm, expectedSize: Int(original)) else {
                    break
                }
                payload = decoded
            }
            
            if let t = RecType(rawValue: typeBase) { 
                res.append(Record(type: t, lsn: lsn, payload: payload)) 
            }
            off += len
        }
        return res
    }

    // Encoders (v2 with defaults)
    public func appendInsert(table: String, row: Row, prevLSN: UInt64 = 0, pageId: UInt64 = 0) throws -> UInt64 {
        var p = Data()
        let t = table.data(using: .utf8) ?? Data()
        p.append(VarInt.encode(UInt64(t.count))); p.append(t)
        let bytes = try JSONEncoder().encode(row)
        p.append(VarInt.encode(UInt64(bytes.count))); p.append(bytes)
        return try append(type: .insertRow, payload: p, prevLSN: prevLSN, pageId: pageId)
    }
    public func appendDelete(table: String, rid: RID, prevLSN: UInt64 = 0) throws -> UInt64 {
        var p = Data(); let t = table.data(using: .utf8) ?? Data()
        p.append(VarInt.encode(UInt64(t.count))); p.append(t)
        var pid = rid.pageId.bigEndian; var sid = rid.slotId.bigEndian
        p.append(Data(bytes: &pid, count: 8)); p.append(Data(bytes: &sid, count: 2))
        return try append(type: .deleteRid, payload: p, prevLSN: prevLSN, pageId: rid.pageId)
    }
    public func appendCheckpoint(prevLSN: UInt64 = 0) throws -> UInt64 { try append(type: .checkpoint, payload: Data(), prevLSN: prevLSN) }
    public func appendBegin(tid: UInt64, prevLSN: UInt64 = 0) throws -> UInt64 { let p = VarInt.encode(tid); return try append(type: .begin, payload: p, prevLSN: prevLSN) }
    public func appendCommit(tid: UInt64, prevLSN: UInt64 = 0) throws -> UInt64 { let p = VarInt.encode(tid); return try append(type: .commit, payload: p, prevLSN: prevLSN) }
    public func appendAbort(tid: UInt64, prevLSN: UInt64 = 0) throws -> UInt64 { let p = VarInt.encode(tid); return try append(type: .abort, payload: p, prevLSN: prevLSN) }
    public func appendInsertPre(tid: UInt64, table: String, row: Row, prevLSN: UInt64 = 0) throws -> UInt64 {
        var p = VarInt.encode(tid); let t = table.data(using: .utf8) ?? Data()
        p.append(VarInt.encode(UInt64(t.count))); p.append(t)
        let bytes = try JSONEncoder().encode(row); p.append(VarInt.encode(UInt64(bytes.count))); p.append(bytes)
        return try append(type: .insertPre, payload: p, prevLSN: prevLSN)
    }
    public func appendInsertDone(tid: UInt64, table: String, rid: RID, prevLSN: UInt64 = 0) throws -> UInt64 {
        var p = VarInt.encode(tid); let t = table.data(using: .utf8) ?? Data()
        p.append(VarInt.encode(UInt64(t.count))); p.append(t)
        var pid = rid.pageId.bigEndian; var sid = rid.slotId.bigEndian
        p.append(Data(bytes: &pid, count: 8)); p.append(Data(bytes: &sid, count: 2))
        return try append(type: .insertDone, payload: p, prevLSN: prevLSN, pageId: rid.pageId)
    }
    public func appendDelete(tid: UInt64, table: String, rid: RID, row: Row, prevLSN: UInt64 = 0) throws -> UInt64 {
        var p = VarInt.encode(tid); let t = table.data(using: .utf8) ?? Data()
        p.append(VarInt.encode(UInt64(t.count))); p.append(t)
        var pid = rid.pageId.bigEndian; var sid = rid.slotId.bigEndian
        p.append(Data(bytes: &pid, count: 8)); p.append(Data(bytes: &sid, count: 2))
        let bytes = try JSONEncoder().encode(row); p.append(VarInt.encode(UInt64(bytes.count))); p.append(bytes)
        return try append(type: .deleteRow, payload: p, prevLSN: prevLSN, pageId: rid.pageId)
    }

    // MARK: - V3: Index logging (global WAL)
    public func appendIndexInsert(table: String, index: String, keyBytes: Data, rid: RID, prevLSN: UInt64 = 0) throws -> UInt64 {
        var p = Data()
        let tt = table.data(using: .utf8) ?? Data()
        let ii = index.data(using: .utf8) ?? Data()
        p.append(VarInt.encode(UInt64(tt.count))); p.append(tt)
        p.append(VarInt.encode(UInt64(ii.count))); p.append(ii)
        p.append(VarInt.encode(UInt64(keyBytes.count))); p.append(keyBytes)
        var pid = rid.pageId.bigEndian; var sid = rid.slotId.bigEndian
        p.append(Data(bytes: &pid, count: 8)); p.append(Data(bytes: &sid, count: 2))
        return try append(type: .insertRow, payload: p, prevLSN: prevLSN) // reuse insertRow channel; versioning via catalog
    }

    public func appendIndexDelete(table: String, index: String, keyBytes: Data, rid: RID, prevLSN: UInt64 = 0) throws -> UInt64 {
        var p = Data()
        let tt = table.data(using: .utf8) ?? Data()
        let ii = index.data(using: .utf8) ?? Data()
        p.append(VarInt.encode(UInt64(tt.count))); p.append(tt)
        p.append(VarInt.encode(UInt64(ii.count))); p.append(ii)
        p.append(VarInt.encode(UInt64(keyBytes.count))); p.append(keyBytes)
        var pid = rid.pageId.bigEndian; var sid = rid.slotId.bigEndian
        p.append(Data(bytes: &pid, count: 8)); p.append(Data(bytes: &sid, count: 2))
        return try append(type: .deleteRid, payload: p, prevLSN: prevLSN)
    }
    // CLR
    public func appendCLRUndoInsert(tid: UInt64, table: String, rid: RID, nextUndoLSN: UInt64, prevLSN: UInt64 = 0) throws -> UInt64 {
        var p = Data([1]); p.append(VarInt.encode(tid))
        let t = table.data(using: .utf8) ?? Data(); p.append(VarInt.encode(UInt64(t.count))); p.append(t)
        var pid = rid.pageId.bigEndian; var sid = rid.slotId.bigEndian
        p.append(Data(bytes: &pid, count: 8)); p.append(Data(bytes: &sid, count: 2))
        var ol = nextUndoLSN.bigEndian; p.append(Data(bytes: &ol, count: 8))
        return try append(type: .clr, payload: p, prevLSN: prevLSN, pageId: rid.pageId)
    }
    public func appendCLRUndoDelete(tid: UInt64, table: String, row: Row, nextUndoLSN: UInt64, prevLSN: UInt64 = 0) throws -> UInt64 {
        var p = Data([2]); p.append(VarInt.encode(tid))
        let t = table.data(using: .utf8) ?? Data(); p.append(VarInt.encode(UInt64(t.count))); p.append(t)
        let bytes = try JSONEncoder().encode(row); p.append(VarInt.encode(UInt64(bytes.count))); p.append(bytes)
        var ol = nextUndoLSN.bigEndian; p.append(Data(bytes: &ol, count: 8))
        return try append(type: .clr, payload: p, prevLSN: prevLSN)
    }
    // WALProtocol
    public func append(record: Data) throws -> UInt64 { try append(type: .insertRow, payload: record) }
    public func flush(upTo lsn: UInt64) throws { 
        try flushPending()
    }
    /// Truncates the WAL file and rewrites the header.
    public func truncate() throws {
        try fh.truncate(atOffset: 0)
        try ensureHeader()
        try sync()
    }
    
    /// Thread-safe access to flushed LSN
    public var flushedLSN: UInt64 {
        flushedLSNLock.lock()
        defer { flushedLSNLock.unlock() }
        return _flushedLSN
    }

    private func sync() throws {
        try IOHints.synchronize(handle: fh, full: fullFSyncEnabled)
    }

    // MARK: - Metrics API
    public func recentFlushMetrics() -> (lastBatch: Int, lastSyncNs: UInt64, flushes: Int, totalBatch: Int, totalSyncNs: UInt64) {
        return (lastFlushBatchSize, lastFlushSyncNs, totalFlushes, totalFlushedRecords, totalSyncNs)
    }
}
