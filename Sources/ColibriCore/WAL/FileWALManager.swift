//
//  FileWALManager.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-27.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Unified File-based WAL Manager implementing global Write-Ahead Logging

import Foundation
import Dispatch
#if os(macOS)
import Darwin
#endif

/// File-based implementation of the global WAL manager
public final class FileWALManager: WALManager {
    
    // MARK: - Constants and Configuration
    
    private static let walMagic: UInt32 = 0x57414C47  // "WALG" in hex
    private static let walVersion: UInt16 = 3
    private static let headerSize: Int = 32
    
    // MARK: - Properties
    
    public let dbId: UInt32
    public var durabilityMode: DurabilityMode {
        didSet { configureDurability() }
    }
    
    private let fileURL: URL
    private var fileHandle: FileHandle
    private let writeQueue: DispatchQueue
    private let metricsQueue: DispatchQueue
    
    // LSN management
    private var _nextLSN: UInt64 = 1
    private var _flushedLSN: UInt64 = 0
    private let lsnLock = NSLock()
    
    // Group commit
    private var pendingRecords: [WALRecord] = []
    private let groupCommitLock = NSLock()
    private var groupCommitTimer: DispatchSourceTimer?
    private let groupCommitThreshold: Int
    private let groupCommitTimeoutMs: Double
    
    // Compression
    private let compressionAlgorithm: CompressionAlgorithm
    private let compressionThreshold: Int = 1024  // Only compress records larger than this
    
    // Metrics
    private var _metrics: WALMetrics
    private var lastMetricsUpdate = Date()
    private var operationCounts = WALOperationCounts()
    
    // MARK: - Initialization
    
    public init(
        dbId: UInt32,
        path: String,
        durabilityMode: DurabilityMode = .grouped,
        groupCommitThreshold: Int = 8,
        groupCommitTimeoutMs: Double = 2.0,
        compressionAlgorithm: CompressionAlgorithm = .none
    ) throws {
        self.dbId = dbId
        self.durabilityMode = durabilityMode
        self.groupCommitThreshold = groupCommitThreshold
        self.groupCommitTimeoutMs = groupCommitTimeoutMs
        self.compressionAlgorithm = compressionAlgorithm
        
        // Initialize file
        self.fileURL = URL(fileURLWithPath: path)
        let fileManager = FileManager.default
        if !fileManager.fileExists(atPath: path) {
            fileManager.createFile(atPath: path, contents: nil)
        }
        self.fileHandle = try FileHandle(forUpdating: fileURL)
        
        // Initialize queues
        self.writeQueue = DispatchQueue(label: "wal.write.\(dbId)", qos: .userInitiated)
        self.metricsQueue = DispatchQueue(label: "wal.metrics.\(dbId)", qos: .utility)
        
        // Initialize metrics
        self._metrics = WALMetrics(
            appendsPerSecond: 0,
            bytesPerSecond: 0,
            fsyncsPerSecond: 0,
            averageBatchSize: 0,
            p95CommitLatencyMs: 0,
            currentFlushedLSN: 0,
            queueDepth: 0,
            compressionRatio: compressionAlgorithm == .none ? nil : 1.0
        )
        
        // Initialize WAL file
        try initializeWAL()
        
        // Configure durability
        configureDurability()
        
        // Start group commit timer if needed
        if durabilityMode == .grouped {
            startGroupCommitTimer()
        }
    }
    
    deinit {
        stopGroupCommitTimer()
        try? close()
    }
    
    // MARK: - WALWriter Implementation
    
    @discardableResult
    public func append(_ record: WALRecord) throws -> UInt64 {
        let startTime = Date()
        
        return try writeQueue.sync {
            // Assign LSN
            lsnLock.lock()
            let lsn = _nextLSN
            _nextLSN += 1
            lsnLock.unlock()
            
            var recordWithLSN = record
            recordWithLSN.lsn = lsn
            
            switch durabilityMode {
            case .always:
                // Immediate write and sync
                try writeRecordImmediately(recordWithLSN)
                updateMetrics(operation: .append, latency: Date().timeIntervalSince(startTime), batchSize: 1)
                
            case .grouped:
                // Add to group commit batch
                groupCommitLock.lock()
                pendingRecords.append(recordWithLSN)
                let shouldFlush = pendingRecords.count >= groupCommitThreshold
                groupCommitLock.unlock()
                
                if shouldFlush {
                    try flushPendingRecords()
                }
                updateMetrics(operation: .append, latency: Date().timeIntervalSince(startTime), batchSize: 0)
                
            case .relaxed:
                // Add to background queue
                groupCommitLock.lock()
                pendingRecords.append(recordWithLSN)
                groupCommitLock.unlock()
                updateMetrics(operation: .append, latency: Date().timeIntervalSince(startTime), batchSize: 0)
            }
            
            return lsn
        }
    }
    
    public func groupCommitSync() throws {
        try writeQueue.sync {
            try flushPendingRecords()
        }
    }
    
    public var flushedLSN: UInt64 {
        lsnLock.lock()
        defer { lsnLock.unlock() }
        return _flushedLSN
    }
    
    public func flush(upTo lsn: UInt64) throws {
        try writeQueue.sync {
            while flushedLSN < lsn {
                try flushPendingRecords()
                // If still not flushed enough, wait briefly and retry
                if flushedLSN < lsn {
                    Thread.sleep(forTimeInterval: 0.001)  // 1ms
                }
            }
        }
    }
    
    // MARK: - WALReader Implementation
    
    public func iterate(from lsn: UInt64) throws -> AnyIterator<WALRecord> {
        let records = try readAllRecords(from: lsn)
        var index = 0
        
        return AnyIterator {
            guard index < records.count else { return nil }
            let record = records[index]
            index += 1
            return record
        }
    }
    
    public func lastLSN() throws -> UInt64 {
        lsnLock.lock()
        defer { lsnLock.unlock() }
        return _nextLSN - 1
    }
    
    public func read(lsn: UInt64) throws -> WALRecord? {
        let allRecords = try readAllRecords(from: 1)
        return allRecords.first { $0.lsn == lsn }
    }
    
    // MARK: - WALCheckpointing Implementation
    
    @discardableResult
    public func writeCheckpoint(dpt: [UInt64: UInt64], att: [UInt64: UInt64]) throws -> UInt64 {
        let checkpointRecord = WALCheckpointRecord(
            dbId: dbId,
            dirtyPageTable: dpt,
            activeTransactionTable: att
        )
        return try append(checkpointRecord)
    }
    
    public func readLastCheckpoint() throws -> WALCheckpointRecord? {
        let allRecords = try readAllRecords(from: 1)
        
        // Find the most recent checkpoint record
        return allRecords
            .compactMap { $0 as? WALCheckpointRecord }
            .last
    }
    
    public func truncate(upTo lsn: UInt64) throws {
        try writeQueue.sync {
            // First ensure everything is flushed
            try flushPendingRecords()
            
            // Read all records after the truncation point
            let recordsToKeep = try readAllRecords(from: lsn + 1)
            
            // Truncate the file and rewrite header
            try fileHandle.truncate(atOffset: UInt64(Self.headerSize))
            try writeHeader()
            
            // Rewrite remaining records
            for record in recordsToKeep {
                try writeRecordToFile(record)
            }
            
            try fileHandle.synchronize()
        }
    }
    
    // MARK: - Metrics
    
    public var metrics: WALMetrics {
        metricsQueue.sync {
            updateMetricsIfNeeded()
            return _metrics
        }
    }
    
    // MARK: - Lifecycle
    
    public func close() throws {
        stopGroupCommitTimer()
        
        try writeQueue.sync {
            // Flush any pending records
            try flushPendingRecords()
            
            // Close file handle
            try fileHandle.close()
        }
    }
    
    // MARK: - Private Implementation
    
    private func initializeWAL() throws {
        let fileSize = try fileHandle.seekToEnd()
        
        if fileSize == 0 {
            // New file, write header
            try writeHeader()
        } else {
            // Existing file, validate header and recover LSN
            try validateHeader()
            try recoverState()
        }
    }
    
    private func writeHeader() throws {
        try fileHandle.seek(toOffset: 0)
        
        var header = Data(capacity: Self.headerSize)
        
        // Magic number
        var magic = Self.walMagic.bigEndian
        header.append(Data(bytes: &magic, count: 4))
        
        // Version
        var version = Self.walVersion.bigEndian
        header.append(Data(bytes: &version, count: 2))
        
        // Database ID
        var dbIdBE = dbId.bigEndian
        header.append(Data(bytes: &dbIdBE, count: 4))
        
        // Reserved space for future use
        header.append(Data(repeating: 0, count: Self.headerSize - header.count))
        
        try fileHandle.write(contentsOf: header)
    }
    
    private func validateHeader() throws {
        try fileHandle.seek(toOffset: 0)
        
        guard let headerData = try fileHandle.read(upToCount: Self.headerSize),
              headerData.count == Self.headerSize else {
            throw WALError.corruptedHeader("Invalid header size")
        }
        
        // Validate magic
        let magic = headerData.withUnsafeBytes { $0.load(fromByteOffset: 0, as: UInt32.self) }.bigEndian
        guard magic == Self.walMagic else {
            throw WALError.corruptedHeader("Invalid magic number")
        }
        
        // Validate version
        let version = headerData.withUnsafeBytes { $0.load(fromByteOffset: 4, as: UInt16.self) }.bigEndian
        guard version == Self.walVersion else {
            throw WALError.incompatibleVersion("Unsupported WAL version: \(version)")
        }
        
        // Validate database ID
        let fileDbId = headerData.withUnsafeBytes { $0.load(fromByteOffset: 6, as: UInt32.self) }.bigEndian
        guard fileDbId == dbId else {
            throw WALError.mismatchedDatabase("Database ID mismatch: file=\(fileDbId), expected=\(dbId)")
        }
    }
    
    private func recoverState() throws {
        let allRecords = try readAllRecords(from: 1)
        
        if let lastRecord = allRecords.last {
            lsnLock.lock()
            _nextLSN = lastRecord.lsn + 1
            _flushedLSN = lastRecord.lsn  // Assume all records in file are flushed
            lsnLock.unlock()
        }
    }
    
    private func writeRecordImmediately(_ record: WALRecord) throws {
        try writeRecordToFile(record)
        try fileHandle.synchronize()
        
        lsnLock.lock()
        _flushedLSN = max(_flushedLSN, record.lsn)
        lsnLock.unlock()
    }
    
    private func flushPendingRecords() throws {
        groupCommitLock.lock()
        let recordsToFlush = pendingRecords
        pendingRecords.removeAll()
        groupCommitLock.unlock()
        
        guard !recordsToFlush.isEmpty else { return }
        
        let startTime = Date()
        
        // Write all records
        for record in recordsToFlush {
            try writeRecordToFile(record)
        }
        
        // Sync to disk
        try fileHandle.synchronize()
        
        // Update flushed LSN
        if let lastRecord = recordsToFlush.last {
            lsnLock.lock()
            _flushedLSN = max(_flushedLSN, lastRecord.lsn)
            lsnLock.unlock()
        }
        
        updateMetrics(operation: .flush, latency: Date().timeIntervalSince(startTime), batchSize: recordsToFlush.count)
    }
    
    private func writeRecordToFile(_ record: WALRecord) throws {
        // Serialize record
        let encoder = JSONEncoder()
        var payload = try encoder.encode(record)
        
        // Compress if beneficial
        var compressionFlag: UInt8 = 0
        if payload.count > compressionThreshold && compressionAlgorithm != .none {
            if let compressed = CompressionCodec.compress(payload, algorithm: compressionAlgorithm) {
                if compressed.count < payload.count {
                    payload = compressed
                    compressionFlag = 1
                }
            }
        }
        
        // Build record header
        var recordData = Data()
        
        // Record type (WALKind + compression flag)
        let typeByte = record.kind.rawValue | (compressionFlag << 7)
        recordData.append(typeByte)
        
        // LSN
        var lsnBE = record.lsn.bigEndian
        recordData.append(Data(bytes: &lsnBE, count: 8))
        
        // Database ID
        var dbIdBE = record.dbId.bigEndian
        recordData.append(Data(bytes: &dbIdBE, count: 4))
        
        // Page ID (optional)
        var pageIdBE = (record.pageId ?? 0).bigEndian
        recordData.append(Data(bytes: &pageIdBE, count: 8))
        
        // Payload length
        var payloadLenBE = UInt32(payload.count).bigEndian
        recordData.append(Data(bytes: &payloadLenBE, count: 4))
        
        // Payload
        recordData.append(payload)
        
        // CRC32 of the entire record
        let crc = CRC32.compute(recordData)
        var crcBE = crc.bigEndian
        
        // Write CRC first, then record
        try fileHandle.write(contentsOf: Data(bytes: &crcBE, count: 4))
        try fileHandle.write(contentsOf: recordData)
    }
    
    private func readAllRecords(from startLSN: UInt64) throws -> [WALRecord] {
        try fileHandle.seek(toOffset: UInt64(Self.headerSize))
        var records: [WALRecord] = []
        
        while true {
            // Try to read CRC
            guard let crcData = try fileHandle.read(upToCount: 4),
                  crcData.count == 4 else { break }
            
            let expectedCRC = crcData.withUnsafeBytes { $0.load(as: UInt32.self) }.bigEndian
            
            // Read record header (25 bytes: type(1) + lsn(8) + dbId(4) + pageId(8) + length(4))
            guard let headerData = try fileHandle.read(upToCount: 25),
                  headerData.count == 25 else { break }
            
            let typeByte = headerData[0]
            let compressionFlag = (typeByte & 0x80) != 0
            let recordType = typeByte & 0x7F
            
            let lsn = headerData.withUnsafeBytes { $0.load(fromByteOffset: 1, as: UInt64.self) }.bigEndian
            let recordDbId = headerData.withUnsafeBytes { $0.load(fromByteOffset: 9, as: UInt32.self) }.bigEndian
            let pageId = headerData.withUnsafeBytes { $0.load(fromByteOffset: 13, as: UInt64.self) }.bigEndian
            let payloadLength = headerData.withUnsafeBytes { $0.load(fromByteOffset: 21, as: UInt32.self) }.bigEndian
            
            // Read payload
            guard let payloadData = try fileHandle.read(upToCount: Int(payloadLength)),
                  payloadData.count == Int(payloadLength) else { break }
            
            // Verify CRC
            var recordData = headerData
            recordData.append(payloadData)
            let actualCRC = CRC32.compute(recordData)
            
            guard actualCRC == expectedCRC else {
                throw WALError.corruptedRecord("CRC mismatch at LSN \(lsn)")
            }
            
            // Skip records before start LSN or wrong database
            if lsn < startLSN || recordDbId != dbId {
                continue
            }
            
            // Decompress if needed
            var finalPayload = payloadData
            if compressionFlag {
                do {
                    finalPayload = try CompressionCodec.decompress(payloadData, algorithm: compressionAlgorithm, expectedSize: payloadData.count * 4)
                } catch {
                    throw WALError.corruptedRecord("Failed to decompress record at LSN \(lsn): \(error)")
                }
            }
            
            // Deserialize record
            let decoder = JSONDecoder()
            let record = try deserializeRecord(
                kind: WALKind(rawValue: recordType) ?? .begin,
                lsn: lsn,
                dbId: recordDbId,
                pageId: pageId == 0 ? nil : pageId,
                payload: finalPayload,
                decoder: decoder
            )
            
            records.append(record)
        }
        
        return records
    }
    
    private func deserializeRecord(kind: WALKind, lsn: UInt64, dbId: UInt32, pageId: UInt64?, payload: Data, decoder: JSONDecoder) throws -> WALRecord {
        switch kind {
        case .begin:
            return try decoder.decode(WALBeginRecord.self, from: payload)
        case .commit:
            return try decoder.decode(WALCommitRecord.self, from: payload)
        case .abort:
            return try decoder.decode(WALAbortRecord.self, from: payload)
        case .heapInsert:
            return try decoder.decode(WALHeapInsertRecord.self, from: payload)
        case .heapUpdate:
            return try decoder.decode(WALHeapUpdateRecord.self, from: payload)
        case .heapDelete:
            return try decoder.decode(WALHeapDeleteRecord.self, from: payload)
        case .indexInsert:
            return try decoder.decode(WALIndexInsertRecord.self, from: payload)
        case .indexDelete:
            return try decoder.decode(WALIndexDeleteRecord.self, from: payload)
        case .catalogCreate, .catalogDrop, .catalogUpdate:
            return try decoder.decode(WALCatalogRecord.self, from: payload)
        case .checkpoint:
            return try decoder.decode(WALCheckpointRecord.self, from: payload)
        case .clr:
            return try decoder.decode(WALCLRRecord.self, from: payload)
        }
    }
    
    private func configureDurability() {
        #if os(macOS)
        if durabilityMode == .always {
            _ = fcntl(fileHandle.fileDescriptor, F_FULLFSYNC)
        }
        #endif
    }
    
    private func startGroupCommitTimer() {
        guard durabilityMode == .grouped else { return }
        
        stopGroupCommitTimer()
        
        let timer = DispatchSource.makeTimerSource(queue: writeQueue)
        timer.schedule(deadline: .now() + .milliseconds(Int(groupCommitTimeoutMs)), repeating: .milliseconds(Int(groupCommitTimeoutMs)))
        
        timer.setEventHandler { [weak self] in
            try? self?.flushPendingRecords()
        }
        
        timer.resume()
        groupCommitTimer = timer
    }
    
    private func stopGroupCommitTimer() {
        groupCommitTimer?.cancel()
        groupCommitTimer = nil
    }
    
    private func updateMetrics(operation: WALOperation, latency: TimeInterval, batchSize: Int) {
        metricsQueue.async { [weak self] in
            guard let self = self else { return }
            
            switch operation {
            case .append:
                self.operationCounts.appends += 1
                self.operationCounts.totalAppendLatency += latency
            case .flush:
                self.operationCounts.flushes += 1
                self.operationCounts.totalFlushLatency += latency
                self.operationCounts.totalBatchSize += batchSize
            }
            
            self.updateMetricsIfNeeded()
        }
    }
    
    private func updateMetricsIfNeeded() {
        let now = Date()
        let timeSinceLastUpdate = now.timeIntervalSince(lastMetricsUpdate)
        
        guard timeSinceLastUpdate >= 1.0 else { return }  // Update every second
        
        let appendsPerSecond = Double(operationCounts.appends) / timeSinceLastUpdate
        let fsyncsPerSecond = Double(operationCounts.flushes) / timeSinceLastUpdate
        let avgBatchSize = operationCounts.flushes > 0 ? Double(operationCounts.totalBatchSize) / Double(operationCounts.flushes) : 0
        let avgCommitLatency = operationCounts.appends > 0 ? (operationCounts.totalAppendLatency / Double(operationCounts.appends)) * 1000 : 0
        
        _metrics = WALMetrics(
            appendsPerSecond: appendsPerSecond,
            bytesPerSecond: 0,  // TODO: Track bytes
            fsyncsPerSecond: fsyncsPerSecond,
            averageBatchSize: avgBatchSize,
            p95CommitLatencyMs: avgCommitLatency,  // Simplified to average for now
            currentFlushedLSN: flushedLSN,
            queueDepth: pendingRecords.count,
            compressionRatio: compressionAlgorithm == .none ? nil : 1.0
        )
        
        // Reset counters
        operationCounts = WALOperationCounts()
        lastMetricsUpdate = now
    }
}

// MARK: - Supporting Types

private enum WALOperation {
    case append, flush
}

private struct WALOperationCounts {
    var appends = 0
    var flushes = 0
    var totalBatchSize = 0
    var totalAppendLatency: TimeInterval = 0
    var totalFlushLatency: TimeInterval = 0
}

/// WAL-specific errors
public enum WALError: Error, LocalizedError {
    case corruptedHeader(String)
    case incompatibleVersion(String)
    case mismatchedDatabase(String)
    case corruptedRecord(String)
    case ioError(String)
    
    public var errorDescription: String? {
        switch self {
        case .corruptedHeader(let msg):
            return "WAL header corrupted: \(msg)"
        case .incompatibleVersion(let msg):
            return "WAL version incompatible: \(msg)"
        case .mismatchedDatabase(let msg):
            return "WAL database mismatch: \(msg)"
        case .corruptedRecord(let msg):
            return "WAL record corrupted: \(msg)"
        case .ioError(let msg):
            return "WAL I/O error: \(msg)"
        }
    }
}
