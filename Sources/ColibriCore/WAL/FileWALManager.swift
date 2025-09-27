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

// MARK: - Helpers for safe big-endian conversions

private extension FixedWidthInteger {
    var bigEndianData: Data {
        var value = self.bigEndian
        return Data(bytes: &value, count: MemoryLayout<Self>.size)
    }
}

private extension Data {
    func readUInt32BE(at offset: Int) -> UInt32 {
        precondition(offset + MemoryLayout<UInt32>.size <= count, "readUInt32BE out of bounds")
        return withUnsafeBytes { rawPtr -> UInt32 in
            var temp: UInt32 = 0
            memcpy(&temp, rawPtr.baseAddress!.advanced(by: offset), MemoryLayout<UInt32>.size)
            return UInt32(bigEndian: temp)
        }
    }
    func readUInt64BE(at offset: Int) -> UInt64 {
        precondition(offset + MemoryLayout<UInt64>.size <= count, "readUInt64BE out of bounds")
        return withUnsafeBytes { rawPtr -> UInt64 in
            var temp: UInt64 = 0
            memcpy(&temp, rawPtr.baseAddress!.advanced(by: offset), MemoryLayout<UInt64>.size)
            return UInt64(bigEndian: temp)
        }
    }
    func readUInt16BE(at offset: Int) -> UInt16 {
        precondition(offset + MemoryLayout<UInt16>.size <= count, "readUInt16BE out of bounds")
        return withUnsafeBytes { rawPtr -> UInt16 in
            var temp: UInt16 = 0
            memcpy(&temp, rawPtr.baseAddress!.advanced(by: offset), MemoryLayout<UInt16>.size)
            return UInt16(bigEndian: temp)
        }
    }
}

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
    private static let writeQueueSpecificKey = DispatchSpecificKey<Void>()
    
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
    private let groupCommitOptimizer: GroupCommitOptimizer
    
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
        
        // Initialize group commit optimizer
        let optimizerPolicy: GroupCommitPolicy
        switch durabilityMode {
        case .always:
            optimizerPolicy = .fixed(threshold: 1, timeoutMs: 0)
        case .grouped:
            optimizerPolicy = .adaptive(minThreshold: max(1, groupCommitThreshold / 2), 
                                      maxThreshold: groupCommitThreshold * 2, 
                                      baseTimeoutMs: UInt32(groupCommitTimeoutMs))
        case .relaxed:
            optimizerPolicy = .priority(criticalThreshold: 1, 
                                      normalThreshold: groupCommitThreshold * 3, 
                                      timeoutMs: UInt32(groupCommitTimeoutMs * 2))
        }
        self.groupCommitOptimizer = GroupCommitOptimizer(policy: optimizerPolicy, compressionAlgorithm: compressionAlgorithm)
        
        // Initialize file
        self.fileURL = URL(fileURLWithPath: path)
        let fileManager = FileManager.default
        if !fileManager.fileExists(atPath: path) {
            fileManager.createFile(atPath: path, contents: nil)
        }
        self.fileHandle = try FileHandle(forUpdating: fileURL)
        
        // Initialize queues
        self.writeQueue = DispatchQueue(label: "wal.write.\(dbId)", qos: .userInitiated)
        self.writeQueue.setSpecific(key: Self.writeQueueSpecificKey, value: ())
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
                
                // Check if we should flush using optimizer
                let oldestAge: TimeInterval
                if let firstRecord = pendingRecords.first {
                    // Calculate age based on LSN timing (approximate)
                    oldestAge = Double(recordWithLSN.lsn - firstRecord.lsn) * 0.001  // Rough estimation
                } else {
                    oldestAge = 0
                }
                let highestPriority = pendingRecords.map { $0.groupCommitPriority }.max() ?? .normal
                let shouldFlush = groupCommitOptimizer.shouldFlush(
                    pendingCount: pendingRecords.count,
                    oldestRecordAge: oldestAge,
                    highestPriority: highestPriority
                )
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
    
    /// Get optimization metrics from the group commit optimizer
    public var optimizationMetrics: GroupCommitMetrics {
        return groupCommitOptimizer.currentMetrics
    }
    
    // MARK: - Lifecycle
    
    public func close() throws {
        stopGroupCommitTimer()
        
        let flushAndClose = {
            try self.flushPendingRecords()
            try self.fileHandle.close()
        }
        
        if DispatchQueue.getSpecific(key: Self.writeQueueSpecificKey) != nil {
            try flushAndClose()
        } else {
            try writeQueue.sync(execute: flushAndClose)
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
        let magic = headerData.readUInt32BE(at: 0)
        guard magic == Self.walMagic else {
            throw WALError.corruptedHeader("Invalid magic number")
        }
        
        // Validate version
        let version = headerData.readUInt16BE(at: 4)
        guard version == Self.walVersion else {
            throw WALError.incompatibleVersion("Unsupported WAL version: \(version)")
        }
        
        // Validate database ID
        let fileDbId = headerData.readUInt32BE(at: 6)
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
        
        // Optimize batch using group commit optimizer
        let optimizedBatch = groupCommitOptimizer.optimizeBatch(recordsToFlush)
        
        // Write optimized batch
        let uncompressedSize = try writeOptimizedBatch(optimizedBatch)
        
        // Sync to disk
        try fileHandle.synchronize()
        
        // Update flushed LSN
        if let lastRecord = optimizedBatch.records.last {
            lsnLock.lock()
            _flushedLSN = max(_flushedLSN, lastRecord.lsn)
            lsnLock.unlock()
        }
        
        let latency = Date().timeIntervalSince(startTime)
        let compressionRatio = uncompressedSize > 0 ? Double(optimizedBatch.estimatedSize) / Double(uncompressedSize) : 1.0
        
        // Record performance for optimization
        groupCommitOptimizer.recordBatchPerformance(
            batchSize: optimizedBatch.records.count,
            latency: latency,
            compressionRatio: compressionRatio
        )
        
        updateMetrics(operation: .flush, latency: latency, batchSize: optimizedBatch.records.count)
    }
    
    private func writeOptimizedBatch(_ batch: GroupCommitBatch) throws -> Int {
        var totalUncompressedSize = 0
        
        // Write records in optimized order
        for record in batch.records {
            totalUncompressedSize += try writeRecordToFile(record)
        }
        
        return totalUncompressedSize
    }
    
    @discardableResult
    private func writeRecordToFile(_ record: WALRecord) throws -> Int {
        // Serialize record
        let encoder = JSONEncoder()
        var payload = try encoder.encode(record)
        let originalSize = payload.count
        
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
        recordData.append(record.lsn.bigEndianData)
        
        // Database ID
        recordData.append(record.dbId.bigEndianData)
        
        // Page ID (optional)
        recordData.append((record.pageId ?? 0).bigEndianData)
        
        // Payload length
        recordData.append(UInt32(payload.count).bigEndianData)
        
        // Payload
        recordData.append(payload)
        
        // CRC32 of the entire record
        let crc = CRC32.compute(recordData)
        var crcBE = crc.bigEndian
        
        // Write CRC first, then record
        try fileHandle.write(contentsOf: Data(bytes: &crcBE, count: 4))
        try fileHandle.write(contentsOf: recordData)
        
        return originalSize
    }
    
    private func readAllRecords(from startLSN: UInt64) throws -> [WALRecord] {
        try fileHandle.seek(toOffset: UInt64(Self.headerSize))
        var records: [WALRecord] = []
        
        while true {
            // Try to read CRC
            guard let crcData = try fileHandle.read(upToCount: 4),
                  crcData.count == 4 else { break }

        let expectedCRC = crcData.readUInt32BE(at: 0)
            
            // Read record header (25 bytes: type(1) + lsn(8) + dbId(4) + pageId(8) + length(4))
            guard let headerData = try fileHandle.read(upToCount: 25),
                  headerData.count == 25 else { break }
            
            let typeByte = headerData[0]
            let compressionFlag = (typeByte & 0x80) != 0
            let recordType = typeByte & 0x7F
            
            let lsn = headerData.readUInt64BE(at: 1)
            let recordDbId = headerData.readUInt32BE(at: 9)
            let pageId = headerData.readUInt64BE(at: 13)
            let payloadLength = headerData.readUInt32BE(at: 21)
            
            // Read payload
            guard let payloadData = try fileHandle.read(upToCount: Int(payloadLength)),
                  payloadData.count == Int(payloadLength) else { break }
            
            // Verify CRC
        var recordData = Data()
        recordData.append(headerData)
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
        
        // Use dynamic timeout from optimizer
        let currentTimeout = groupCommitOptimizer.currentParameters.timeoutMs
        timer.schedule(deadline: .now() + .milliseconds(Int(currentTimeout)), repeating: .milliseconds(Int(currentTimeout)))
        
        timer.setEventHandler { [weak self] in
            try? self?.flushPendingRecords()
            
            // Restart timer with updated timeout from optimizer
            self?.startGroupCommitTimer()
        }
        
        timer.resume()
        groupCommitTimer = timer
    }
    
    private func stopGroupCommitTimer() {
        groupCommitTimer?.cancel()
        groupCommitTimer = nil
    }
    
    private func updateMetrics(operation: WALOperation, latency: TimeInterval, batchSize: Int) {
        metricsQueue.async { @Sendable [weak self] in
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
