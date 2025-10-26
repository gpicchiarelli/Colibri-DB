//
//  GroupCommit.swift
//  ColibrìDB Group Commit Implementation
//
//  Based on: spec/WAL.tla
//  Implements: Group commit for WAL records with configurable flush policy
//  Author: ColibrìDB Team
//  Date: 2025-10-26
//
//  Key Properties:
//  - Batch multiple WAL records for efficient I/O
//  - Configurable flush intervals (time and size)
//  - F_FULLFSYNC on macOS for guaranteed durability
//  - Thread-safe group commit operations
//

import Foundation

/// Group Commit Configuration
/// Corresponds to TLA+: GroupCommitConfig
public struct GroupCommitConfig: Sendable {
    /// Maximum time to wait before flushing (milliseconds)
    public let maxWaitMs: UInt64
    
    /// Maximum batch size before forcing flush (bytes)
    public let maxBatchBytes: UInt64
    
    /// Whether to use F_FULLFSYNC for durability
    public let useFullSync: Bool
    
    /// Maximum number of records to batch
    public let maxBatchRecords: UInt32
    
    public init(
        maxWaitMs: UInt64 = 10,        // 10ms default
        maxBatchBytes: UInt64 = 64 * 1024,  // 64KB default
        useFullSync: Bool = true,      // Use F_FULLFSYNC on macOS
        maxBatchRecords: UInt32 = 1000 // 1000 records default
    ) {
        self.maxWaitMs = maxWaitMs
        self.maxBatchBytes = maxBatchBytes
        self.useFullSync = useFullSync
        self.maxBatchRecords = maxBatchRecords
    }
}

/// Group Commit Manager
/// Manages batching and flushing of WAL records
/// Corresponds to TLA+: GroupCommitManager
public final class GroupCommitManager: @unchecked Sendable {
    
    // MARK: - Thread Safety
    
    private let lock = NSLock()
    
    // MARK: - Configuration
    
    private let config: GroupCommitConfig
    
    // MARK: - State Variables (TLA+ vars)
    
    /// Pending records waiting for flush
    /// TLA+: pendingRecords \in Seq(WALRecord)
    private var pendingRecords: [WALRecordWithChecksum] = []
    
    /// Current batch size in bytes
    /// TLA+: currentBatchSize \in Nat
    private var currentBatchSize: UInt64 = 0
    
    /// Last flush timestamp
    /// TLA+: lastFlushTime \in Time
    private var lastFlushTime: UInt64 = 0
    
    /// Flush callback function
    private let flushCallback: ([WALRecordWithChecksum]) throws -> Void
    
    /// Background flush timer
    private var flushTimer: Timer?
    
    // MARK: - Initialization
    
    public init(config: GroupCommitConfig, flushCallback: @escaping ([WALRecordWithChecksum]) throws -> Void) {
        self.config = config
        self.flushCallback = flushCallback
        self.lastFlushTime = UInt64(Date().timeIntervalSince1970 * 1000)
        
        // Start background flush timer
        startFlushTimer()
    }
    
    deinit {
        stopFlushTimer()
        // Flush any remaining records
        try? flushPendingRecords()
    }
    
    // MARK: - Group Commit Operations
    
    /// Add a WAL record to the pending batch
    /// TLA+ Action: AddToBatch
    /// - Parameter record: WAL record to add
    /// - Throws: Error if batch operations fail
    public func addRecord(_ record: WALRecordWithChecksum) throws {
        lock.lock()
        defer { lock.unlock() }
        
        pendingRecords.append(record)
        currentBatchSize += UInt64(record.totalSize)
        
        // Check if we should flush immediately
        if shouldFlushImmediately() {
            try flushPendingRecordsUnsafe()
        }
    }
    
    /// Force flush all pending records
    /// TLA+ Action: ForceFlush
    /// - Throws: Error if flush fails
    public func forceFlush() throws {
        lock.lock()
        defer { lock.unlock() }
        
        try flushPendingRecordsUnsafe()
    }
    
    /// Check if immediate flush is needed
    /// - Returns: true if flush should happen immediately
    private func shouldFlushImmediately() -> Bool {
        // Check batch size limit
        if currentBatchSize >= config.maxBatchBytes {
            return true
        }
        
        // Check record count limit
        if pendingRecords.count >= Int(config.maxBatchRecords) {
            return true
        }
        
        return false
    }
    
    /// Flush pending records (unsafe - must be called with lock held)
    /// TLA+ Action: FlushBatch
    /// - Throws: Error if flush fails
    private func flushPendingRecordsUnsafe() throws {
        guard !pendingRecords.isEmpty else {
            return
        }
        
        let recordsToFlush = pendingRecords
        pendingRecords.removeAll()
        currentBatchSize = 0
        lastFlushTime = UInt64(Date().timeIntervalSince1970 * 1000)
        
        // Release lock before calling flush callback
        lock.unlock()
        defer { lock.lock() }
        
        try flushCallback(recordsToFlush)
    }
    
    /// Flush pending records (safe - acquires lock)
    /// - Throws: Error if flush fails
    private func flushPendingRecords() throws {
        lock.lock()
        defer { lock.unlock() }
        
        try flushPendingRecordsUnsafe()
    }
    
    // MARK: - Background Flush Timer
    
    /// Start the background flush timer
    private func startFlushTimer() {
        let interval = TimeInterval(config.maxWaitMs) / 1000.0
        
        flushTimer = Timer.scheduledTimer(withTimeInterval: interval, repeats: true) { [weak self] _ in
            do {
                try self?.flushPendingRecords()
            } catch {
                // Log error but don't crash
                print("Group commit flush error: \(error)")
            }
        }
    }
    
    /// Stop the background flush timer
    private func stopFlushTimer() {
        flushTimer?.invalidate()
        flushTimer = nil
    }
    
    // MARK: - Statistics
    
    /// Get current batch statistics
    /// - Returns: Batch statistics
    public func getBatchStats() -> BatchStats {
        lock.lock()
        defer { lock.unlock() }
        
        return BatchStats(
            pendingRecords: pendingRecords.count,
            currentBatchSize: currentBatchSize,
            lastFlushTime: lastFlushTime
        )
    }
}

/// Batch Statistics
/// Corresponds to TLA+: BatchStats
public struct BatchStats: Sendable {
    /// Number of pending records
    public let pendingRecords: Int
    
    /// Current batch size in bytes
    public let currentBatchSize: UInt64
    
    /// Last flush timestamp
    public let lastFlushTime: UInt64
    
    public init(pendingRecords: Int, currentBatchSize: UInt64, lastFlushTime: UInt64) {
        self.pendingRecords = pendingRecords
        self.currentBatchSize = currentBatchSize
        self.lastFlushTime = lastFlushTime
    }
}

// MARK: - File System Durability

/// File system durability operations
/// Provides platform-specific durability guarantees
public struct FileSystemDurability {
    
    /// Ensure data is durably written to storage
    /// Uses F_FULLFSYNC on macOS for guaranteed durability
    /// - Parameter fileDescriptor: File descriptor to sync
    /// - Throws: Error if sync fails
    public static func ensureDurability(fileDescriptor: Int32) throws {
        #if os(macOS)
        // Use F_FULLFSYNC for maximum durability on macOS
        let result = fcntl(fileDescriptor, F_FULLFSYNC, 0)
        if result != 0 {
            throw DBError.ioError("Failed to sync file: \(String(cString: strerror(errno)))")
        }
        #else
        // Use fsync on other platforms
        let result = fsync(fileDescriptor)
        if result != 0 {
            throw DBError.ioError("Failed to sync file: \(String(cString: strerror(errno)))")
        }
        #endif
    }
    
    /// Ensure directory is durably written
    /// - Parameter directoryPath: Path to directory
    /// - Throws: Error if sync fails
    public static func ensureDirectoryDurability(directoryPath: String) throws {
        let fileDescriptor = open(directoryPath, O_RDONLY)
        guard fileDescriptor >= 0 else {
            throw DBError.ioError("Failed to open directory: \(String(cString: strerror(errno)))")
        }
        
        defer { close(fileDescriptor) }
        
        try ensureDurability(fileDescriptor: fileDescriptor)
    }
}

// MARK: - System Calls

#if os(macOS)
import Darwin

/// F_FULLFSYNC command for fcntl
private let F_FULLFSYNC: Int32 = 51
#endif