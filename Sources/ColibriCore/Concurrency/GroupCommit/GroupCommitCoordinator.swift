//
//  GroupCommitCoordinator.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-10-17.
//
// ColibrDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Group commit orchestrator batching multiple transaction commits into a single fsync.

import Foundation
import Dispatch

/// Group commit coordinator that batches multiple transaction commits into a single WAL flush.
/// This can provide 5-10x performance improvement for high-throughput commit workloads.
public final class GroupCommitCoordinator: @unchecked Sendable {
    
    // MARK: - Configuration
    
    /// Configuration for group commit behavior
    public struct Configuration {
        /// Maximum number of transactions to batch before forcing a flush
        public var maxBatchSize: Int
        
        /// Maximum time to wait before forcing a flush (milliseconds)
        public var maxWaitTimeMs: Double
        
        /// Minimum number of transactions required to trigger immediate flush
        public var minBatchSize: Int
        
        /// Whether group commit is enabled
        public var enabled: Bool
        
        public init(
            maxBatchSize: Int = 64,
            maxWaitTimeMs: Double = 2.0,
            minBatchSize: Int = 4,
            enabled: Bool = true
        ) {
            self.maxBatchSize = maxBatchSize
            self.maxWaitTimeMs = maxWaitTimeMs
            self.minBatchSize = minBatchSize
            self.enabled = enabled
        }
    }
    
    // MARK: - Types
    
    /// A pending commit request waiting to be flushed
    private struct CommitRequest {
        let tid: UInt64
        let targetLSN: UInt64
        let completion: (Result<Void, Error>) -> Void
        let timestamp: DispatchTime
    }
    
    // MARK: - State
    
    private var configuration: Configuration
    private var pendingCommits: [CommitRequest] = []
    private let lock = NSLock()
    private let condition = NSCondition()
    
    // Background flusher thread
    private var flusherThread: Thread?
    private var shouldStop = false
    
    // Metrics
    private var totalCommits: UInt64 = 0
    private var totalBatches: UInt64 = 0
    private var totalWaitTimeNs: UInt64 = 0
    private var largestBatch: Int = 0
    
    // Callback for actual flush operation
    private let flushCallback: (UInt64) throws -> Void
    
    // MARK: - Initialization
    
    /// Creates a new group commit coordinator
    /// - Parameters:
    ///   - configuration: Group commit configuration
    ///   - flushCallback: Callback to perform actual WAL flush to given LSN
    public init(configuration: Configuration = Configuration(), flushCallback: @escaping (UInt64) throws -> Void) {
        self.configuration = configuration
        self.flushCallback = flushCallback
        
        if configuration.enabled {
            startFlusher()
        }
    }
    
    deinit {
        stop()
    }
    
    // MARK: - Public API
    
    /// Updates the configuration (thread-safe)
    public func updateConfiguration(_ newConfig: Configuration) {
        lock.lock()
        let wasEnabled = configuration.enabled
        configuration = newConfig
        lock.unlock()
        
        if newConfig.enabled && !wasEnabled {
            startFlusher()
        } else if !newConfig.enabled && wasEnabled {
            stop()
        }
    }
    
    /// Submits a transaction commit to the group commit queue
    /// - Parameters:
    ///   - tid: Transaction ID
    ///   - targetLSN: LSN that must be flushed
    ///   - completion: Completion handler called when flush completes
    public func submitCommit(tid: UInt64, targetLSN: UInt64, completion: @escaping (Result<Void, Error>) -> Void) {
        guard configuration.enabled else {
            // If group commit disabled, flush immediately
            do {
                try flushCallback(targetLSN)
                completion(.success(()))
            } catch {
                completion(.failure(error))
            }
            return
        }
        
        let request = CommitRequest(
            tid: tid,
            targetLSN: targetLSN,
            completion: completion,
            timestamp: DispatchTime.now()
        )
        
        lock.lock()
        pendingCommits.append(request)
        let pendingCount = pendingCommits.count
        lock.unlock()
        
        // Wake up flusher if we've reached min batch size
        if pendingCount >= configuration.minBatchSize {
            condition.lock()
            condition.signal()
            condition.unlock()
        }
    }
    
    /// Synchronously commits a transaction (waits for group flush)
    /// - Parameters:
    ///   - tid: Transaction ID
    ///   - targetLSN: LSN that must be flushed
    /// - Throws: Any error from flush operation
    public func commitSync(tid: UInt64, targetLSN: UInt64) throws {
        let semaphore = DispatchSemaphore(value: 0)
        var result: Result<Void, Error>?
        
        submitCommit(tid: tid, targetLSN: targetLSN) { res in
            result = res
            semaphore.signal()
        }
        
        semaphore.wait()
        
        switch result! {
        case .success:
            return
        case .failure(let error):
            throw error
        }
    }
    
    /// Forces an immediate flush of all pending commits
    public func flushNow() {
        condition.lock()
        condition.signal()
        condition.unlock()
    }
    
    /// Stops the group commit coordinator and flushes pending commits
    public func stop() {
        lock.lock()
        shouldStop = true
        lock.unlock()
        
        condition.lock()
        condition.signal()
        condition.unlock()
        
        // Wait for flusher thread to finish
        if let thread = flusherThread, !thread.isCancelled {
            while !thread.isFinished {
                Thread.sleep(forTimeInterval: 0.001)
            }
        }
        flusherThread = nil
    }
    
    /// Gets current metrics
    public func getMetrics() -> TransactionGroupCommitMetrics {
        lock.lock()
        defer { lock.unlock() }
        
        let avgBatchSize = totalBatches > 0 ? Double(totalCommits) / Double(totalBatches) : 0
        let avgWaitTimeUs = totalCommits > 0 ? Double(totalWaitTimeNs) / Double(totalCommits) / 1000.0 : 0
        
        return TransactionGroupCommitMetrics(
            totalCommits: totalCommits,
            totalBatches: totalBatches,
            averageBatchSize: avgBatchSize,
            largestBatch: largestBatch,
            averageWaitTimeUs: avgWaitTimeUs,
            pendingCommits: pendingCommits.count
        )
    }
    
    /// Resets metrics
    public func resetMetrics() {
        lock.lock()
        defer { lock.unlock() }
        
        totalCommits = 0
        totalBatches = 0
        totalWaitTimeNs = 0
        largestBatch = 0
    }
    
    // MARK: - Private Implementation
    
    private func startFlusher() {
        guard flusherThread == nil else { return }
        
        shouldStop = false
        let thread = Thread { [weak self] in
            self?.flusherLoop()
        }
        thread.name = "GroupCommitFlusher"
        thread.qualityOfService = .userInitiated
        flusherThread = thread
        thread.start()
    }
    
    private func flusherLoop() {
        while true {
            lock.lock()
            if shouldStop {
                lock.unlock()
                break
            }
            lock.unlock()
            
            // Wait for signal or timeout
            condition.lock()
            let timeoutDate = Date(timeIntervalSinceNow: configuration.maxWaitTimeMs / 1000.0)
            condition.wait(until: timeoutDate)
            condition.unlock()
            
            // Check if we should process commits
            lock.lock()
            let shouldFlush = !pendingCommits.isEmpty
            lock.unlock()
            
            if shouldFlush {
                processCommits()
            }
        }
        
        // Final flush on shutdown
        processCommits()
    }
    
    private func processCommits() {
        lock.lock()
        
        guard !pendingCommits.isEmpty else {
            lock.unlock()
            return
        }
        
        // Take up to maxBatchSize commits
        let batchSize = min(pendingCommits.count, configuration.maxBatchSize)
        let batch = Array(pendingCommits.prefix(batchSize))
        pendingCommits.removeFirst(batchSize)
        
        lock.unlock()
        
        // Find max LSN to flush
        let maxLSN = batch.map { $0.targetLSN }.max() ?? 0
        
        // Calculate wait times
        let flushStart = DispatchTime.now()
        var waitTimeSum: UInt64 = 0
        for request in batch {
            let waitTime = flushStart.uptimeNanoseconds - request.timestamp.uptimeNanoseconds
            waitTimeSum += waitTime
        }
        
        // Perform the flush
        do {
            try flushCallback(maxLSN)
            
            // Notify all commits in the batch
            for request in batch {
                request.completion(.success(()))
            }
            
            // Update metrics
            lock.lock()
            totalCommits += UInt64(batch.count)
            totalBatches += 1
            totalWaitTimeNs += waitTimeSum
            largestBatch = max(largestBatch, batch.count)
            lock.unlock()
            
        } catch {
            // Notify all commits of failure
            for request in batch {
                request.completion(.failure(error))
            }
        }
    }
}

// MARK: - Metrics

/// Metrics for transaction group commit performance
public struct TransactionGroupCommitMetrics {
    /// Total number of commits processed
    public let totalCommits: UInt64
    
    /// Total number of flush batches executed
    public let totalBatches: UInt64
    
    /// Average number of commits per batch
    public let averageBatchSize: Double
    
    /// Largest batch size seen
    public let largestBatch: Int
    
    /// Average wait time per commit (microseconds)
    public let averageWaitTimeUs: Double
    
    /// Number of commits currently waiting
    public let pendingCommits: Int
    
    public init(
        totalCommits: UInt64,
        totalBatches: UInt64,
        averageBatchSize: Double,
        largestBatch: Int,
        averageWaitTimeUs: Double,
        pendingCommits: Int
    ) {
        self.totalCommits = totalCommits
        self.totalBatches = totalBatches
        self.averageBatchSize = averageBatchSize
        self.largestBatch = largestBatch
        self.averageWaitTimeUs = averageWaitTimeUs
        self.pendingCommits = pendingCommits
    }
    
    /// Calculates the effectiveness of group commit (reduction in sync operations)
    public var syncReduction: Double {
        guard totalCommits > 0 else { return 0 }
        return 1.0 - (Double(totalBatches) / Double(totalCommits))
    }
    
    /// Estimated performance multiplier from group commit
    public var performanceMultiplier: Double {
        guard totalBatches > 0 else { return 1.0 }
        return averageBatchSize
    }
}

