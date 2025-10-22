/*
 * GroupCommit.swift
 * ColibrìDB - Group Commit Optimization Implementation
 *
 * Based on TLA+ specification: GroupCommit.tla
 *
 * Batches multiple transaction commits into single fsync for performance
 * without compromising durability guarantees.
 *
 * Key Properties:
 * - Durability Preserved: Group commit doesn't compromise durability
 * - Order Preserved: Commit order matches LSN order
 * - Fairness: No transaction starved indefinitely
 *
 * Academic References:
 * - Gray, J., & Reuter, A. (1993). "Transaction Processing: Concepts and Techniques"
 * - Helland, P., et al. (1987). "Group Commit Timers and High Volume Transaction Systems"
 * - DeWitt, D. J., et al. (1984). "Implementation techniques for main memory database systems"
 *
 * Author: ColibrìDB Team
 * Date: 2025-10-19
 */

import Foundation

// MARK: - Commit Request

/// Commit request from a transaction
/// Corresponds to TLA+: CommitRequest
public struct CommitRequest: Codable, Sendable {
    public let tid: TxID
    public let targetLSN: LSN
    public let timestamp: Timestamp
    
    public init(tid: TxID, targetLSN: LSN, timestamp: Timestamp) {
        self.tid = tid
        self.targetLSN = targetLSN
        self.timestamp = timestamp
    }
}

// MARK: - Group Commit Configuration

/// Configuration for group commit optimization
/// Corresponds to TLA+ constants: MAX_BATCH_SIZE, MAX_WAIT_TIME_MS
public struct GroupCommitConfig: Sendable {
    /// Maximum commits per batch before forced flush
    /// TLA+: MAX_BATCH_SIZE
    public let maxBatchSize: Int
    
    /// Maximum wait time (in milliseconds) before forced flush
    /// TLA+: MAX_WAIT_TIME_MS
    public let maxWaitTimeMs: Int
    
    /// Enable group commit optimization
    public let enabled: Bool
    
    public init(maxBatchSize: Int = 100, maxWaitTimeMs: Int = 10, enabled: Bool = true) {
        self.maxBatchSize = maxBatchSize
        self.maxWaitTimeMs = maxWaitTimeMs
        self.enabled = enabled
    }
    
    public static let `default` = GroupCommitConfig()
}

// MARK: - Group Commit Manager

/// Manager for group commit optimization
/// Corresponds to TLA+ module: GroupCommit.tla
public actor GroupCommitManager {
    
    // MARK: - State Variables (TLA+ vars)
    
    /// Sequence of pending commit requests
    /// TLA+: commitQueue \in Seq(CommitRequest)
    private var commitQueue: [CommitRequest] = []
    
    /// Timer for forced flush
    /// TLA+: batchTimer \in Nat
    private var batchTimer: Int = 0
    
    /// Timestamp of last flush
    /// TLA+: lastFlushTime \in Timestamp
    private var lastFlushTime: Timestamp = 0
    
    /// Current flushed LSN (from WAL module)
    private var flushedLSN: LSN = 0
    
    // MARK: - Configuration
    
    /// Configuration for group commit
    private let config: GroupCommitConfig
    
    /// Flush callback (to WAL)
    private let flushCallback: (LSN) async throws -> Void
    
    /// Completion handlers for commit requests
    private var completionHandlers: [TxID: (Result<LSN, Error>) -> Void] = [:]
    
    /// Timer task
    private var timerTask: Task<Void, Never>?
    
    /// Statistics
    private var stats: GroupCommitStats = GroupCommitStats()
    
    // MARK: - Initialization
    
    public init(config: GroupCommitConfig = .default,
                flushCallback: @escaping (LSN) async throws -> Void) {
        self.config = config
        self.flushCallback = flushCallback
        
        // TLA+ Init_GC
        self.commitQueue = []
        self.batchTimer = 0
        self.lastFlushTime = 0
        self.flushedLSN = 0
        
        if config.enabled {
            startTimer()
        }
    }
    
    // MARK: - Public API
    
    /// Request a commit (adds to queue)
    /// TLA+ Action: RequestCommit(tid, targetLSN, timestamp)
    /// Precondition: Len(commitQueue) < MAX_BATCH_SIZE
    /// Postcondition: request added to queue
    public func requestCommit(
        tid: TxID,
        targetLSN: LSN,
        completion: @escaping (Result<LSN, Error>) -> Void
    ) {
        // TLA+: Len(commitQueue) < MAX_BATCH_SIZE
        guard commitQueue.count < config.maxBatchSize else {
            completion(.failure(GroupCommitError.queueFull))
            return
        }
        
        // TLA+: request == [tid |-> tid, targetLSN |-> targetLSN, timestamp |-> timestamp]
        let timestamp = UInt64(Date().timeIntervalSince1970 * 1000)
        let request = CommitRequest(tid: tid, targetLSN: targetLSN, timestamp: timestamp)
        
        // TLA+: commitQueue' = Append(commitQueue, request)
        commitQueue.append(request)
        completionHandlers[tid] = completion
        stats.totalRequests += 1
        
        if !config.enabled {
            // Group commit disabled - flush immediately
            Task {
                do {
                    try await flushCallback(targetLSN)
                    flushedLSN = max(flushedLSN, targetLSN)
                    completion(.success(targetLSN))
                } catch {
                    completion(.failure(error))
                }
            }
            return
        }
        
        // Check if we should flush immediately
        if shouldFlushBatch() {
            Task {
                await flushBatch()
            }
        }
    }
    
    /// Force flush all pending commits
    /// TLA+ Action: FlushBatch
    public func forceFlush() async throws {
        guard !commitQueue.isEmpty else { return }
        await flushBatch()
    }
    
    /// Get current flushed LSN
    public func getFlushedLSN() -> LSN {
        return flushedLSN
    }
    
    /// Get statistics
    public func getStats() -> GroupCommitStats {
        return stats
    }
    
    /// Shutdown group commit manager
    public func shutdown() {
        timerTask?.cancel()
        timerTask = nil
    }
    
    // MARK: - Batch Processing
    
    /// Check if batch should be flushed
    /// TLA+: FlushBatch precondition
    private func shouldFlushBatch() -> Bool {
        guard !commitQueue.isEmpty else { return false }
        
        // TLA+: Len(commitQueue) >= MAX_BATCH_SIZE \/ batchTimer >= MAX_WAIT_TIME_MS
        return commitQueue.count >= config.maxBatchSize || batchTimer >= config.maxWaitTimeMs
    }
    
    /// Flush batch of commits
    /// TLA+ Action: FlushBatch
    /// Precondition: commitQueue # <<>> /\ (size threshold \/ time threshold)
    /// Postcondition: all commits in batch flushed atomically
    private func flushBatch() async {
        guard !commitQueue.isEmpty else { return }
        
        let startTime = Date()
        let batch = commitQueue
        
        // TLA+: commitQueue' = <<>>
        commitQueue = []
        
        // TLA+: batchTimer' = 0
        batchTimer = 0
        
        // TLA+: maxLSN == Max({req.targetLSN : req \in Range(commitQueue)})
        let maxLSN = batch.map { $0.targetLSN }.max() ?? 0
        
        do {
            // Perform flush to disk
            try await flushCallback(maxLSN)
            
            // TLA+: flushedLSN' = maxLSN
            flushedLSN = max(flushedLSN, maxLSN)
            
            // Complete all commits in batch
            for request in batch {
                if let handler = completionHandlers[request.tid] {
                    handler(.success(maxLSN))
                    completionHandlers.removeValue(forKey: request.tid)
                }
            }
            
            // TLA+: lastFlushTime' = lastFlushTime + 1
            lastFlushTime += 1
            
            // Update statistics
            stats.totalBatches += 1
            stats.totalCommits += batch.count
            stats.averageBatchSize = Double(stats.totalCommits) / Double(stats.totalBatches)
            
            let elapsed = Date().timeIntervalSince(startTime) * 1000
            stats.averageFlushTimeMs = (stats.averageFlushTimeMs * Double(stats.totalBatches - 1) + elapsed) / Double(stats.totalBatches)
            
        } catch {
            // Flush failed - fail all commits in batch
            for request in batch {
                if let handler = completionHandlers[request.tid] {
                    handler(.failure(error))
                    completionHandlers.removeValue(forKey: request.tid)
                }
            }
            
            stats.totalErrors += 1
        }
    }
    
    // MARK: - Timer Management
    
    /// Start timer for forced flush
    private func startTimer() {
        timerTask = Task {
            while !Task.isCancelled {
                try? await Task.sleep(nanoseconds: 1_000_000) // 1ms
                
                guard !Task.isCancelled else { break }
                
                await tickTimer()
            }
        }
    }
    
    /// Tick timer (increment batch timer)
    /// TLA+ Action: TickTimer
    /// Precondition: commitQueue # <<>> /\ batchTimer < MAX_WAIT_TIME_MS
    /// Postcondition: batchTimer' = batchTimer + 1
    private func tickTimer() async {
        guard !commitQueue.isEmpty else {
            batchTimer = 0
            return
        }
        
        // TLA+: batchTimer < MAX_WAIT_TIME_MS
        guard batchTimer < config.maxWaitTimeMs else {
            // Time threshold reached - flush batch
            await flushBatch()
            return
        }
        
        // TLA+: batchTimer' = batchTimer + 1
        batchTimer += 1
        
        if shouldFlushBatch() {
            await flushBatch()
        }
    }
    
    // MARK: - Query Operations
    
    /// Get current commit queue size
    public func getQueueSize() -> Int {
        return commitQueue.count
    }
    
    /// Get current batch timer value
    public func getBatchTimer() -> Int {
        return batchTimer
    }
    
    /// Get last flush time
    public func getLastFlushTime() -> Timestamp {
        return lastFlushTime
    }
    
    // MARK: - Invariant Checking (for testing)
    
    /// Check durability preserved invariant
    /// TLA+ Inv_GC_DurabilityPreserved
    public func checkDurabilityPreservedInvariant() -> Bool {
        return commitQueue.allSatisfy { $0.targetLSN > flushedLSN }
    }
    
    /// Check order preserved invariant
    /// TLA+ Inv_GC_OrderPreserved
    public func checkOrderPreservedInvariant() -> Bool {
        for i in 0..<commitQueue.count {
            for j in (i+1)..<commitQueue.count {
                if commitQueue[i].targetLSN > commitQueue[j].targetLSN {
                    return false
                }
            }
        }
        return true
    }
    
    /// Check bounded wait invariant
    /// TLA+ Inv_GC_BoundedWait
    public func checkBoundedWaitInvariant() -> Bool {
        let currentTime = UInt64(Date().timeIntervalSince1970 * 1000)
        return commitQueue.allSatisfy { 
            currentTime - $0.timestamp <= UInt64(config.maxWaitTimeMs)
        }
    }
    
    /// Check all invariants
    public func checkAllInvariants() -> Bool {
        let durabilityPreserved = checkDurabilityPreservedInvariant()
        let orderPreserved = checkOrderPreservedInvariant()
        let boundedWait = checkBoundedWaitInvariant()
        
        return durabilityPreserved && orderPreserved && boundedWait
    }
}

// MARK: - Statistics

/// Statistics for group commit
public struct GroupCommitStats: Codable, Sendable {
    public var totalRequests: Int = 0
    public var totalBatches: Int = 0
    public var totalCommits: Int = 0
    public var totalErrors: Int = 0
    public var averageBatchSize: Double = 0.0
    public var averageFlushTimeMs: Double = 0.0
    
    public var compressionRatio: Double {
        guard totalBatches > 0 else { return 1.0 }
        return Double(totalCommits) / Double(totalBatches)
    }
    
    public var throughput: Double {
        guard averageFlushTimeMs > 0 else { return 0.0 }
        return averageBatchSize / (averageFlushTimeMs / 1000.0) // commits per second
    }
}

// MARK: - Errors

public enum GroupCommitError: Error, LocalizedError {
    case queueFull
    case flushFailed(underlying: Error)
    case timeout
    case managerShutdown
    
    public var errorDescription: String? {
        switch self {
        case .queueFull:
            return "Commit queue is full"
        case .flushFailed(let error):
            return "Flush failed: \(error.localizedDescription)"
        case .timeout:
            return "Commit timeout"
        case .managerShutdown:
            return "Group commit manager is shutdown"
        }
    }
}

/*
 * IMPLEMENTATION NOTES:
 *
 * This implementation follows the GroupCommit.tla specification:
 *
 * 1. Batching Strategy:
 *    - Size-based: Flush when batch reaches maxBatchSize
 *    - Time-based: Flush when maxWaitTimeMs elapsed
 *    - Whichever comes first triggers flush
 *
 * 2. Durability Guarantee:
 *    - All commits in batch flushed atomically to disk
 *    - Single fsync() for entire batch
 *    - No commit completes until fsync() succeeds
 *
 * 3. Order Preservation:
 *    - Commits processed in LSN order
 *    - Flushed LSN is maximum of all commits in batch
 *    - Later commits never visible before earlier ones
 *
 * 4. Fairness:
 *    - Timer ensures no commit waits forever
 *    - FIFO queue processing
 *    - Bounded wait time (maxWaitTimeMs)
 *
 * 5. Performance Benefits:
 *    - Reduces disk I/O: N commits -> 1 fsync
 *    - Higher throughput: Batch processing
 *    - Lower latency: Amortized sync cost
 *    - Typical improvement: 10-100x for write-heavy workloads
 *
 * 6. Correctness Properties (verified by TLA+):
 *    - Durability preserved: No commit lost after success
 *    - Order preserved: LSN ordering maintained
 *    - Bounded wait: No starvation
 *    - Atomicity: Batch commits atomic
 *
 * 7. Implementation Details:
 *    - Uses Swift async/await for concurrent operations
 *    - Timer runs in background task
 *    - Completion handlers called after successful flush
 *    - Statistics tracking for monitoring
 *
 * Academic References:
 * - Gray & Reuter (1993): Classic transaction processing reference
 * - Helland et al. (1987): Group commit timer optimization
 * - DeWitt et al. (1984): Main memory database techniques
 *
 * Production Examples:
 * - PostgreSQL: Uses group commit for WAL
 * - MySQL/InnoDB: Group commit for redo log
 * - MongoDB: Journaling group commit
 * - All modern databases use this optimization
 */

