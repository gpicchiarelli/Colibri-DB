//
//  GroupCommitOptimizer.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-09-27.
//
// ColibrDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Advanced group commit optimization for Global WAL

import Foundation

/// Advanced group commit optimization policies
public enum GroupCommitPolicy {
    case fixed(threshold: Int, timeoutMs: UInt32)
    case adaptive(minThreshold: Int, maxThreshold: Int, baseTimeoutMs: UInt32)
    case priority(criticalThreshold: Int, normalThreshold: Int, timeoutMs: UInt32)
}

/// WAL record priority for group commit optimization
public enum WALRecordPriority: Int, Comparable {
    case background = 0     // Index maintenance, cleanup
    case normal = 1         // Regular DML operations
    case transaction = 2    // Transaction begin/commit/abort
    case critical = 3       // Checkpoint, emergency flush
    
    public static func < (lhs: WALRecordPriority, rhs: WALRecordPriority) -> Bool {
        return lhs.rawValue < rhs.rawValue
    }
}

/// Group commit batch with optimization metadata
public struct GroupCommitBatch {
    public let records: [WALRecord]
    public let priority: WALRecordPriority
    public let timestamp: Date
    public let estimatedSize: Int
    
    public init(records: [WALRecord], priority: WALRecordPriority, estimatedSize: Int) {
        self.records = records
        self.priority = priority
        self.timestamp = Date()
        self.estimatedSize = estimatedSize
    }
}

/// Performance metrics for group commit optimization
public struct GroupCommitMetrics {
    public var totalBatches: Int = 0
    public var totalRecords: Int = 0
    public var averageBatchSize: Double = 0.0
    public var averageLatency: TimeInterval = 0.0
    public var compressionRatio: Double = 0.0
    public var adaptiveAdjustments: Int = 0
    
    public var lastBatchSize: Int = 0
    public var lastLatency: TimeInterval = 0.0
    public var lastCompressionRatio: Double = 0.0
}

/// Advanced group commit optimizer
public class GroupCommitOptimizer {
    
    // MARK: - Configuration
    
    private let policy: GroupCommitPolicy
    private let compressionAlgorithm: CompressionAlgorithm
    private var metrics = GroupCommitMetrics()
    
    // MARK: - Dynamic State
    
    private var currentThreshold: Int
    private var currentTimeoutMs: UInt32
    private var performanceHistory: [(batchSize: Int, latency: TimeInterval)] = []
    private let maxHistorySize = 100
    
    // MARK: - Initialization
    
    public init(policy: GroupCommitPolicy, compressionAlgorithm: CompressionAlgorithm = .lzfse) {
        self.policy = policy
        self.compressionAlgorithm = compressionAlgorithm
        
        switch policy {
        case .fixed(let threshold, let timeoutMs):
            self.currentThreshold = threshold
            self.currentTimeoutMs = timeoutMs
            
        case .adaptive(let minThreshold, _, let baseTimeoutMs):
            self.currentThreshold = minThreshold
            self.currentTimeoutMs = baseTimeoutMs
            
        case .priority(_, let normalThreshold, let timeoutMs):
            self.currentThreshold = normalThreshold
            self.currentTimeoutMs = timeoutMs
        }
    }
    
    // MARK: - Optimization Logic
    
    /// Determines if a batch should be flushed based on policy
    public func shouldFlush(pendingCount: Int, oldestRecordAge: TimeInterval, highestPriority: WALRecordPriority) -> Bool {
        switch policy {
        case .fixed(let threshold, _):
            return pendingCount >= threshold
            
        case .adaptive(_, _, _):
            return pendingCount >= currentThreshold || shouldAdaptiveFlush(oldestRecordAge: oldestRecordAge)
            
        case .priority(let criticalThreshold, let normalThreshold, _):
            if highestPriority >= .critical {
                return pendingCount >= criticalThreshold
            } else {
                return pendingCount >= normalThreshold
            }
        }
    }
    
    /// Optimizes a batch before writing
    public func optimizeBatch(_ records: [WALRecord]) -> GroupCommitBatch {
        let priority = records.map { getRecordPriority($0) }.max() ?? .normal
        
        // Sort records by priority and LSN for optimal layout
        let sortedRecords = records.sorted { lhs, rhs in
            let lhsPriority = getRecordPriority(lhs)
            let rhsPriority = getRecordPriority(rhs)
            
            if lhsPriority != rhsPriority {
                return lhsPriority > rhsPriority
            }
            return lhs.lsn < rhs.lsn
        }
        
        let estimatedSize = estimateBatchSize(sortedRecords)
        return GroupCommitBatch(records: sortedRecords, priority: priority, estimatedSize: estimatedSize)
    }
    
    /// Updates metrics and adapts thresholds based on performance
    public func recordBatchPerformance(batchSize: Int, latency: TimeInterval, compressionRatio: Double) {
        // Update metrics
        metrics.totalBatches += 1
        metrics.totalRecords += batchSize
        metrics.averageBatchSize = Double(metrics.totalRecords) / Double(metrics.totalBatches)
        metrics.averageLatency = (metrics.averageLatency * Double(metrics.totalBatches - 1) + latency) / Double(metrics.totalBatches)
        metrics.compressionRatio = (metrics.compressionRatio * Double(metrics.totalBatches - 1) + compressionRatio) / Double(metrics.totalBatches)
        
        metrics.lastBatchSize = batchSize
        metrics.lastLatency = latency
        metrics.lastCompressionRatio = compressionRatio
        
        // Add to performance history
        performanceHistory.append((batchSize: batchSize, latency: latency))
        if performanceHistory.count > maxHistorySize {
            performanceHistory.removeFirst()
        }
        
        // Adaptive threshold adjustment
        if case .adaptive = policy {
            adaptThreshold()
        }
    }
    
    /// Current optimization metrics
    public var currentMetrics: GroupCommitMetrics {
        return metrics
    }
    
    /// Current threshold and timeout values
    public var currentParameters: (threshold: Int, timeoutMs: UInt32) {
        return (currentThreshold, currentTimeoutMs)
    }
    
    // MARK: - Private Implementation
    
    private func getRecordPriority(_ record: WALRecord) -> WALRecordPriority {
        switch record {
        case is WALCheckpointRecord:
            return .critical
        case is WALBeginRecord, is WALCommitRecord, is WALAbortRecord:
            return .transaction
        case is WALCLRRecord:
            return .normal
        case is WALIndexInsertRecord, is WALIndexDeleteRecord:
            return .background
        default:
            return .normal
        }
    }
    
    private func estimateBatchSize(_ records: [WALRecord]) -> Int {
        // Rough estimation: 100 bytes base + variable content
        return records.reduce(0) { total, record in
            let baseSize = 100
            let contentSize: Int
            
            switch record {
            case let heapRecord as WALHeapInsertRecord:
                contentSize = heapRecord.rowData.count
            case let heapRecord as WALHeapUpdateRecord:
                contentSize = heapRecord.oldRowData.count + heapRecord.newRowData.count
            case let heapRecord as WALHeapDeleteRecord:
                contentSize = heapRecord.rowData.count
            case let indexRecord as WALIndexInsertRecord:
                contentSize = indexRecord.keyBytes.count + 20  // +RID
            case let indexRecord as WALIndexDeleteRecord:
                contentSize = indexRecord.keyBytes.count + 20  // +RID
            default:
                contentSize = 50  // Small records
            }
            
            return total + baseSize + contentSize
        }
    }
    
    private func shouldAdaptiveFlush(oldestRecordAge: TimeInterval) -> Bool {
        let timeoutSeconds = Double(currentTimeoutMs) / 1000.0
        return oldestRecordAge >= timeoutSeconds
    }
    
    private func adaptThreshold() {
        guard case .adaptive(let minThreshold, let maxThreshold, let baseTimeoutMs) = policy,
              performanceHistory.count >= 10 else { return }
        
        // Calculate recent performance trend
        let recentHistory = Array(performanceHistory.suffix(10))
        let avgLatency = recentHistory.map { $0.latency }.reduce(0, +) / Double(recentHistory.count)
        let avgBatchSize = recentHistory.map { $0.batchSize }.reduce(0, +) / recentHistory.count
        
        // Target latency: 2-5ms for group commit
        let targetLatency: TimeInterval = 0.003  // 3ms
        
        let newThreshold: Int
        
        if avgLatency > targetLatency * 1.5 {
            // Too slow, reduce batch size
            newThreshold = max(minThreshold, currentThreshold - 2)
        } else if avgLatency < targetLatency * 0.7 && avgBatchSize >= currentThreshold {
            // Fast enough, can increase batch size
            newThreshold = min(maxThreshold, currentThreshold + 1)
        } else {
            newThreshold = currentThreshold
        }
        
        if newThreshold != currentThreshold {
            currentThreshold = newThreshold
            metrics.adaptiveAdjustments += 1
        }
        
        // Also adapt timeout based on performance
        let newTimeoutMs: UInt32
        if avgLatency > targetLatency {
            newTimeoutMs = max(1, currentTimeoutMs - 1)
        } else if avgLatency < targetLatency * 0.5 {
            newTimeoutMs = min(baseTimeoutMs * 2, currentTimeoutMs + 1)
        } else {
            newTimeoutMs = currentTimeoutMs
        }
        
        currentTimeoutMs = newTimeoutMs
    }
}

// MARK: - WALRecord Priority Extension

extension WALRecord {
    /// Get the priority of this WAL record for group commit optimization
    public var groupCommitPriority: WALRecordPriority {
        switch self {
        case is WALCheckpointRecord:
            return .critical
        case is WALBeginRecord, is WALCommitRecord, is WALAbortRecord:
            return .transaction
        case is WALCLRRecord:
            return .normal
        case is WALIndexInsertRecord, is WALIndexDeleteRecord:
            return .background
        default:
            return .normal
        }
    }
}
