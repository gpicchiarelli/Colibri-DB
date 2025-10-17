//
//  PerformanceMonitor.swift
//  ColibrDB
//
//  Real-time performance monitoring
//

import Foundation

/// Performance metrics snapshot
public struct PerformanceSnapshot: Codable {
    public let timestamp: Date
    public let memoryUsageMB: Int
    public let cpuUsagePercent: Double
    public let activeTransactions: Int
    public let queuedOperations: Int
    public let bufferPoolHitRate: Double
    public let walSize: UInt64
    
    public init(
        timestamp: Date = Date(),
        memoryUsageMB: Int,
        cpuUsagePercent: Double,
        activeTransactions: Int,
        queuedOperations: Int,
        bufferPoolHitRate: Double,
        walSize: UInt64
    ) {
        self.timestamp = timestamp
        self.memoryUsageMB = memoryUsageMB
        self.cpuUsagePercent = cpuUsagePercent
        self.activeTransactions = activeTransactions
        self.queuedOperations = queuedOperations
        self.bufferPoolHitRate = bufferPoolHitRate
        self.walSize = walSize
    }
}

/// Real-time performance monitoring
public final class PerformanceMonitor {
    
    private var snapshots: [PerformanceSnapshot] = []
    private let maxSnapshots = 1000
    private let lock = NSLock()
    
    public init() {}
    
    /// Record a performance snapshot
    public func recordSnapshot(_ snapshot: PerformanceSnapshot) {
        lock.lock()
        defer { lock.unlock() }
        
        snapshots.append(snapshot)
        
        // Keep only recent snapshots
        if snapshots.count > maxSnapshots {
            snapshots.removeFirst(snapshots.count - maxSnapshots)
        }
    }
    
    /// Get recent snapshots
    public func getRecentSnapshots(count: Int = 10) -> [PerformanceSnapshot] {
        lock.lock()
        defer { lock.unlock() }
        
        let actualCount = min(count, snapshots.count)
        return Array(snapshots.suffix(actualCount))
    }
    
    /// Get all snapshots
    public func getAllSnapshots() -> [PerformanceSnapshot] {
        lock.lock()
        defer { lock.unlock() }
        
        return snapshots
    }
    
    /// Clear all snapshots
    public func clear() {
        lock.lock()
        defer { lock.unlock() }
        
        snapshots.removeAll()
    }
    
    /// Get aggregated statistics
    public func getStatistics() -> Statistics {
        lock.lock()
        let snaps = snapshots
        lock.unlock()
        
        guard !snaps.isEmpty else {
            return Statistics(
                avgMemoryMB: 0,
                avgCPUPercent: 0,
                avgTransactions: 0,
                avgBufferHitRate: 0,
                peakMemoryMB: 0,
                peakCPUPercent: 0,
                snapshotCount: 0
            )
        }
        
        let avgMemory = snaps.map { $0.memoryUsageMB }.reduce(0, +) / snaps.count
        let avgCPU = snaps.map { $0.cpuUsagePercent }.reduce(0, +) / Double(snaps.count)
        let avgTx = snaps.map { $0.activeTransactions }.reduce(0, +) / snaps.count
        let avgBuf = snaps.map { $0.bufferPoolHitRate }.reduce(0, +) / Double(snaps.count)
        
        let peakMemory = snaps.map { $0.memoryUsageMB }.max() ?? 0
        let peakCPU = snaps.map { $0.cpuUsagePercent }.max() ?? 0
        
        return Statistics(
            avgMemoryMB: avgMemory,
            avgCPUPercent: avgCPU,
            avgTransactions: avgTx,
            avgBufferHitRate: avgBuf,
            peakMemoryMB: peakMemory,
            peakCPUPercent: peakCPU,
            snapshotCount: snaps.count
        )
    }
    
    public struct Statistics {
        public let avgMemoryMB: Int
        public let avgCPUPercent: Double
        public let avgTransactions: Int
        public let avgBufferHitRate: Double
        public let peakMemoryMB: Int
        public let peakCPUPercent: Double
        public let snapshotCount: Int
    }
}

