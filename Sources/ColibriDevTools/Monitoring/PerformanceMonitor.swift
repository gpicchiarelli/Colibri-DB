//
//  PerformanceMonitor.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Real-time performance monitoring and profiling tools.

import Foundation
import ColibriCore
import os.log

/// Real-time performance monitoring for ColibrDB
public final class PerformanceMonitor: @unchecked Sendable {
    private let database: Database
    private let logger = Logger(subsystem: "com.colibridb.monitor", category: "performance")
    private var isMonitoring = false
    private var monitoringTimer: Timer?
    private var metrics: [PerformanceMetric] = []
    private let maxMetrics = 1000 // Keep last 1000 metrics
    
    public init(database: Database) {
        self.database = database
    }
    
    // MARK: - Monitoring Control
    
    /// Starts real-time performance monitoring
    public func startMonitoring(interval: TimeInterval = 1.0) {
        guard !isMonitoring else {
            logger.warning("Monitoring already started")
            return
        }
        
        isMonitoring = true
        logger.info("Starting performance monitoring with \(interval)s interval")
        
        monitoringTimer = Timer.scheduledTimer(withTimeInterval: interval, repeats: true) { [weak self] _ in
            self?.collectMetrics()
        }
    }
    
    /// Stops performance monitoring
    public func stopMonitoring() {
        guard isMonitoring else {
            logger.warning("Monitoring not started")
            return
        }
        
        isMonitoring = false
        monitoringTimer?.invalidate()
        monitoringTimer = nil
        logger.info("Performance monitoring stopped")
    }
    
    /// Collects current performance metrics
    private func collectMetrics() {
        let bufferStats = database.bufferPoolAggregateNumbers()
        _ = database.vacuumStats()
        
        let metric = PerformanceMetric(
            timestamp: Date(),
            bufferHits: bufferStats.hits,
            bufferMisses: bufferStats.misses,
            bufferHitRatio: Double(bufferStats.hits) / Double(bufferStats.hits + bufferStats.misses),
            bufferEvictions: UInt64(bufferStats.evictions),
            bufferPages: UInt64(bufferStats.pages),
            bufferCapacity: UInt64(bufferStats.capacity),
            bufferPinned: UInt64(bufferStats.pinned),
            bufferDirty: UInt64(bufferStats.dirty),
            vacuumRuns: UInt64(database.vacuumRuns),
            vacuumPagesCompacted: UInt64(database.vacuumTotalPagesCompacted),
            vacuumBytesReclaimed: UInt64(database.vacuumTotalBytesReclaimed),
            memoryUsage: getCurrentMemoryUsage()
        )
        
        metrics.append(metric)
        
        // Keep only last maxMetrics
        if metrics.count > maxMetrics {
            metrics.removeFirst(metrics.count - maxMetrics)
        }
        
        logger.debug("Collected performance metric: \(metric.bufferHitRatio * 100)% hit ratio")
    }
    
    // MARK: - Metrics Access
    
    /// Gets current performance metrics
    public func getCurrentMetrics() -> PerformanceMetric? {
        return metrics.last
    }
    
    /// Gets all collected metrics
    public func getAllMetrics() -> [PerformanceMetric] {
        return metrics
    }
    
    /// Gets metrics within a time range
    public func getMetrics(from startDate: Date, to endDate: Date) -> [PerformanceMetric] {
        return metrics.filter { $0.timestamp >= startDate && $0.timestamp <= endDate }
    }
    
    /// Gets performance summary
    public func getPerformanceSummary() -> PerformanceSummary {
        guard !metrics.isEmpty else {
            return PerformanceSummary(
                averageHitRatio: 0,
                peakHitRatio: 0,
                averageMemoryUsage: 0,
                peakMemoryUsage: 0,
                totalBufferHits: 0,
                totalBufferMisses: 0,
                totalEvictions: 0,
                monitoringDuration: 0,
                sampleCount: 0
            )
        }
        
        let hitRatios = metrics.map { $0.bufferHitRatio }
        let memoryUsages = metrics.map { $0.memoryUsage }
        
        let averageHitRatio = hitRatios.reduce(0, +) / Double(hitRatios.count)
        let peakHitRatio = hitRatios.max() ?? 0
        let averageMemoryUsage = memoryUsages.map { Double($0) }.reduce(0.0, +) / Double(memoryUsages.count)
        let peakMemoryUsage = Double(memoryUsages.max() ?? 0)
        
        let totalBufferHits = metrics.last?.bufferHits ?? 0
        let totalBufferMisses = metrics.last?.bufferMisses ?? 0
        let totalEvictions = metrics.last?.bufferEvictions ?? 0
        
        let monitoringDuration = metrics.last?.timestamp.timeIntervalSince(metrics.first?.timestamp ?? Date()) ?? 0
        
        return PerformanceSummary(
            averageHitRatio: averageHitRatio,
            peakHitRatio: peakHitRatio,
            averageMemoryUsage: averageMemoryUsage,
            peakMemoryUsage: peakMemoryUsage,
            totalBufferHits: totalBufferHits,
            totalBufferMisses: totalBufferMisses,
            totalEvictions: totalEvictions,
            monitoringDuration: monitoringDuration,
            sampleCount: metrics.count
        )
    }
    
    // MARK: - Memory Usage
    
    private func getCurrentMemoryUsage() -> UInt64 {
        var memoryInfo = mach_task_basic_info()
        var count = mach_msg_type_number_t(MemoryLayout<mach_task_basic_info>.size)/4
        
        let kerr: kern_return_t = withUnsafeMutablePointer(to: &memoryInfo) {
            $0.withMemoryRebound(to: integer_t.self, capacity: 1) {
                task_info(mach_task_self_,
                         task_flavor_t(MACH_TASK_BASIC_INFO),
                         $0,
                         &count)
            }
        }
        
        if kerr == KERN_SUCCESS {
            return memoryInfo.resident_size
        } else {
            logger.error("Failed to get memory info: \(kerr)")
            return 0
        }
    }
}

// MARK: - Data Structures

public struct PerformanceMetric {
    public let timestamp: Date
    public let bufferHits: UInt64
    public let bufferMisses: UInt64
    public let bufferHitRatio: Double
    public let bufferEvictions: UInt64
    public let bufferPages: UInt64
    public let bufferCapacity: UInt64
    public let bufferPinned: UInt64
    public let bufferDirty: UInt64
    public let vacuumRuns: UInt64
    public let vacuumPagesCompacted: UInt64
    public let vacuumBytesReclaimed: UInt64
    public let memoryUsage: UInt64
    
    public var memoryUsageMB: Double {
        return Double(memoryUsage) / 1024.0 / 1024.0
    }
}

public struct PerformanceSummary {
    public let averageHitRatio: Double
    public let peakHitRatio: Double
    public let averageMemoryUsage: Double
    public let peakMemoryUsage: Double
    public let totalBufferHits: UInt64
    public let totalBufferMisses: UInt64
    public let totalEvictions: UInt64
    public let monitoringDuration: TimeInterval
    public let sampleCount: Int
    
    public var averageHitRatioPercentage: Double {
        return averageHitRatio * 100
    }
    
    public var peakHitRatioPercentage: Double {
        return peakHitRatio * 100
    }
    
    public var averageMemoryUsageMB: Double {
        return averageMemoryUsage / 1024.0 / 1024.0
    }
    
    public var peakMemoryUsageMB: Double {
        return peakMemoryUsage / 1024.0 / 1024.0
    }
}

// MARK: - CPU Profiler

public class CPUProfiler {
    private let database: Database
    private let logger = Logger(subsystem: "com.colibridb.profiler", category: "cpu")
    private var isProfiling = false
    private var profileData: [CPUProfileData] = []
    
    public init(database: Database) {
        self.database = database
    }
    
    /// Starts CPU profiling
    public func startProfiling() {
        guard !isProfiling else {
            logger.warning("CPU profiling already started")
            return
        }
        
        isProfiling = true
        logger.info("Starting CPU profiling")
    }
    
    /// Stops CPU profiling
    public func stopProfiling() {
        guard isProfiling else {
            logger.warning("CPU profiling not started")
            return
        }
        
        isProfiling = false
        logger.info("CPU profiling stopped")
    }
    
    /// Profiles a specific operation
    public func profileOperation<T>(_ operation: () throws -> T, name: String) throws -> CPUProfileResult<T> {
        let startTime = CFAbsoluteTimeGetCurrent()
        let startCPU = getCurrentCPUUsage()
        
        let result: T
        do {
            result = try operation()
        } catch {
            let endTime = CFAbsoluteTimeGetCurrent()
            let endCPU = getCurrentCPUUsage()
            
            return CPUProfileResult(
                name: name,
                duration: endTime - startTime,
                cpuUsage: endCPU - startCPU,
                success: false,
                error: error,
                result: nil,
                timestamp: Date()
            )
        }
        
        let endTime = CFAbsoluteTimeGetCurrent()
        let endCPU = getCurrentCPUUsage()
        
        let profileData = CPUProfileData(
            name: name,
            duration: endTime - startTime,
            cpuUsage: endCPU - startCPU,
            timestamp: Date()
        )
        
        self.profileData.append(profileData)
        
        return CPUProfileResult(
            name: name,
            duration: endTime - startTime,
            cpuUsage: endCPU - startCPU,
            success: true,
            error: nil,
            result: result,
            timestamp: Date()
        )
    }
    
    /// Gets CPU usage statistics
    public func getCPUStats() -> CPUStats {
        let durations = profileData.map { $0.duration }
        let cpuUsages = profileData.map { $0.cpuUsage }
        
        let averageDuration = durations.reduce(0, +) / Double(durations.count)
        let peakDuration = durations.max() ?? 0
        let averageCPUUsage = cpuUsages.reduce(0, +) / Double(cpuUsages.count)
        let peakCPUUsage = cpuUsages.max() ?? 0
        
        return CPUStats(
            averageDuration: averageDuration,
            peakDuration: peakDuration,
            averageCPUUsage: averageCPUUsage,
            peakCPUUsage: peakCPUUsage,
            totalOperations: profileData.count,
            timestamp: Date()
        )
    }
    
    private func getCurrentCPUUsage() -> Double {
        var info = mach_task_basic_info()
        var count = mach_msg_type_number_t(MemoryLayout<mach_task_basic_info>.size)/4
        
        let kerr: kern_return_t = withUnsafeMutablePointer(to: &info) {
            $0.withMemoryRebound(to: integer_t.self, capacity: 1) {
                task_info(mach_task_self_,
                         task_flavor_t(MACH_TASK_BASIC_INFO),
                         $0,
                         &count)
            }
        }
        
        if kerr == KERN_SUCCESS {
            return Double(info.resident_size) / 1024.0 / 1024.0 // Convert to MB
        } else {
            return 0
        }
    }
}

public struct CPUProfileData {
    public let name: String
    public let duration: TimeInterval
    public let cpuUsage: Double
    public let timestamp: Date
}

public struct CPUProfileResult<T> {
    public let name: String
    public let duration: TimeInterval
    public let cpuUsage: Double
    public let success: Bool
    public let error: Error?
    public let result: T?
    public let timestamp: Date
}

public struct CPUStats {
    public let averageDuration: TimeInterval
    public let peakDuration: TimeInterval
    public let averageCPUUsage: Double
    public let peakCPUUsage: Double
    public let totalOperations: Int
    public let timestamp: Date
}
