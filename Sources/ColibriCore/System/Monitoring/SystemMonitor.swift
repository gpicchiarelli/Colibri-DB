//
//  SystemMonitor.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-09-26.
//
// ColibrDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: System monitoring and performance profiling.

import Foundation
import os.log

/// System monitor for performance tracking and analysis
public final class SystemMonitor: @unchecked Sendable {
    private let logger = Logger(subsystem: "com.colibridb.monitor", category: "system")
    private let database: Database
    
    // Monitoring components
    private let cpuMonitor: CPUMonitor
    private let memoryMonitor: MemoryMonitor
    private let ioMonitor: IOMonitor
    private let queryMonitor: QueryMonitor
    private let transactionMonitor: TransactionMonitor
    
    // Monitoring state
    private var isMonitoring = false
    private var monitoringInterval: TimeInterval = 1.0
    private var monitoringTimer: DispatchSourceTimer?
    private let monitoringQueue = DispatchQueue(label: "com.colibridb.monitor", qos: .utility)
    
    public init(database: Database) {
        self.database = database
        self.cpuMonitor = CPUMonitor()
        self.memoryMonitor = MemoryMonitor()
        self.ioMonitor = IOMonitor()
        self.queryMonitor = QueryMonitor()
        // Create a dummy TransactionManager for monitoring
        let dummyTxManager = TransactionManager(database: database)
        self.transactionMonitor = TransactionMonitor(transactionManager: dummyTxManager)
    }
    
    /// Starts system monitoring
    public func startMonitoring(interval: TimeInterval = 1.0) {
        guard !isMonitoring else { return }
        
        isMonitoring = true
        monitoringInterval = interval
        
        monitoringTimer = DispatchSource.makeTimerSource(queue: monitoringQueue)
        monitoringTimer?.schedule(deadline: .now(), repeating: .seconds(Int(interval)))
        monitoringTimer?.setEventHandler { [weak self] in
            self?.collectMetrics()
        }
        monitoringTimer?.resume()
        
        logger.info("System monitoring started with interval: \(interval)s")
    }
    
    /// Stops system monitoring
    public func stopMonitoring() {
        guard isMonitoring else { return }
        
        isMonitoring = false
        monitoringTimer?.cancel()
        monitoringTimer = nil
        
        logger.info("System monitoring stopped")
    }
    
    /// Collects system metrics
    private func collectMetrics() {
        let metrics = SystemMetrics(
            timestamp: Date(),
            cpu: cpuMonitor.getCurrentMetrics(),
            memory: memoryMonitor.getCurrentMetrics(),
            io: ioMonitor.getCurrentMetrics(),
            queries: queryMonitor.getCurrentMetrics(),
            transactions: TransactionMetrics(activeCount: 0, totalCount: 0, averageDuration: 0.0, committedCount: 0, abortedCount: 0)
        )
        
        // Log metrics if needed  
        logger.debug("System metrics collected: \(metrics.timestamp)")
    }
    
    /// Gets current system metrics
    public func getCurrentMetrics() -> SystemMetrics {
        return SystemMetrics(
            timestamp: Date(),
            cpu: cpuMonitor.getCurrentMetrics(),
            memory: memoryMonitor.getCurrentMetrics(),
            io: ioMonitor.getCurrentMetrics(),
            queries: queryMonitor.getCurrentMetrics(),
            transactions: TransactionMetrics(activeCount: 0, totalCount: 0, averageDuration: 0.0, committedCount: 0, abortedCount: 0)
        )
    }
    
    /// Gets system health status
    public func getHealthStatus() -> SystemHealthStatus {
        let metrics = getCurrentMetrics()
        
        var issues: [HealthIssue] = []
        
        // Check CPU usage
        if metrics.cpu.usage > 90.0 {
            issues.append(HealthIssue(type: .highCPU, severity: .warning, message: "High CPU usage: \(metrics.cpu.usage)%"))
        }
        
        // Check memory usage
        if metrics.memory.usage > 90.0 {
            issues.append(HealthIssue(type: .highMemory, severity: .warning, message: "High memory usage: \(metrics.memory.usage)%"))
        }
        
        // Check I/O performance
        if metrics.io.readLatency > 100.0 {
            issues.append(HealthIssue(type: .slowIO, severity: .warning, message: "Slow I/O read latency: \(metrics.io.readLatency)ms"))
        }
        
        // Check query performance
        if metrics.queries.averageExecutionTime > 5.0 {
            issues.append(HealthIssue(type: .slowQueries, severity: .warning, message: "Slow query execution: \(metrics.queries.averageExecutionTime)s"))
        }
        
        // Check transaction performance
        if metrics.transactions.activeCount > 100 {
            issues.append(HealthIssue(type: .highTransactionCount, severity: .warning, message: "High transaction count: \(metrics.transactions.activeCount)"))
        }
        
        let severity = issues.isEmpty ? HealthStatus.healthy : (issues.contains { $0.severity == .critical } ? HealthStatus.critical : HealthStatus.warning)
        
        return SystemHealthStatus(
            status: severity,
            issues: issues,
            timestamp: Date()
        )
    }
}

/// System metrics
public struct SystemMetrics {
    public let timestamp: Date
    public let cpu: CPUMetrics
    public let memory: MemoryMetrics
    public let io: IOMetrics
    public let queries: QueryMetrics
    public let transactions: TransactionMetrics
    
    public init(timestamp: Date, cpu: CPUMetrics, memory: MemoryMetrics, io: IOMetrics, queries: QueryMetrics, transactions: TransactionMetrics) {
        self.timestamp = timestamp
        self.cpu = cpu
        self.memory = memory
        self.io = io
        self.queries = queries
        self.transactions = transactions
    }
}

/// CPU metrics
public struct CPUMetrics {
    public let usage: Double
    public let userTime: Double
    public let systemTime: Double
    public let idleTime: Double
    public let coreCount: Int
    
    public init(usage: Double, userTime: Double, systemTime: Double, idleTime: Double, coreCount: Int) {
        self.usage = usage
        self.userTime = userTime
        self.systemTime = systemTime
        self.idleTime = idleTime
        self.coreCount = coreCount
    }
}

/// Memory metrics
public struct MemoryMetrics {
    public let usage: Double
    public let totalBytes: UInt64
    public let usedBytes: UInt64
    public let freeBytes: UInt64
    public let cachedBytes: UInt64
    
    public init(usage: Double, totalBytes: UInt64, usedBytes: UInt64, freeBytes: UInt64, cachedBytes: UInt64) {
        self.usage = usage
        self.totalBytes = totalBytes
        self.usedBytes = usedBytes
        self.freeBytes = freeBytes
        self.cachedBytes = cachedBytes
    }
}

/// I/O metrics
public struct IOMetrics {
    public let readLatency: Double
    public let writeLatency: Double
    public let readThroughput: Double
    public let writeThroughput: Double
    public let readCount: UInt64
    public let writeCount: UInt64
    
    public init(readLatency: Double, writeLatency: Double, readThroughput: Double, writeThroughput: Double, readCount: UInt64, writeCount: UInt64) {
        self.readLatency = readLatency
        self.writeLatency = writeLatency
        self.readThroughput = readThroughput
        self.writeThroughput = writeThroughput
        self.readCount = readCount
        self.writeCount = writeCount
    }
}

/// Query metrics
public struct QueryMetrics {
    public let activeQueries: Int
    public let totalQueries: UInt64
    public let averageExecutionTime: Double
    public let slowQueries: Int
    public let failedQueries: Int
    
    public init(activeQueries: Int, totalQueries: UInt64, averageExecutionTime: Double, slowQueries: Int, failedQueries: Int) {
        self.activeQueries = activeQueries
        self.totalQueries = totalQueries
        self.averageExecutionTime = averageExecutionTime
        self.slowQueries = slowQueries
        self.failedQueries = failedQueries
    }
}

/// Transaction metrics
public struct TransactionMetrics {
    public let activeCount: Int
    public let totalCount: UInt64
    public let averageDuration: Double
    public let committedCount: UInt64
    public let abortedCount: UInt64
    
    public init(activeCount: Int, totalCount: UInt64, averageDuration: Double, committedCount: UInt64, abortedCount: UInt64) {
        self.activeCount = activeCount
        self.totalCount = totalCount
        self.averageDuration = averageDuration
        self.committedCount = committedCount
        self.abortedCount = abortedCount
    }
}

/// System health status
public struct SystemHealthStatus {
    public let status: HealthStatus
    public let issues: [HealthIssue]
    public let timestamp: Date
    
    public init(status: HealthStatus, issues: [HealthIssue], timestamp: Date) {
        self.status = status
        self.issues = issues
        self.timestamp = timestamp
    }
}

/// Health status levels
public enum HealthStatus {
    case healthy
    case warning
    case critical
}

/// Health issue
public struct HealthIssue {
    public let type: HealthIssueType
    public let severity: HealthSeverity
    public let message: String
    
    public init(type: HealthIssueType, severity: HealthSeverity, message: String) {
        self.type = type
        self.severity = severity
        self.message = message
    }
}

/// Health issue types
public enum HealthIssueType {
    case highCPU
    case highMemory
    case slowIO
    case slowQueries
    case highTransactionCount
    case diskFull
    case networkIssue
    case databaseError
}

/// Health severity levels
public enum HealthSeverity {
    case info
    case warning
    case critical
}

/// CPU monitor
public final class CPUMonitor {
    private var lastCPUTime: (user: UInt64, system: UInt64, idle: UInt64) = (0, 0, 0)
    
    public init() {}
    
    public func getCurrentMetrics() -> CPUMetrics {
        let cpuInfo = getCPUInfo()
        let coreCount = ProcessInfo.processInfo.processorCount
        
        return CPUMetrics(
            usage: cpuInfo.usage,
            userTime: cpuInfo.user,
            systemTime: cpuInfo.system,
            idleTime: cpuInfo.idle,
            coreCount: coreCount
        )
    }
    
    private func getCPUInfo() -> (usage: Double, user: Double, system: Double, idle: Double) {
        // This would implement actual CPU monitoring
        // For now, return mock data
        return (usage: 25.0, user: 20.0, system: 5.0, idle: 75.0)
    }
}

/// Memory monitor
public final class MemoryMonitor {
    public init() {}
    
    public func getCurrentMetrics() -> MemoryMetrics {
        let memoryInfo = getMemoryInfo()
        
        return MemoryMetrics(
            usage: memoryInfo.usage,
            totalBytes: memoryInfo.total,
            usedBytes: memoryInfo.used,
            freeBytes: memoryInfo.free,
            cachedBytes: memoryInfo.cached
        )
    }
    
    private func getMemoryInfo() -> (usage: Double, total: UInt64, used: UInt64, free: UInt64, cached: UInt64) {
        // This would implement actual memory monitoring
        // For now, return mock data
        let total: UInt64 = 8 * 1024 * 1024 * 1024 // 8GB
        let used: UInt64 = 2 * 1024 * 1024 * 1024  // 2GB
        let free = total - used
        let cached: UInt64 = 512 * 1024 * 1024     // 512MB
        
        return (usage: Double(used) / Double(total) * 100, total: total, used: used, free: free, cached: cached)
    }
}

/// I/O monitor
public final class IOMonitor {
    private var readCount: UInt64 = 0
    private var writeCount: UInt64 = 0
    private var readBytes: UInt64 = 0
    private var writeBytes: UInt64 = 0
    
    public init() {}
    
    public func getCurrentMetrics() -> IOMetrics {
        // This would implement actual I/O monitoring
        // For now, return mock data
        return IOMetrics(
            readLatency: 5.0,
            writeLatency: 8.0,
            readThroughput: 100.0,
            writeThroughput: 80.0,
            readCount: readCount,
            writeCount: writeCount
        )
    }
    
    public func recordRead(bytes: Int) {
        readCount += 1
        readBytes += UInt64(bytes)
    }
    
    public func recordWrite(bytes: Int) {
        writeCount += 1
        writeBytes += UInt64(bytes)
    }
}

/// Query monitor
public final class QueryMonitor {
    private var activeQueries: Int = 0
    private var totalQueries: UInt64 = 0
    private var totalExecutionTime: Double = 0.0
    private var slowQueries: Int = 0
    private var failedQueries: Int = 0
    
    public init() {}
    
    public func getCurrentMetrics() -> QueryMetrics {
        let averageExecutionTime = totalQueries > 0 ? totalExecutionTime / Double(totalQueries) : 0.0
        
        return QueryMetrics(
            activeQueries: activeQueries,
            totalQueries: totalQueries,
            averageExecutionTime: averageExecutionTime,
            slowQueries: slowQueries,
            failedQueries: failedQueries
        )
    }
    
    public func recordQueryStart() {
        activeQueries += 1
    }
    
    public func recordQueryEnd(executionTime: Double, success: Bool) {
        activeQueries = max(0, activeQueries - 1)
        totalQueries += 1
        totalExecutionTime += executionTime
        
        if executionTime > 5.0 {
            slowQueries += 1
        }
        
        if !success {
            failedQueries += 1
        }
    }
}

/// Performance profiler
public final class PerformanceProfiler {
    private let logger = Logger(subsystem: "com.colibridb.profiler", category: "performance")
    private var profiles: [String: PerformanceProfile] = [:]
    private let profileLock = NSLock()
    
    public init() {}
    
    /// Starts profiling an operation
    public func startProfile(_ name: String) -> PerformanceProfile {
        let profile = PerformanceProfile(name: name, startTime: Date())
        
        profileLock.lock()
        defer { profileLock.unlock() }
        
        profiles[name] = profile
        return profile
    }
    
    /// Ends profiling an operation
    public func endProfile(_ name: String) -> PerformanceProfile? {
        profileLock.lock()
        defer { profileLock.unlock() }
        
        guard var profile = profiles[name] else { return nil }
        
        profile.endTime = Date()
        profile.duration = profile.endTime!.timeIntervalSince(profile.startTime)
        
        profiles[name] = profile
        
        logger.debug("Profile \(name): \(profile.duration)s")
        return profile
    }
    
    /// Gets all profiles
    public func getAllProfiles() -> [PerformanceProfile] {
        profileLock.lock()
        defer { profileLock.unlock() }
        return Array(profiles.values)
    }
    
    /// Clears all profiles
    public func clearProfiles() {
        profileLock.lock()
        defer { profileLock.unlock() }
        profiles.removeAll()
    }
}

/// Performance profile
public struct PerformanceProfile {
    public let name: String
    public let startTime: Date
    public var endTime: Date?
    public var duration: TimeInterval = 0.0
    public var metadata: [String: Any] = [:]
    
    public init(name: String, startTime: Date) {
        self.name = name
        self.startTime = startTime
    }
    
    public var isComplete: Bool {
        return endTime != nil
    }
}
