//
//  PerformanceMonitor.swift
//  ColibrìDB Performance Monitor
//
//  Implements: Performance metrics collection
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//

import Foundation

/// Performance metrics
public struct PerformanceMetrics: Codable, Sendable {
    public var queryLatency: TimeInterval
    public var transactionThroughput: Double
    public var cacheHitRate: Double
    public var diskIOLatency: TimeInterval
    public var memoryUsage: Int64
    
    public init(queryLatency: TimeInterval = 0, transactionThroughput: Double = 0, cacheHitRate: Double = 0, diskIOLatency: TimeInterval = 0, memoryUsage: Int64 = 0) {
        self.queryLatency = queryLatency
        self.transactionThroughput = transactionThroughput
        self.cacheHitRate = cacheHitRate
        self.diskIOLatency = diskIOLatency
        self.memoryUsage = memoryUsage
    }
}

/// Performance monitor protocol
public protocol PerformanceMonitor: Sendable {
    func recordQueryLatency(_ latency: TimeInterval) async
    func recordTransaction(_ duration: TimeInterval) async
    func recordCacheHit(_ hit: Bool) async
    func recordDiskIO(_ latency: TimeInterval) async
    func getMetrics() async -> PerformanceMetrics
}

/// Default performance monitor implementation
public actor DefaultPerformanceMonitor: PerformanceMonitor {
    private var metrics: PerformanceMetrics = PerformanceMetrics()
    private var queryCount: Int = 0
    private var transactionCount: Int = 0
    private var cacheHits: Int = 0
    private var cacheMisses: Int = 0
    private var totalQueryLatency: TimeInterval = 0
    private var totalTransactionTime: TimeInterval = 0
    private var totalDiskIOLatency: TimeInterval = 0
    private var diskIOCount: Int = 0
    
    public init() {}
    
    public func recordQueryLatency(_ latency: TimeInterval) async {
        queryCount += 1
        totalQueryLatency += latency
        metrics.queryLatency = totalQueryLatency / Double(queryCount)
    }
    
    public func recordTransaction(_ duration: TimeInterval) async {
        transactionCount += 1
        totalTransactionTime += duration
        metrics.transactionThroughput = Double(transactionCount) / totalTransactionTime
    }
    
    public func recordCacheHit(_ hit: Bool) async {
        if hit {
            cacheHits += 1
        } else {
            cacheMisses += 1
        }
        let total = cacheHits + cacheMisses
        if total > 0 {
            metrics.cacheHitRate = Double(cacheHits) / Double(total)
        }
    }
    
    public func recordDiskIO(_ latency: TimeInterval) async {
        diskIOCount += 1
        totalDiskIOLatency += latency
        metrics.diskIOLatency = totalDiskIOLatency / Double(diskIOCount)
    }
    
    public func getMetrics() async -> PerformanceMetrics {
        return metrics
    }
}

