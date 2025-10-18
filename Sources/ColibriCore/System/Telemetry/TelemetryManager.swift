//
//  TelemetryManager.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-01-27.
//
// ColibrDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Comprehensive telemetry and monitoring system for ColibrDB.

import Foundation
import os.log

/// Comprehensive telemetry manager for ColibrDB
public final class TelemetryManager {
    private let logger = Logger(subsystem: "com.colibridb.telemetry", category: "manager")
    
    // Configuration
    public let config: TelemetryConfig
    
    // State
    private var isCollecting = false
    private var collectionTimer: Timer?
    
    // 🚀 FIX #21: Metrics collection
    private var metrics: TelemetryMetrics
    private let metricsLock = NSLock()
    
    public init(config: TelemetryConfig = TelemetryConfig()) {
        self.config = config
        self.metrics = TelemetryMetrics()
        logger.info("TelemetryManager initialized")
    }
    
    /// Starts telemetry collection
    public func startCollection() {
        guard !isCollecting else { return }
        
        isCollecting = true
        logger.info("Starting telemetry collection")
        
        // Start collection timer
        collectionTimer = Timer.scheduledTimer(withTimeInterval: config.collectionInterval, repeats: true) { @Sendable [weak self] _ in
            self?.collectData()
        }
    }
    
    /// Stops telemetry collection
    public func stopCollection() {
        guard isCollecting else { return }
        
        isCollecting = false
        collectionTimer?.invalidate()
        collectionTimer = nil
        
        logger.info("Stopped telemetry collection")
    }
    
    /// Collects telemetry data
    /// 🚀 FIX #21: Real implementation
    private func collectData() {
        metricsLock.lock()
        defer { metricsLock.unlock() }
        
        // Update metrics
        metrics.collectionCount += 1
        metrics.lastCollectionTime = Date()
        
        // Sample system metrics
        if config.collectSystemMetrics {
            metrics.memoryUsageMB = ProcessInfo.processInfo.physicalMemory / (1024 * 1024)
        }
        
        logger.debug("Collected telemetry data: \(metrics.collectionCount) collections")
    }
    
    /// Exports telemetry data in Prometheus format
    /// 🚀 FIX #21: Prometheus export implementation
    public func exportData() -> Data? {
        metricsLock.lock()
        let currentMetrics = metrics
        metricsLock.unlock()
        
        let prometheusText = """
        # HELP colibridb_queries_total Total number of queries executed
        # TYPE colibridb_queries_total counter
        colibridb_queries_total \(currentMetrics.queryCount)
        
        # HELP colibridb_transactions_total Total number of transactions
        # TYPE colibridb_transactions_total counter
        colibridb_transactions_total \(currentMetrics.transactionCount)
        
        # HELP colibridb_cache_hits_total Total cache hits
        # TYPE colibridb_cache_hits_total counter
        colibridb_cache_hits_total \(currentMetrics.cacheHits)
        
        # HELP colibridb_cache_misses_total Total cache misses
        # TYPE colibridb_cache_misses_total counter
        colibridb_cache_misses_total \(currentMetrics.cacheMisses)
        
        # HELP colibridb_memory_usage_mb Current memory usage in MB
        # TYPE colibridb_memory_usage_mb gauge
        colibridb_memory_usage_mb \(currentMetrics.memoryUsageMB)
        
        # HELP colibridb_active_transactions Current active transactions
        # TYPE colibridb_active_transactions gauge
        colibridb_active_transactions \(currentMetrics.activeTransactions)
        
        # HELP colibridb_uptime_seconds Database uptime in seconds
        # TYPE colibridb_uptime_seconds counter
        colibridb_uptime_seconds \(Date().timeIntervalSince(currentMetrics.startTime))
        """
        
        logger.info("Exported telemetry data in Prometheus format")
        return prometheusText.data(using: .utf8)
    }
    
    /// Record a query execution
    /// 🚀 FIX #21: Public API for metrics recording
    public func recordQuery() {
        metricsLock.lock()
        defer { metricsLock.unlock() }
        metrics.queryCount += 1
    }
    
    /// Record a transaction
    public func recordTransaction() {
        metricsLock.lock()
        defer { metricsLock.unlock() }
        metrics.transactionCount += 1
    }
    
    /// Record cache hit
    public func recordCacheHit() {
        metricsLock.lock()
        defer { metricsLock.unlock() }
        metrics.cacheHits += 1
    }
    
    /// Record cache miss
    public func recordCacheMiss() {
        metricsLock.lock()
        defer { metricsLock.unlock() }
        metrics.cacheMisses += 1
    }
    
    /// Update active transactions count
    public func setActiveTransactions(_ count: Int) {
        metricsLock.lock()
        defer { metricsLock.unlock() }
        metrics.activeTransactions = count
    }
    
    /// Get current metrics snapshot
    public func getCurrentMetrics() -> TelemetryMetrics {
        metricsLock.lock()
        defer { metricsLock.unlock() }
        return metrics
    }
}

/// 🚀 FIX #21: Telemetry metrics structure
public struct TelemetryMetrics {
    public var queryCount: UInt64 = 0
    public var transactionCount: UInt64 = 0
    public var cacheHits: UInt64 = 0
    public var cacheMisses: UInt64 = 0
    public var memoryUsageMB: UInt64 = 0
    public var activeTransactions: Int = 0
    public var collectionCount: UInt64 = 0
    public var lastCollectionTime: Date?
    public let startTime: Date = Date()
    
    public var cacheHitRate: Double {
        let total = cacheHits + cacheMisses
        return total > 0 ? Double(cacheHits) / Double(total) : 0.0
    }
}

/// Telemetry configuration
public struct TelemetryConfig {
    public let collectionInterval: TimeInterval
    public let enabled: Bool
    public let collectSystemMetrics: Bool
    
    public init(
        collectionInterval: TimeInterval = 1.0, 
        enabled: Bool = true,
        collectSystemMetrics: Bool = true
    ) {
        self.collectionInterval = collectionInterval
        self.enabled = enabled
        self.collectSystemMetrics = collectSystemMetrics
    }
}