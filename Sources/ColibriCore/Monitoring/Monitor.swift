//
//  Monitor.swift
//  ColibrìDB Monitoring and Observability
//
//  Based on: spec/Monitor.tla
//  Implements: System monitoring, metrics, health checks
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//

import Foundation


/// Health status
public enum HealthStatus: Sendable {
    case healthy
    case degraded
    case unhealthy
}

/// System health
public struct SystemHealth: Sendable {
    public let status: HealthStatus
    public let components: [String: HealthStatus]
    public let message: String?
    
    public init(status: HealthStatus, components: [String: HealthStatus] = [:], message: String? = nil) {
        self.status = status
        self.components = components
        self.message = message
    }
}

/// Monitor Manager
/// Corresponds to TLA+ module: Monitor.tla
public actor MonitorManager {
    // MARK: - State
    
    /// Metrics history
    private var metrics: [String: [Metric]] = [:]
    
    /// Current health status
    private var health: SystemHealth
    
    /// Alert thresholds
    private var thresholds: [String: Double] = [:]
    
    /// Maximum metrics to keep per name
    private let maxMetricsPerName = 1000
    
    // MARK: - Initialization
    
    public init() {
        self.health = SystemHealth(status: .healthy)
        
        // Set default thresholds
        self.thresholds = [
            "cpu_usage_percent": 80.0,
            "memory_usage_percent": 85.0,
            "disk_usage_percent": 90.0,
            "active_connections": 90.0,
            "transaction_latency_ms": 100.0
        ]
    }
    
    // MARK: - Metrics Collection
    
    /// Record a metric
    /// TLA+ Action: RecordMetric(name, value, type, labels)
    public func recordMetric(name: String, value: Double, type: MetricType, labels: [String: String] = [:]) {
        let metric = Metric(
            metricId: UUID().uuidString,
            name: name,
            value: value,
            unit: "count",
            timestamp: UInt64(Date().timeIntervalSince1970 * 1000),
            componentId: "monitor",
            metricType: type,
            labels: labels,
            isActive: true
        )
        
        metrics[name, default: []].append(metric)
        
        // Keep only recent metrics
        if metrics[name]!.count > maxMetricsPerName {
            metrics[name]!.removeFirst()
        }
        
        // Check thresholds
        checkThreshold(name: name, value: value)
    }
    
    /// Increment counter
    public func incrementCounter(name: String, by amount: Double = 1.0, labels: [String: String] = [:]) {
        let currentValue = metrics[name]?.last?.value ?? 0.0
        recordMetric(name: name, value: currentValue + amount, type: .counter, labels: labels)
    }
    
    /// Set gauge value
    public func setGauge(name: String, value: Double, labels: [String: String] = [:]) {
        recordMetric(name: name, value: value, type: .gauge, labels: labels)
    }
    
    /// Record histogram value
    public func recordHistogram(name: String, value: Double, labels: [String: String] = [:]) {
        recordMetric(name: name, value: value, type: .histogram, labels: labels)
    }
    
    // MARK: - Health Checks
    
    /// Update health status
    /// TLA+ Action: UpdateHealth(status, component)
    public func updateHealth(component: String, status: HealthStatus) {
        var components = health.components
        components[component] = status
        
        // Determine overall status
        let overallStatus: HealthStatus
        if components.values.contains(.unhealthy) {
            overallStatus = .unhealthy
        } else if components.values.contains(.degraded) {
            overallStatus = .degraded
        } else {
            overallStatus = .healthy
        }
        
        health = SystemHealth(status: overallStatus, components: components)
    }
    
    /// Get current health
    public func getHealth() -> SystemHealth {
        return health
    }
    
    /// Perform health check
    public func performHealthCheck(db: ColibrìDB) async -> SystemHealth {
        var components: [String: HealthStatus] = [:]
        
        // Check buffer pool
        let stats = await db.getStatistics()
        
        if stats.dirtyPages > stats.bufferPoolSize * 9 / 10 {
            components["buffer_pool"] = .degraded
        } else {
            components["buffer_pool"] = .healthy
        }
        
        // Check active transactions
        if stats.activeTransactions > 100 {
            components["transactions"] = .degraded
        } else {
            components["transactions"] = .healthy
        }
        
        // Determine overall status
        let overallStatus: HealthStatus
        if components.values.contains(.unhealthy) {
            overallStatus = .unhealthy
        } else if components.values.contains(.degraded) {
            overallStatus = .degraded
        } else {
            overallStatus = .healthy
        }
        
        let health = SystemHealth(status: overallStatus, components: components)
        self.health = health
        
        return health
    }
    
    // MARK: - Query Operations
    
    /// Get metric history
    public func getMetrics(name: String, since: Date? = nil) -> [Metric] {
        guard let metricHistory = metrics[name] else {
            return []
        }
        
        if let since = since {
            let sinceTimestamp = UInt64(since.timeIntervalSince1970 * 1000)
            return metricHistory.filter { $0.timestamp >= sinceTimestamp }
        }
        
        return metricHistory
    }
    
    /// Get all metric names
    public func getMetricNames() -> [String] {
        return Array(metrics.keys)
    }
    
    /// Get metric summary
    public func getMetricSummary(name: String, since: Date? = nil) -> MetricSummary? {
        let metricHistory = getMetrics(name: name, since: since)
        
        guard !metricHistory.isEmpty else {
            return nil
        }
        
        let values = metricHistory.map { $0.value }
        
        return MetricSummary(
            name: name,
            count: values.count,
            min: values.min() ?? 0.0,
            max: values.max() ?? 0.0,
            avg: values.reduce(0.0, +) / Double(values.count),
            last: values.last ?? 0.0
        )
    }
    
    // MARK: - Alerts
    
    /// Set alert threshold
    public func setThreshold(name: String, value: Double) {
        thresholds[name] = value
    }
    
    /// Check if metric exceeds threshold
    private func checkThreshold(name: String, value: Double) {
        guard let threshold = thresholds[name] else {
            return
        }
        
        if value > threshold {
            logInfo("⚠️  ALERT: Metric '\(name)' exceeded threshold: \(value) > \(threshold)")
            // In production, would send alert to monitoring system
        }
    }
}

// MARK: - Supporting Types

/// Metric summary
public struct MetricSummary: Sendable {
    public let name: String
    public let count: Int
    public let min: Double
    public let max: Double
    public let avg: Double
    public let last: Double
}

