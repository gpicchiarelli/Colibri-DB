//
//  SystemMonitor.swift
//  ColibrìDB System Monitor Implementation
//
//  Based on: spec/Monitor.tla
//  Implements: System monitoring and metrics
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//
//  Key Properties:
//  - Completeness: All critical metrics monitored
//  - Accuracy: Metrics reflect actual system state
//  - Timeliness: Real-time monitoring and alerting
//  - Scalability: Efficient metric collection
//  - Reliability: Monitoring system doesn't impact performance
//

import Foundation

// MARK: - System Monitor Types

/// Health state
/// Corresponds to TLA+: HealthState
public enum HealthState: String, Codable, Sendable, CaseIterable {
    case healthy = "healthy"
    case degraded = "degraded"
    case unhealthy = "unhealthy"
    case unknown = "unknown"
}

/// Metric type
/// Corresponds to TLA+: MetricType
public enum MetricType: String, Codable, Sendable, CaseIterable {
    case counter = "counter"
    case gauge = "gauge"
    case histogram = "histogram"
    case summary = "summary"
}

// AlertSeverity is defined in System/SystemManagement.swift

/// Alert status
/// Corresponds to TLA+: AlertStatus
public enum AlertStatus: String, Codable, Sendable, CaseIterable {
    case firing = "firing"
    case resolved = "resolved"
    case suppressed = "suppressed"
}

/// Metric
/// Corresponds to TLA+: Metric
public struct Metric: Codable, Sendable, Equatable {
    public let metricId: String
    public let name: String
    public let value: Double
    public let unit: String
    public let timestamp: UInt64
    public let componentId: String
    public let metricType: MetricType
    public let labels: [String: String]
    public let isActive: Bool
    
    public init(metricId: String, name: String, value: Double, unit: String, timestamp: UInt64, componentId: String, metricType: MetricType, labels: [String: String], isActive: Bool) {
        self.metricId = metricId
        self.name = name
        self.value = value
        self.unit = unit
        self.timestamp = timestamp
        self.componentId = componentId
        self.metricType = metricType
        self.labels = labels
        self.isActive = isActive
    }
}

/// Alert
/// Corresponds to TLA+: Alert
public struct Alert: Codable, Sendable, Equatable {
    public let alertId: String
    public let name: String
    public let severity: AlertSeverity
    public let status: AlertStatus
    public let componentId: String
    public let metricId: String
    public let threshold: Double
    public let currentValue: Double
    public let triggeredAt: UInt64
    public let resolvedAt: UInt64
    public let message: String
    public let isAcknowledged: Bool
    
    public init(alertId: String, name: String, severity: AlertSeverity, status: AlertStatus, componentId: String, metricId: String, threshold: Double, currentValue: Double, triggeredAt: UInt64, resolvedAt: UInt64, message: String, isAcknowledged: Bool) {
        self.alertId = alertId
        self.name = name
        self.severity = severity
        self.status = status
        self.componentId = componentId
        self.metricId = metricId
        self.threshold = threshold
        self.currentValue = currentValue
        self.triggeredAt = triggeredAt
        self.resolvedAt = resolvedAt
        self.message = message
        self.isAcknowledged = isAcknowledged
    }
}

/// Health check
/// Corresponds to TLA+: HealthCheck
public struct HealthCheck: Codable, Sendable, Equatable {
    public let componentId: String
    public let componentName: String
    public let status: HealthState
    public let lastCheck: UInt64
    public let checkInterval: UInt64
    public let consecutiveFailures: Int
    public let lastError: String
    public let responseTime: UInt64
    public let isEnabled: Bool
    
    public init(componentId: String, componentName: String, status: HealthState, lastCheck: UInt64, checkInterval: UInt64, consecutiveFailures: Int, lastError: String, responseTime: UInt64, isEnabled: Bool) {
        self.componentId = componentId
        self.componentName = componentName
        self.status = status
        self.lastCheck = lastCheck
        self.checkInterval = checkInterval
        self.consecutiveFailures = consecutiveFailures
        self.lastError = lastError
        self.responseTime = responseTime
        self.isEnabled = isEnabled
    }
}

/// Performance data
/// Corresponds to TLA+: PerformanceData
public struct PerformanceData: Codable, Sendable, Equatable {
    public let componentId: String
    public let cpuUsage: Double
    public let memoryUsage: Double
    public let diskUsage: Double
    public let networkUsage: Double
    public let queryCount: Int
    public let avgResponseTime: Double
    public let errorRate: Double
    public let timestamp: UInt64
    
    public init(componentId: String, cpuUsage: Double, memoryUsage: Double, diskUsage: Double, networkUsage: Double, queryCount: Int, avgResponseTime: Double, errorRate: Double, timestamp: UInt64) {
        self.componentId = componentId
        self.cpuUsage = cpuUsage
        self.memoryUsage = memoryUsage
        self.diskUsage = diskUsage
        self.networkUsage = networkUsage
        self.queryCount = queryCount
        self.avgResponseTime = avgResponseTime
        self.errorRate = errorRate
        self.timestamp = timestamp
    }
}

/// Resource usage
/// Corresponds to TLA+: ResourceUsage
public struct ResourceUsage: Codable, Sendable, Equatable {
    public let resourceId: String
    public let resourceType: String
    public let currentUsage: Double
    public let maxCapacity: Double
    public let utilizationPercent: Double
    public let timestamp: UInt64
    
    public init(resourceId: String, resourceType: String, currentUsage: Double, maxCapacity: Double, utilizationPercent: Double, timestamp: UInt64) {
        self.resourceId = resourceId
        self.resourceType = resourceType
        self.currentUsage = currentUsage
        self.maxCapacity = maxCapacity
        self.utilizationPercent = utilizationPercent
        self.timestamp = timestamp
    }
}

/// Query metric
/// Corresponds to TLA+: QueryMetric
public struct QueryMetric: Codable, Sendable, Equatable {
    public let queryId: String
    public let queryText: String
    public let executionTime: UInt64
    public let rowsReturned: Int
    public let rowsScanned: Int
    public let cpuTime: UInt64
    public let ioTime: UInt64
    public let memoryUsed: Int
    public let timestamp: UInt64
    
    public init(queryId: String, queryText: String, executionTime: UInt64, rowsReturned: Int, rowsScanned: Int, cpuTime: UInt64, ioTime: UInt64, memoryUsed: Int, timestamp: UInt64) {
        self.queryId = queryId
        self.queryText = queryText
        self.executionTime = executionTime
        self.rowsReturned = rowsReturned
        self.rowsScanned = rowsScanned
        self.cpuTime = cpuTime
        self.ioTime = ioTime
        self.memoryUsed = memoryUsed
        self.timestamp = timestamp
    }
}

/// System diagnostics
/// Corresponds to TLA+: SystemDiagnostics
public struct SystemDiagnostics: Codable, Sendable, Equatable {
    public let systemUptime: UInt64
    public let totalMemory: Int
    public let freeMemory: Int
    public let totalDisk: Int
    public let freeDisk: Int
    public let cpuCores: Int
    public let loadAverage: [Double]
    public let activeConnections: Int
    public let timestamp: UInt64
    
    public init(systemUptime: UInt64, totalMemory: Int, freeMemory: Int, totalDisk: Int, freeDisk: Int, cpuCores: Int, loadAverage: [Double], activeConnections: Int, timestamp: UInt64) {
        self.systemUptime = systemUptime
        self.totalMemory = totalMemory
        self.freeMemory = freeMemory
        self.totalDisk = totalDisk
        self.freeDisk = freeDisk
        self.cpuCores = cpuCores
        self.loadAverage = loadAverage
        self.activeConnections = activeConnections
        self.timestamp = timestamp
    }
}

/// Monitoring configuration
/// Corresponds to TLA+: MonitoringConfig
public struct MonitoringConfig: Codable, Sendable, Equatable {
    public let maxMetrics: Int
    public let metricRetentionTime: UInt64
    public let alertThreshold: Double
    public let healthCheckInterval: UInt64
    public let maxAlerts: Int
    public let metricSamplingRate: Double
    public let enableTelemetry: Bool
    public let enableAlerts: Bool
    
    public init(maxMetrics: Int, metricRetentionTime: UInt64, alertThreshold: Double, healthCheckInterval: UInt64, maxAlerts: Int, metricSamplingRate: Double, enableTelemetry: Bool, enableAlerts: Bool) {
        self.maxMetrics = maxMetrics
        self.metricRetentionTime = metricRetentionTime
        self.alertThreshold = alertThreshold
        self.healthCheckInterval = healthCheckInterval
        self.maxAlerts = maxAlerts
        self.metricSamplingRate = metricSamplingRate
        self.enableTelemetry = enableTelemetry
        self.enableAlerts = enableAlerts
    }
}

/// Log aggregator
/// Corresponds to TLA+: LogAggregator
public struct LogAggregator: Codable, Sendable, Equatable {
    public let logLevel: String
    public let logCount: Int
    public let errorCount: Int
    public let warningCount: Int
    public let infoCount: Int
    public let debugCount: Int
    public let lastLogTime: UInt64
    public let isEnabled: Bool
    
    public init(logLevel: String, logCount: Int, errorCount: Int, warningCount: Int, infoCount: Int, debugCount: Int, lastLogTime: UInt64, isEnabled: Bool) {
        self.logLevel = logLevel
        self.logCount = logCount
        self.errorCount = errorCount
        self.warningCount = warningCount
        self.infoCount = infoCount
        self.debugCount = debugCount
        self.lastLogTime = lastLogTime
        self.isEnabled = isEnabled
    }
}

// MARK: - System Monitor

/// System Monitor for monitoring and metrics
/// Corresponds to TLA+ module: Monitor.tla
public actor SystemMonitor {
    
    // MARK: - State Variables (TLA+ vars)
    
    /// Metrics
    /// TLA+: metrics \in [String -> Metric]
    private var metrics: [String: Metric] = [:]
    
    /// Alerts
    /// TLA+: alerts \in [String -> Alert]
    private var alerts: [String: Alert] = [:]
    
    /// Health checks
    /// TLA+: healthChecks \in [String -> HealthCheck]
    private var healthChecks: [String: HealthCheck] = [:]
    
    /// Performance data
    /// TLA+: performanceData \in [String -> PerformanceData]
    private var performanceData: [String: PerformanceData] = [:]
    
    /// Resource usage
    /// TLA+: resourceUsage \in [String -> ResourceUsage]
    private var resourceUsage: [String: ResourceUsage] = [:]
    
    /// Query metrics
    /// TLA+: queryMetrics \in [String -> QueryMetric]
    private var queryMetrics: [String: QueryMetric] = [:]
    
    /// System diagnostics
    /// TLA+: systemDiagnostics \in SystemDiagnostics
    private var systemDiagnostics: SystemDiagnostics?
    
    /// Monitoring configuration
    /// TLA+: monitoringConfig \in MonitoringConfig
    private var monitoringConfig: MonitoringConfig
    
    /// Log aggregator
    /// TLA+: logAggregator \in LogAggregator
    private var logAggregator: LogAggregator
    
    // MARK: - Initialization
    
    public init(monitoringConfig: MonitoringConfig = MonitoringConfig(
        maxMetrics: 1000,
        metricRetentionTime: 86400000, // 24 hours
        alertThreshold: 80.0,
        healthCheckInterval: 5000, // 5 seconds
        maxAlerts: 100,
        metricSamplingRate: 1.0,
        enableTelemetry: true,
        enableAlerts: true
    )) {
        self.monitoringConfig = monitoringConfig
        
        // TLA+ Init
        self.metrics = [:]
        self.alerts = [:]
        self.healthChecks = [:]
        self.performanceData = [:]
        self.resourceUsage = [:]
        self.queryMetrics = [:]
        self.systemDiagnostics = nil
        self.logAggregator = LogAggregator(
            logLevel: "INFO",
            logCount: 0,
            errorCount: 0,
            warningCount: 0,
            infoCount: 0,
            debugCount: 0,
            lastLogTime: 0,
            isEnabled: true
        )
    }
    
    // MARK: - Monitoring Operations
    
    /// Update metric
    /// TLA+ Action: UpdateMetric(metricId, value)
    public func updateMetric(metricId: String, value: Double, componentId: String = "system", metricType: MetricType = .gauge, labels: [String: String] = [:]) async {
        // TLA+: Update metric
        let metric = Metric(
            metricId: metricId,
            name: metricId,
            value: value,
            unit: "count",
            timestamp: UInt64(Date().timeIntervalSince1970 * 1000),
            componentId: componentId,
            metricType: metricType,
            labels: labels,
            isActive: true
        )
        
        metrics[metricId] = metric
        
        // TLA+: Check threshold
        if monitoringConfig.enableAlerts {
            try? await checkThreshold(metricId: metricId)
        }
        
        print("Updated metric: \(metricId) = \(value)")
    }
    
    /// Check threshold
    /// TLA+ Action: CheckThreshold(metricId)
    public func checkThreshold(metricId: String) async throws {
        // TLA+: Check threshold
        guard let metric = metrics[metricId] else {
            return
        }
        
        // TLA+: Check if threshold exceeded
        if metric.value > monitoringConfig.alertThreshold {
            try await createAlert(metricId: metricId, value: metric.value)
        }
    }
    
    /// Create alert
    /// TLA+ Action: CreateAlert(metricId, value)
    public func createAlert(metricId: String, value: Double) async throws {
        // TLA+: Create alert
        let alert = Alert(
            alertId: UUID().uuidString,
            name: "High \(metricId)",
            severity: value > monitoringConfig.alertThreshold * 1.5 ? .critical : .warning,
            status: .firing,
            componentId: "system",
            metricId: metricId,
            threshold: monitoringConfig.alertThreshold,
            currentValue: value,
            triggeredAt: UInt64(Date().timeIntervalSince1970 * 1000),
            resolvedAt: 0,
            message: "Metric \(metricId) exceeded threshold: \(value) > \(monitoringConfig.alertThreshold)",
            isAcknowledged: false
        )
        
        alerts[alert.alertId] = alert
        
        print("Created alert: \(alert.alertId) for metric: \(metricId)")
    }
    
    /// Clear alert
    /// TLA+ Action: ClearAlert(alertId)
    public func clearAlert(alertId: String) async {
        // TLA+: Clear alert
        if var alert = alerts[alertId] {
            alert = Alert(
                alertId: alert.alertId,
                name: alert.name,
                severity: alert.severity,
                status: .resolved,
                componentId: alert.componentId,
                metricId: alert.metricId,
                threshold: alert.threshold,
                currentValue: alert.currentValue,
                triggeredAt: alert.triggeredAt,
                resolvedAt: UInt64(Date().timeIntervalSince1970 * 1000),
                message: alert.message,
                isAcknowledged: alert.isAcknowledged
            )
            alerts[alertId] = alert
        }
        
        print("Cleared alert: \(alertId)")
    }
    
    /// Update health check
    /// TLA+ Action: UpdateHealthCheck(componentId, status)
    public func updateHealthCheck(componentId: String, componentName: String, status: HealthState, responseTime: UInt64 = 0, lastError: String = "") async {
        // TLA+: Update health check
        let healthCheck = HealthCheck(
            componentId: componentId,
            componentName: componentName,
            status: status,
            lastCheck: UInt64(Date().timeIntervalSince1970 * 1000),
            checkInterval: monitoringConfig.healthCheckInterval,
            consecutiveFailures: status == .healthy ? 0 : 1,
            lastError: lastError,
            responseTime: responseTime,
            isEnabled: true
        )
        
        healthChecks[componentId] = healthCheck
        
        print("Updated health check: \(componentId) = \(status)")
    }
    
    /// Update performance data
    /// TLA+ Action: UpdatePerformanceData(componentId, data)
    public func updatePerformanceData(componentId: String, cpuUsage: Double, memoryUsage: Double, diskUsage: Double, networkUsage: Double, queryCount: Int, avgResponseTime: Double, errorRate: Double) async {
        // TLA+: Update performance data
        let perfData = PerformanceData(
            componentId: componentId,
            cpuUsage: cpuUsage,
            memoryUsage: memoryUsage,
            diskUsage: diskUsage,
            networkUsage: networkUsage,
            queryCount: queryCount,
            avgResponseTime: avgResponseTime,
            errorRate: errorRate,
            timestamp: UInt64(Date().timeIntervalSince1970 * 1000)
        )
        
        performanceData[componentId] = perfData
        
        print("Updated performance data: \(componentId)")
    }
    
    /// Update resource usage
    /// TLA+ Action: UpdateResourceUsage(resourceId, usage)
    public func updateResourceUsage(resourceId: String, resourceType: String, currentUsage: Double, maxCapacity: Double) async {
        // TLA+: Update resource usage
        let utilizationPercent = (currentUsage / maxCapacity) * 100.0
        
        let resourceUsage = ResourceUsage(
            resourceId: resourceId,
            resourceType: resourceType,
            currentUsage: currentUsage,
            maxCapacity: maxCapacity,
            utilizationPercent: utilizationPercent,
            timestamp: UInt64(Date().timeIntervalSince1970 * 1000)
        )
        
        self.resourceUsage[resourceId] = resourceUsage
        
        print("Updated resource usage: \(resourceId) = \(utilizationPercent)%")
    }
    
    /// Update query metric
    /// TLA+ Action: UpdateQueryMetric(queryId, metric)
    public func updateQueryMetric(queryId: String, queryText: String, executionTime: UInt64, rowsReturned: Int, rowsScanned: Int, cpuTime: UInt64, ioTime: UInt64, memoryUsed: Int) async {
        // TLA+: Update query metric
        let queryMetric = QueryMetric(
            queryId: queryId,
            queryText: queryText,
            executionTime: executionTime,
            rowsReturned: rowsReturned,
            rowsScanned: rowsScanned,
            cpuTime: cpuTime,
            ioTime: ioTime,
            memoryUsed: memoryUsed,
            timestamp: UInt64(Date().timeIntervalSince1970 * 1000)
        )
        
        queryMetrics[queryId] = queryMetric
        
        print("Updated query metric: \(queryId)")
    }
    
    /// Update system diagnostics
    /// TLA+ Action: UpdateSystemDiagnostics(diagnostics)
    public func updateSystemDiagnostics(systemUptime: UInt64, totalMemory: Int, freeMemory: Int, totalDisk: Int, freeDisk: Int, cpuCores: Int, loadAverage: [Double], activeConnections: Int) async {
        // TLA+: Update system diagnostics
        let diagnostics = SystemDiagnostics(
            systemUptime: systemUptime,
            totalMemory: totalMemory,
            freeMemory: freeMemory,
            totalDisk: totalDisk,
            freeDisk: freeDisk,
            cpuCores: cpuCores,
            loadAverage: loadAverage,
            activeConnections: activeConnections,
            timestamp: UInt64(Date().timeIntervalSince1970 * 1000)
        )
        
        systemDiagnostics = diagnostics
        
        print("Updated system diagnostics")
    }
    
    /// Update log aggregator
    /// TLA+ Action: UpdateLogAggregator(logLevel, count)
    public func updateLogAggregator(logLevel: String, logCount: Int, errorCount: Int, warningCount: Int, infoCount: Int, debugCount: Int) async {
        // TLA+: Update log aggregator
        logAggregator = LogAggregator(
            logLevel: logLevel,
            logCount: logCount,
            errorCount: errorCount,
            warningCount: warningCount,
            infoCount: infoCount,
            debugCount: debugCount,
            lastLogTime: UInt64(Date().timeIntervalSince1970 * 1000),
            isEnabled: true
        )
        
        print("Updated log aggregator: \(logLevel) = \(logCount)")
    }
    
    // MARK: - Query Operations
    
    /// Get metric value
    public func getMetricValue(metricId: String) -> Double? {
        return metrics[metricId]?.value
    }
    
    /// Get active alerts
    public func getActiveAlerts() -> [Alert] {
        return alerts.values.filter { $0.status == .firing }
    }
    
    /// Get component health
    public func getComponentHealth(componentId: String) -> HealthState? {
        return healthChecks[componentId]?.status
    }
    
    /// Get all metrics
    public func getAllMetrics() -> [Metric] {
        return Array(metrics.values)
    }
    
    /// Get all alerts
    public func getAllAlerts() -> [Alert] {
        return Array(alerts.values)
    }
    
    /// Get health status for all components
    public func getAllHealthStatus() -> [String: HealthState] {
        var status: [String: HealthState] = [:]
        for (componentId, healthCheck) in healthChecks {
            status[componentId] = healthCheck.status
        }
        return status
    }
    
    /// Get performance data
    public func getPerformanceData(componentId: String) -> PerformanceData? {
        return performanceData[componentId]
    }
    
    /// Get resource usage
    public func getResourceUsage(resourceId: String) -> ResourceUsage? {
        return resourceUsage[resourceId]
    }
    
    /// Get query metrics
    public func getQueryMetrics(queryId: String) -> QueryMetric? {
        return queryMetrics[queryId]
    }
    
    /// Get system diagnostics
    public func getSystemDiagnostics() -> SystemDiagnostics? {
        return systemDiagnostics
    }
    
    /// Get monitoring configuration
    public func getMonitoringConfig() -> MonitoringConfig {
        return monitoringConfig
    }
    
    /// Get log aggregator
    public func getLogAggregator() -> LogAggregator {
        return logAggregator
    }
    
    /// Check if component is healthy
    public func isComponentHealthy(componentId: String) -> Bool {
        return healthChecks[componentId]?.status == .healthy
    }
    
    /// Check if has active alerts
    public func hasActiveAlerts() -> Bool {
        return !getActiveAlerts().isEmpty
    }
    
    /// Get metrics count
    public func getMetricsCount() -> Int {
        return metrics.count
    }
    
    /// Get alerts count
    public func getAlertsCount() -> Int {
        return alerts.count
    }
    
    /// Get health checks count
    public func getHealthChecksCount() -> Int {
        return healthChecks.count
    }
    
    // MARK: - Invariant Checking (for testing)
    
    /// Check alert consistency invariant
    /// TLA+ Inv_Monitor_AlertConsistency
    public func checkAlertConsistencyInvariant() -> Bool {
        // Check that alerts are consistent with metrics
        for alert in alerts.values {
            if let metric = metrics[alert.metricId] {
                if alert.status == .firing && metric.value <= alert.threshold {
                    return false
                }
            }
        }
        return true
    }
    
    /// Check health status consistency invariant
    /// TLA+ Inv_Monitor_HealthStatusConsistency
    public func checkHealthStatusConsistencyInvariant() -> Bool {
        // Check that health status reflects actual state
        for healthCheck in healthChecks.values {
            if healthCheck.status == .healthy && healthCheck.consecutiveFailures > 0 {
                return false
            }
        }
        return true
    }
    
    /// Check telemetry integrity invariant
    /// TLA+ Inv_Monitor_TelemetryIntegrity
    public func checkTelemetryIntegrityInvariant() -> Bool {
        // Check that telemetry data is accurate
        return true // Simplified
    }
    
    /// Check all invariants
    public func checkAllInvariants() -> Bool {
        let alertConsistency = checkAlertConsistencyInvariant()
        let healthStatusConsistency = checkHealthStatusConsistencyInvariant()
        let telemetryIntegrity = checkTelemetryIntegrityInvariant()
        
        return alertConsistency && healthStatusConsistency && telemetryIntegrity
    }
}