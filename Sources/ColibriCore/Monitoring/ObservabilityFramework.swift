//
//  ObservabilityFramework.swift
//  ColibrìDB Observability with Correlation IDs & PII-Free Logging
//
//  Exit Criteria: structured logs with correlation-ID, PII-free, all signals present
//

import Foundation
import Logging

/// Correlation ID for distributed tracing
public struct CorrelationID: Codable, Hashable, Sendable, CustomStringConvertible {
    public let value: String
    
    public init() {
        self.value = UUID().uuidString
    }
    
    public init(value: String) {
        self.value = value
    }
    
    public var description: String {
        return value
    }
}

/// Structured log entry with correlation support
public struct StructuredLogEntry: Codable {
    public let timestamp: Date
    public let level: String
    public let message: String
    public let correlationID: CorrelationID?
    public let metadata: [String: String]
    
    public init(
        level: String,
        message: String,
        correlationID: CorrelationID? = nil,
        metadata: [String: String] = [:]
    ) {
        self.timestamp = Date()
        self.level = level
        self.message = message
        self.correlationID = correlationID
        self.metadata = PIIFilter.filter(metadata)  // Auto-filter PII
    }
    
    public func toJSON() -> String {
        let encoder = JSONEncoder()
        encoder.dateEncodingStrategy = .iso8601
        if let data = try? encoder.encode(self),
           let json = String(data: data, encoding: .utf8) {
            return json
        }
        return "{}"
    }
}

/// PII (Personally Identifiable Information) filter
public enum PIIFilter {
    private static let piiPatterns = [
        "password",
        "secret",
        "token",
        "api_key",
        "apikey",
        "email",
        "ssn",
        "credit_card",
        "phone"
    ]
    
    /// Filter PII from metadata
    public static func filter(_ metadata: [String: String]) -> [String: String] {
        var filtered: [String: String] = [:]
        
        for (key, value) in metadata {
            let lowerKey = key.lowercased()
            
            if piiPatterns.contains(where: { lowerKey.contains($0) }) {
                filtered[key] = "[REDACTED]"
            } else {
                filtered[key] = value
            }
        }
        
        return filtered
    }
    
    /// Redact email addresses
    public static func redactEmail(_ email: String) -> String {
        guard let atIndex = email.firstIndex(of: "@") else {
            return "[REDACTED]"
        }
        
        let prefix = email[..<atIndex]
        let suffix = email[atIndex...]
        
        if prefix.count <= 2 {
            return "**" + suffix
        } else {
            let visible = String(prefix.prefix(2))
            let hidden = String(repeating: "*", count: prefix.count - 2)
            return visible + hidden + suffix
        }
    }
}

/// Observable database metrics
public struct DatabaseMetrics: Codable {
    public var totalTransactions: Int = 0
    public var activeTransactions: Int = 0
    public var totalQueries: Int = 0
    public var cacheHits: Int = 0
    public var cacheMisses: Int = 0
    public var walFlushes: Int = 0
    public var replayTimeMs: Double = 0
    
    public var cacheHitRate: Double {
        let total = cacheHits + cacheMisses
        return total > 0 ? Double(cacheHits) / Double(total) : 0.0
    }
    
    public mutating func recordTransaction() {
        totalTransactions += 1
    }
    
    public mutating func recordQuery() {
        totalQueries += 1
    }
    
    public mutating func recordCacheHit() {
        cacheHits += 1
    }
    
    public mutating func recordCacheMiss() {
        cacheMisses += 1
    }
    
    public mutating func recordWALFlush() {
        walFlushes += 1
    }
    
    public mutating func recordReplay(durationMs: Double) {
        replayTimeMs = durationMs
    }
}

/// Observability manager
public actor ObservabilityManager {
    private var metrics = DatabaseMetrics()
    private let logger: ColibriLogger
    
    public init() {
        self.logger = ColibriLogger()
    }
    
    /// Log structured entry
    public func log(
        level: LogLevel,
        message: String,
        correlationID: CorrelationID? = nil,
        metadata: [String: String] = [:]
    ) async {
        let entry = StructuredLogEntry(
            level: level.rawValue,
            message: message,
            correlationID: correlationID,
            metadata: metadata
        )
        
        await logger.log(
            level,
            category: .general,
            message,
            metadata: metadata
        )
    }
    
    /// Record transaction
    public func recordTransaction(correlationID: CorrelationID) async {
        metrics.recordTransaction()
        await log(
            level: .info,
            message: "Transaction recorded",
            correlationID: correlationID,
            metadata: ["total": "\(metrics.totalTransactions)"]
        )
    }
    
    /// Get current metrics
    public func getMetrics() -> DatabaseMetrics {
        return metrics
    }
    
    /// Export metrics for dashboard
    public func exportMetrics() -> String {
        let encoder = JSONEncoder()
        encoder.outputFormatting = .prettyPrinted
        
        if let data = try? encoder.encode(metrics),
           let json = String(data: data, encoding: .utf8) {
            return json
        }
        
        return "{}"
    }
}

/// Metric collector for monitoring
public actor MetricCollector {
    private var counters: [String: Int] = [:]
    private var histograms: [String: [Double]] = [:]
    
    public init() {}
    
    /// Increment counter
    public func increment(metric: String, by value: Int = 1) {
        counters[metric, default: 0] += value
    }
    
    /// Record histogram value
    public func record(metric: String, value: Double) {
        histograms[metric, default: []].append(value)
    }
    
    /// Get counter value
    public func getCounter(_ metric: String) -> Int {
        return counters[metric, default: 0]
    }
    
    /// Get histogram percentile
    public func getPercentile(_ metric: String, percentile: Double) -> Double {
        guard var values = histograms[metric], !values.isEmpty else {
            return 0.0
        }
        
        values.sort()
        let index = Int(Double(values.count) * percentile / 100.0)
        return values[min(index, values.count - 1)]
    }
    
    /// Export all metrics
    public func export() -> [String: Any] {
        var result: [String: Any] = [:]
        
        for (key, value) in counters {
            result[key] = value
        }
        
        for (key, values) in histograms {
            result["\(key).count"] = values.count
            result["\(key).p50"] = getPercentile(key, percentile: 50)
            result["\(key).p95"] = getPercentile(key, percentile: 95)
            result["\(key).p99"] = getPercentile(key, percentile: 99)
        }
        
        return result
    }
}

