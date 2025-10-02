//
//  DevCLI+Monitoring.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Monitoring commands for development CLI.

import Foundation
import ColibriCore

extension DevCLI {
    
    @MainActor private static var performanceMonitor: PerformanceMonitor?
    @MainActor private static var cpuProfiler: CPUProfiler?
    
    /// Handles monitoring-related commands
    @MainActor mutating func handleMonitoringCommands(_ trimmed: String) {
        if trimmed.hasPrefix("\\monitor stats") {
            handleMonitorStats(trimmed)
            return
        }
        
        if trimmed.hasPrefix("\\monitor memory") {
            handleMonitorMemory(trimmed)
            return
        }
        
        if trimmed.hasPrefix("\\monitor performance") {
            handleMonitorPerformance(trimmed)
            return
        }
        
        if trimmed.hasPrefix("\\monitor constraints") {
            handleMonitorConstraints(trimmed)
            return
        }
        
        if trimmed.hasPrefix("\\profile start") {
            handleProfileStart(trimmed)
            return
        }
        
        if trimmed.hasPrefix("\\profile stop") {
            handleProfileStop()
            return
        }
        
        if trimmed.hasPrefix("\\profile memory") {
            handleProfileMemory(trimmed)
            return
        }
        
        if trimmed.hasPrefix("\\profile sql") {
            handleProfileSQL(trimmed)
            return
        }
        
        if trimmed.hasPrefix("\\profile constraints") {
            handleProfileConstraints(trimmed)
            return
        }
    }
    
    // MARK: - Monitor Commands
    
    /// Monitor real-time statistics
    @MainActor private func handleMonitorStats(_ trimmed: String) {
        let parts = trimmed.split(separator: " ")
        let interval = Double(parts.first(where: { $0.hasPrefix("interval=") })?.dropFirst("interval=".count) ?? "1.0") ?? 1.0
        let duration = Double(parts.first(where: { $0.hasPrefix("duration=") })?.dropFirst("duration=".count) ?? "60.0") ?? 60.0
        
        if Self.performanceMonitor == nil {
            Self.performanceMonitor = PerformanceMonitor(database: db)
        }
        
        Self.performanceMonitor?.startMonitoring(interval: interval)
        
        print("Monitoring started for \(duration) seconds with \(interval)s interval")
        print("Press Ctrl+C to stop early")
        
        // Stop after duration
        DispatchQueue.main.asyncAfter(deadline: .now() + duration) {
            self.handleMonitorStop()
        }
    }
    
    /// Monitor memory usage
    private func handleMonitorMemory(_ trimmed: String) {
        let debugTools = DebugTools(database: db)
        let analysis = debugTools.analyzeMemory()
        
        print("=== Memory Monitor ===")
        print("Resident Size: \(String(format: "%.2f", analysis.residentSizeMB)) MB")
        print("Virtual Size: \(String(format: "%.2f", analysis.virtualSizeMB)) MB")
        print("Peak Resident Size: \(String(format: "%.2f", Double(analysis.peakResidentSize) / 1024.0 / 1024.0)) MB")
        print("Timestamp: \(analysis.timestamp)")
        
        // Check if continuous monitoring is requested
        let parts = trimmed.split(separator: " ")
        if parts.contains("continuous") {
            let interval = Double(parts.first(where: { $0.hasPrefix("interval=") })?.dropFirst("interval=".count) ?? "1.0") ?? 1.0
            startMemoryMonitoring(interval: interval)
        }
    }
    
    /// Monitor performance metrics
    @MainActor private func handleMonitorPerformance(_ trimmed: String) {
        if let monitor = Self.performanceMonitor {
            let summary = monitor.getPerformanceSummary()
            print("=== Performance Monitor ===")
            print("Average Hit Ratio: \(String(format: "%.2f", summary.averageHitRatioPercentage))%")
            print("Peak Hit Ratio: \(String(format: "%.2f", summary.peakHitRatioPercentage))%")
            print("Average Memory Usage: \(String(format: "%.2f", summary.averageMemoryUsageMB)) MB")
            print("Peak Memory Usage: \(String(format: "%.2f", summary.peakMemoryUsageMB)) MB")
            print("Total Buffer Hits: \(summary.totalBufferHits)")
            print("Total Buffer Misses: \(summary.totalBufferMisses)")
            print("Total Evictions: \(summary.totalEvictions)")
            print("Monitoring Duration: \(String(format: "%.1f", summary.monitoringDuration))s")
            print("Sample Count: \(summary.sampleCount)")
        } else {
            print("No performance monitoring active. Use \\monitor stats to start.")
        }
    }
    
    /// Monitor constraint validation
    private func handleMonitorConstraints(_ trimmed: String) {
        let debugTools = DebugTools(database: db)
        let analysis = debugTools.analyzeConstraints()
        
        print("=== Constraint Monitor ===")
        print("Total Constraints: \(analysis.totalConstraints)")
        print("Tables: \(analysis.tables.joined(separator: ", "))")
        
        if !analysis.constraintTypes.isEmpty {
            print("\nConstraint Types:")
            for (type, count) in analysis.constraintTypes.sorted(by: { $0.value > $1.value }) {
                print("  \(type): \(count)")
            }
        }
        
        if !analysis.validationTimes.isEmpty {
            print("\nValidation Times:")
            for (name, time) in analysis.validationTimes.sorted(by: { $0.value > $1.value }) {
                print("  \(name): \(String(format: "%.4f", time))s")
            }
        }
        
        print("Timestamp: \(analysis.timestamp)")
    }
    
    /// Stop monitoring
    @MainActor private func handleMonitorStop() {
        Self.performanceMonitor?.stopMonitoring()
        print("Monitoring stopped")
    }
    
    // MARK: - Profile Commands
    
    /// Start profiling
    @MainActor private func handleProfileStart(_ trimmed: String) {
        if Self.cpuProfiler == nil {
            Self.cpuProfiler = CPUProfiler(database: db)
        }
        
        Self.cpuProfiler?.startProfiling()
        print("CPU profiling started")
    }
    
    /// Stop profiling
    @MainActor private func handleProfileStop() {
        Self.cpuProfiler?.stopProfiling()
        
        if let profiler = Self.cpuProfiler {
            let stats = profiler.getCPUStats()
            print("=== CPU Profile Results ===")
            print("Average Duration: \(String(format: "%.4f", stats.averageDuration))s")
            print("Peak Duration: \(String(format: "%.4f", stats.peakDuration))s")
            print("Average CPU Usage: \(String(format: "%.2f", stats.averageCPUUsage)) MB")
            print("Peak CPU Usage: \(String(format: "%.2f", stats.peakCPUUsage)) MB")
            print("Total Operations: \(stats.totalOperations)")
            print("Timestamp: \(stats.timestamp)")
        }
    }
    
    /// Profile memory operations
    private func handleProfileMemory(_ trimmed: String) {
        let debugTools = DebugTools(database: db)
        let operation = String(trimmed.dropFirst("\\profile memory ".count))
        
        do {
            let result = try debugTools.profileOperation({
                // Execute the operation
                self.executeMemoryOperation(operation)
            }, name: "memory_\(operation)")
            
            print("=== Memory Profile ===")
            print("Operation: \(result.name)")
            print("Duration: \(String(format: "%.4f", result.duration))s")
            print("Memory Delta: \(String(format: "%.2f", Double(result.memoryDelta) / 1024.0 / 1024.0)) MB")
            print("Success: \(result.success)")
            
            if let error = result.error {
                print("Error: \(error)")
            }
            
            print("Timestamp: \(result.timestamp)")
        } catch {
            print("Profile error: \(error)")
        }
    }
    
    /// Profile SQL operations
    private func handleProfileSQL(_ trimmed: String) {
        let sql = String(trimmed.dropFirst("\\profile sql ".count))
        let debugTools = DebugTools(database: db)
        let analysis = debugTools.analyzeSQL(sql)
        
        print("=== SQL Profile ===")
        print("SQL: \(analysis.sql)")
        print("Parse Time: \(String(format: "%.4f", analysis.parseTime))s")
        print("Execution Time: \(String(format: "%.4f", analysis.executionTime))s")
        print("Total Time: \(String(format: "%.4f", analysis.totalTime))s")
        print("Success: \(analysis.success)")
        
        if let error = analysis.error {
            print("Error: \(error)")
        }
        
        if let resultType = analysis.resultType {
            print("Result Type: \(resultType)")
        }
        
        print("Timestamp: \(analysis.timestamp)")
    }
    
    /// Profile constraint operations
    private func handleProfileConstraints(_ trimmed: String) {
        let debugTools = DebugTools(database: db)
        let analysis = debugTools.analyzeConstraints()
        
        print("=== Constraint Profile ===")
        print("Total Constraints: \(analysis.totalConstraints)")
        
        if !analysis.validationTimes.isEmpty {
            let totalTime = analysis.validationTimes.values.reduce(0, +)
            let averageTime = totalTime / Double(analysis.validationTimes.count)
            let maxTime = analysis.validationTimes.values.max() ?? 0
            let minTime = analysis.validationTimes.values.min() ?? 0
            
            print("Total Validation Time: \(String(format: "%.4f", totalTime))s")
            print("Average Validation Time: \(String(format: "%.4f", averageTime))s")
            print("Max Validation Time: \(String(format: "%.4f", maxTime))s")
            print("Min Validation Time: \(String(format: "%.4f", minTime))s")
        }
        
        print("Timestamp: \(analysis.timestamp)")
    }
    
    // MARK: - Helper Methods
    
    private func startMemoryMonitoring(interval: TimeInterval) {
        let debugTools = DebugTools(database: db)
        let monitor = debugTools.startMemoryMonitoring(interval: interval, duration: 60.0)
        monitor.start()
        
        print("Memory monitoring started with \(interval)s interval")
    }
    
    private func executeMemoryOperation(_ operation: String) {
        // Execute various memory-intensive operations for profiling
        switch operation {
        case "scan_all":
            let tables = db.listTables()
            for table in tables {
                _ = try? db.scan(table)
            }
        case "buffer_flush":
            db.flushAll(fullSync: true)
        case "vacuum":
            db.startVacuum(intervalSeconds: 0.1, pagesPerRun: 10)
            Thread.sleep(forTimeInterval: 1.0)
            db.stopVacuum()
        case "index_scan":
            let tables = db.listTables()
            for table in tables {
                let indexes = db.listIndexes(table: table)
                for index in indexes {
                    _ = try? db.indexSearchEqualsTyped(table: table, index: index, value: .string("test"))
                }
            }
        default:
            print("Unknown memory operation: \(operation)")
        }
    }
}
