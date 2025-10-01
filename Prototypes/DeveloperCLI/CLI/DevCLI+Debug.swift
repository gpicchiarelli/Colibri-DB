//
//  DevCLI+Debug.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Debug commands for development CLI.

import Foundation
import ColibriCore

extension DevCLI {
    
    /// Handles debug-related commands
    mutating func handleDebugCommands(_ trimmed: String) {
        if trimmed.hasPrefix("\\debug memory") {
            handleDebugMemory(trimmed)
            return
        }
        
        if trimmed.hasPrefix("\\debug performance") {
            handleDebugPerformance(trimmed)
            return
        }
        
        if trimmed.hasPrefix("\\debug constraints") {
            handleDebugConstraints(trimmed)
            return
        }
        
        if trimmed.hasPrefix("\\debug sql") {
            handleDebugSQL(trimmed)
            return
        }
        
        if trimmed.hasPrefix("\\debug types") {
            handleDebugTypes(trimmed)
            return
        }
        
        if trimmed.hasPrefix("\\debug profile") {
            handleDebugProfile(trimmed)
            return
        }
    }
    
    /// Debug memory usage
    private func handleDebugMemory(_ trimmed: String) {
        let debugTools = DebugTools(database: db)
        let analysis = debugTools.analyzeMemory()
        
        print("=== Memory Analysis ===")
        print("Resident Size: \(String(format: "%.2f", analysis.residentSizeMB)) MB")
        print("Virtual Size: \(String(format: "%.2f", analysis.virtualSizeMB)) MB")
        print("Peak Resident Size: \(String(format: "%.2f", Double(analysis.peakResidentSize) / 1024.0 / 1024.0)) MB")
        print("Timestamp: \(analysis.timestamp)")
        
        // Check if monitoring is requested
        let parts = trimmed.split(separator: " ")
        if parts.contains("monitor") {
            let interval = Double(parts.first(where: { $0.hasPrefix("interval=") })?.dropFirst("interval=".count) ?? "1.0") ?? 1.0
            let duration = Double(parts.first(where: { $0.hasPrefix("duration=") })?.dropFirst("duration=".count) ?? "60.0") ?? 60.0
            
            print("\nStarting memory monitoring for \(duration) seconds...")
            let monitor = debugTools.startMemoryMonitoring(interval: interval, duration: duration)
            monitor.start()
            
            // Wait for monitoring to complete
            DispatchQueue.main.asyncAfter(deadline: .now() + duration) {
                let analysis = monitor.getAnalysis()
                self.printMemoryMonitoringResults(analysis)
            }
        }
    }
    
    /// Debug performance metrics
    private func handleDebugPerformance(_ trimmed: String) {
        let debugTools = DebugTools(database: db)
        let analysis = debugTools.analyzePerformance()
        
        print("=== Performance Analysis ===")
        print("Buffer Hits: \(analysis.bufferHits)")
        print("Buffer Misses: \(analysis.bufferMisses)")
        print("Buffer Hit Ratio: \(String(format: "%.2f", analysis.bufferHitRatio * 100))%")
        print("Buffer Evictions: \(analysis.bufferEvictions)")
        print("Buffer Pages: \(analysis.bufferPages)")
        print("Buffer Capacity: \(analysis.bufferCapacity)")
        print("Buffer Pinned: \(analysis.bufferPinned)")
        print("Buffer Dirty: \(analysis.bufferDirty)")
        print("Vacuum Runs: \(analysis.vacuumRuns)")
        print("Vacuum Pages Compacted: \(analysis.vacuumPagesCompacted)")
        print("Vacuum Bytes Reclaimed: \(analysis.vacuumBytesReclaimed)")
        if let lastRun = analysis.vacuumLastRun {
            print("Vacuum Last Run: \(lastRun)")
        } else {
            print("Vacuum Last Run: Never")
        }
        print("Timestamp: \(analysis.timestamp)")
    }
    
    /// Debug constraint validation
    private func handleDebugConstraints(_ trimmed: String) {
        let debugTools = DebugTools(database: db)
        let analysis = debugTools.analyzeConstraints()
        
        print("=== Constraint Analysis ===")
        print("Total Constraints: \(analysis.totalConstraints)")
        print("Tables: \(analysis.tables.joined(separator: ", "))")
        print("\nConstraint Types:")
        for (type, count) in analysis.constraintTypes.sorted(by: { $0.value > $1.value }) {
            print("  \(type): \(count)")
        }
        
        if !analysis.validationTimes.isEmpty {
            print("\nValidation Times:")
            for (name, time) in analysis.validationTimes.sorted(by: { $0.value > $1.value }) {
                print("  \(name): \(String(format: "%.4f", time))s")
            }
        }
        print("Timestamp: \(analysis.timestamp)")
    }
    
    /// Debug SQL parsing and execution
    private func handleDebugSQL(_ trimmed: String) {
        let sql = String(trimmed.dropFirst("\\debug sql ".count))
        let debugTools = DebugTools(database: db)
        let analysis = debugTools.analyzeSQL(sql)
        
        print("=== SQL Analysis ===")
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
    
    /// Debug type system
    private func handleDebugTypes(_ trimmed: String) {
        let debugTools = DebugTools(database: db)
        let analysis = debugTools.analyzeTypeSystem()
        
        print("=== Type System Analysis ===")
        print("Tables: \(analysis.tables.joined(separator: ", "))")
        
        if !analysis.typeUsage.isEmpty {
            print("\nType Usage:")
            for (type, count) in analysis.typeUsage.sorted(by: { $0.value > $1.value }) {
                print("  \(type): \(count)")
            }
        }
        
        if !analysis.conversionErrors.isEmpty {
            print("\nConversion Errors:")
            for (type, count) in analysis.conversionErrors.sorted(by: { $0.value > $1.value }) {
                print("  \(type): \(count)")
            }
        }
        
        print("Timestamp: \(analysis.timestamp)")
    }
    
    /// Debug profiling
    private func handleDebugProfile(_ trimmed: String) {
        let parts = trimmed.split(separator: " ")
        guard parts.count >= 3 else {
            print("usage: \\debug profile <operation> <command>")
            print("operations: start, stop, results")
            return
        }
        
        let operation = String(parts[1])
        let command = parts.dropFirst(2).joined(separator: " ")
        
        switch operation {
        case "start":
            startProfiling(command: command)
        case "stop":
            stopProfiling()
        case "results":
            showProfilingResults()
        default:
            print("Unknown operation: \(operation)")
        }
    }
    
    
    private func startProfiling(command: String) {
        let profilingSession = ProfilingSession(database: db, command: command)
        profilingSession.start()
        print("Profiling started for command: \(command)")
    }
    
    private func stopProfiling() {
        print("Profiling stopped")
    }
    
    private func showProfilingResults() {
        print("No profiling session available")
    }
    
    private func printMemoryMonitoringResults(_ analysis: MemoryMonitoringAnalysis) {
        print("\n=== Memory Monitoring Results ===")
        print("Samples Collected: \(analysis.samples.count)")
        print("Average Resident Size: \(String(format: "%.2f", Double(analysis.averageResidentSize) / 1024.0 / 1024.0)) MB")
        print("Peak Resident Size: \(String(format: "%.2f", Double(analysis.peakResidentSize) / 1024.0 / 1024.0)) MB")
        print("Memory Growth: \(String(format: "%.2f", Double(analysis.memoryGrowth) / 1024.0 / 1024.0)) MB")
        print("Duration: \(String(format: "%.1f", analysis.duration))s")
    }
}

// MARK: - Profiling Session

private class ProfilingSession {
    private let database: Database
    private let command: String
    private let debugTools: DebugTools
    private var startTime: CFAbsoluteTime?
    private var startMemory: MemoryAnalysis?
    private var endTime: CFAbsoluteTime?
    private var endMemory: MemoryAnalysis?
    private var success: Bool = false
    private var error: Error?
    
    init(database: Database, command: String) {
        self.database = database
        self.command = command
        self.debugTools = DebugTools(database: database)
    }
    
    func start() {
        startTime = CFAbsoluteTimeGetCurrent()
        startMemory = debugTools.analyzeMemory()
    }
    
    func stop() {
        endTime = CFAbsoluteTimeGetCurrent()
        endMemory = debugTools.analyzeMemory()
    }
    
    func getResults() -> ProfilingResults {
        let totalDuration = (endTime ?? CFAbsoluteTimeGetCurrent()) - (startTime ?? 0)
        let memoryDelta = Int64((endMemory?.residentSize ?? 0) - (startMemory?.residentSize ?? 0))
        
        return ProfilingResults(
            command: command,
            totalDuration: totalDuration,
            memoryDelta: memoryDelta,
            success: success,
            error: error,
            timestamp: Date()
        )
    }
}

private struct ProfilingResults {
    let command: String
    let totalDuration: TimeInterval
    let memoryDelta: Int64
    let success: Bool
    let error: Error?
    let timestamp: Date
}
