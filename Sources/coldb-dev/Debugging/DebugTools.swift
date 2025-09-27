//
//  DebugTools.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Advanced debugging tools for development CLI.

import Foundation
import ColibriCore
import os.log

/// Advanced debugging tools for ColibrìDB development
public class DebugTools {
    private let database: Database
    private let logger = Logger(subsystem: "com.colibridb.debug", category: "tools")
    
    public init(database: Database) {
        self.database = database
    }
    
    // MARK: - Memory Analysis
    
    /// Analyzes memory usage and provides detailed statistics
    public func analyzeMemory() -> MemoryAnalysis {
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
            return MemoryAnalysis(
                residentSize: memoryInfo.resident_size,
                virtualSize: memoryInfo.virtual_size,
                peakResidentSize: memoryInfo.resident_size_max,
                timestamp: Date()
            )
        } else {
            logger.error("Failed to get memory info: \(kerr)")
            return MemoryAnalysis(
                residentSize: 0,
                virtualSize: 0,
                peakResidentSize: 0,
                timestamp: Date()
            )
        }
    }
    
    /// Monitors memory usage over time
    public func startMemoryMonitoring(interval: TimeInterval = 1.0, duration: TimeInterval = 60.0) -> MemoryMonitor {
        return MemoryMonitor(database: database, interval: interval, duration: duration)
    }
    
    // MARK: - Performance Analysis
    
    /// Analyzes database performance metrics
    public func analyzePerformance() -> PerformanceAnalysis {
        let bufferStats = database.bufferPoolAggregateNumbers()
        _ = database.vacuumStats()
        
        return PerformanceAnalysis(
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
            vacuumLastRun: database.vacuumLastRun,
            timestamp: Date()
        )
    }
    
    /// Profiles a specific operation
    public func profileOperation<T>(_ operation: () throws -> T, name: String) throws -> ProfilingResult<T> {
        let startTime = CFAbsoluteTimeGetCurrent()
        let startMemory = analyzeMemory()
        
        let result: T
        do {
            result = try operation()
        } catch {
            let endTime = CFAbsoluteTimeGetCurrent()
            let endMemory = analyzeMemory()
            
            return ProfilingResult(
                name: name,
                duration: endTime - startTime,
                memoryDelta: Int64(endMemory.residentSize - startMemory.residentSize),
                success: false,
                error: error,
                result: nil,
                timestamp: Date()
            )
        }
        
        let endTime = CFAbsoluteTimeGetCurrent()
        let endMemory = analyzeMemory()
        
        return ProfilingResult(
            name: name,
            duration: endTime - startTime,
            memoryDelta: Int64(endMemory.residentSize - startMemory.residentSize),
            success: true,
            error: nil,
            result: result,
            timestamp: Date()
        )
    }
    
    // MARK: - Constraint Analysis
    
    /// Analyzes constraint validation performance
    public func analyzeConstraints() -> ConstraintAnalysis {
        let tables = database.listTables()
        var totalConstraints = 0
        var constraintTypes: [String: Int] = [:]
        var validationTimes: [String: TimeInterval] = [:]
        
        for table in tables {
            let constraints = database.constraintManager.getConstraints(for: table)
            totalConstraints += constraints.count
            
            for constraint in constraints {
                let type = String(describing: type(of: constraint))
                constraintTypes[type, default: 0] += 1
                
                // Measure validation time
                let startTime = CFAbsoluteTimeGetCurrent()
                do {
                    _ = try database.constraintManager.validateTable(table, rows: [])
                } catch {
                    // Continue even if validation fails
                }
                let endTime = CFAbsoluteTimeGetCurrent()
                validationTimes[constraint.name] = endTime - startTime
            }
        }
        
        return ConstraintAnalysis(
            totalConstraints: totalConstraints,
            constraintTypes: constraintTypes,
            validationTimes: validationTimes,
            tables: tables,
            timestamp: Date()
        )
    }
    
    // MARK: - SQL Analysis
    
    /// Analyzes SQL parsing and execution
    public func analyzeSQL(_ sql: String) -> SQLAnalysis {
        let startTime = CFAbsoluteTimeGetCurrent()
        
        do {
            let parser = SimpleSQLParser(sql: sql)
            let statement = try parser.parse()
            let parseTime = CFAbsoluteTimeGetCurrent() - startTime
            
            let execStartTime = CFAbsoluteTimeGetCurrent()
            let executor = SimpleSQLExecutor(database: database)
            let result = try executor.execute(statement)
            let execTime = CFAbsoluteTimeGetCurrent() - execStartTime
            
            return SQLAnalysis(
                sql: sql,
                parseTime: parseTime,
                executionTime: execTime,
                totalTime: CFAbsoluteTimeGetCurrent() - startTime,
                success: true,
                error: nil,
                resultType: String(describing: type(of: result)),
                timestamp: Date()
            )
        } catch {
            return SQLAnalysis(
                sql: sql,
                parseTime: CFAbsoluteTimeGetCurrent() - startTime,
                executionTime: 0,
                totalTime: CFAbsoluteTimeGetCurrent() - startTime,
                success: false,
                error: error,
                resultType: nil,
                timestamp: Date()
            )
        }
    }
    
    // MARK: - Type System Analysis
    
    /// Analyzes data type usage and conversions
    public func analyzeTypeSystem() -> TypeSystemAnalysis {
        let tables = database.listTables()
        var typeUsage: [String: Int] = [:]
        let conversionErrors: [String: Int] = [:]
        
        for table in tables {
            do {
                let rows = try database.scan(table)
                for (_, row) in rows {
                    for (_, value) in row {
                        let typeName = String(describing: type(of: value))
                        typeUsage[typeName, default: 0] += 1
                    }
                }
            } catch {
                // Continue with other tables
            }
        }
        
        return TypeSystemAnalysis(
            typeUsage: typeUsage,
            conversionErrors: conversionErrors,
            tables: tables,
            timestamp: Date()
        )
    }
}

// MARK: - Data Structures

public struct MemoryAnalysis {
    public let residentSize: UInt64
    public let virtualSize: UInt64
    public let peakResidentSize: UInt64
    public let timestamp: Date
    
    public var residentSizeMB: Double {
        return Double(residentSize) / 1024.0 / 1024.0
    }
    
    public var virtualSizeMB: Double {
        return Double(virtualSize) / 1024.0 / 1024.0
    }
}

public struct PerformanceAnalysis {
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
    public let vacuumLastRun: Date?
    public let timestamp: Date
}

public struct ProfilingResult<T> {
    public let name: String
    public let duration: TimeInterval
    public let memoryDelta: Int64
    public let success: Bool
    public let error: Error?
    public let result: T?
    public let timestamp: Date
}

public struct ConstraintAnalysis {
    public let totalConstraints: Int
    public let constraintTypes: [String: Int]
    public let validationTimes: [String: TimeInterval]
    public let tables: [String]
    public let timestamp: Date
}

public struct SQLAnalysis {
    public let sql: String
    public let parseTime: TimeInterval
    public let executionTime: TimeInterval
    public let totalTime: TimeInterval
    public let success: Bool
    public let error: Error?
    public let resultType: String?
    public let timestamp: Date
}

public struct TypeSystemAnalysis {
    public let typeUsage: [String: Int]
    public let conversionErrors: [String: Int]
    public let tables: [String]
    public let timestamp: Date
}

// MARK: - Memory Monitor

public class MemoryMonitor {
    private let database: Database
    private let interval: TimeInterval
    private let duration: TimeInterval
    private var timer: Timer?
    private var samples: [MemoryAnalysis] = []
    private let logger = Logger(subsystem: "com.colibridb.debug", category: "memory-monitor")
    
    public init(database: Database, interval: TimeInterval, duration: TimeInterval) {
        self.database = database
        self.interval = interval
        self.duration = duration
    }
    
    public func start() {
        logger.info("Starting memory monitoring for \(self.duration) seconds with \(self.interval)s intervals")
        
        timer = Timer.scheduledTimer(withTimeInterval: interval, repeats: true) { [weak self] _ in
            self?.takeSample()
        }
        
        // Stop after duration
        DispatchQueue.main.asyncAfter(deadline: .now() + duration) {
            self.stop()
        }
    }
    
    public func stop() {
        timer?.invalidate()
        timer = nil
        logger.info("Memory monitoring stopped. Collected \(self.samples.count) samples")
    }
    
    private func takeSample() {
        let debugTools = DebugTools(database: database)
        let analysis = debugTools.analyzeMemory()
        samples.append(analysis)
        
        logger.debug("Memory sample: \(analysis.residentSizeMB)MB resident, \(analysis.virtualSizeMB)MB virtual")
    }
    
    public func getAnalysis() -> MemoryMonitoringAnalysis {
        guard !samples.isEmpty else {
            return MemoryMonitoringAnalysis(
                samples: [],
                averageResidentSize: 0,
                peakResidentSize: 0,
                memoryGrowth: 0,
                duration: 0
            )
        }
        
        let averageResidentSize = samples.map { $0.residentSize }.reduce(0, +) / UInt64(samples.count)
        let peakResidentSize = samples.map { $0.residentSize }.max() ?? 0
        let memoryGrowth = (samples.last?.residentSize ?? 0) - (samples.first?.residentSize ?? 0)
        
        return MemoryMonitoringAnalysis(
            samples: samples,
            averageResidentSize: averageResidentSize,
            peakResidentSize: peakResidentSize,
            memoryGrowth: Int64(memoryGrowth),
            duration: duration
        )
    }
}

public struct MemoryMonitoringAnalysis {
    public let samples: [MemoryAnalysis]
    public let averageResidentSize: UInt64
    public let peakResidentSize: UInt64
    public let memoryGrowth: Int64
    public let duration: TimeInterval
}
