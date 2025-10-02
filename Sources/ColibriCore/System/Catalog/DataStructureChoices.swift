//
//  DataStructureChoices.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Data structure choices persistence for the catalog system.

import Foundation
import os.log

// MARK: - Data Structure Choice

/// Represents a data structure choice made by the system
public struct DataStructureChoice {
    public let id: UUID
    public let objectType: DataStructureObjectType
    public let objectId: UUID
    public let objectName: String
    public let database: String
    public let chosenStructure: DataStructureType
    public let reason: ChoiceReason
    public let performanceMetrics: DataStructurePerformanceMetrics
    public let configuration: DataStructureConfiguration
    public let alternatives: [DataStructureAlternative]
    public let chosen: Date
    public let lastEvaluated: Date
    public let status: ChoiceStatus
    
    public init(id: UUID, objectType: DataStructureObjectType, objectId: UUID, objectName: String, 
                database: String, chosenStructure: DataStructureType, reason: ChoiceReason, 
                performanceMetrics: DataStructurePerformanceMetrics, configuration: DataStructureConfiguration, 
                alternatives: [DataStructureAlternative] = [], chosen: Date, lastEvaluated: Date, 
                status: ChoiceStatus) {
        self.id = id
        self.objectType = objectType
        self.objectId = objectId
        self.objectName = objectName
        self.database = database
        self.chosenStructure = chosenStructure
        self.reason = reason
        self.performanceMetrics = performanceMetrics
        self.configuration = configuration
        self.alternatives = alternatives
        self.chosen = chosen
        self.lastEvaluated = lastEvaluated
        self.status = status
    }
}

public enum DataStructureObjectType: String, CaseIterable {
    case table = "TABLE"
    case index = "INDEX"
    case view = "VIEW"
    case sequence = "SEQUENCE"
    case buffer = "BUFFER"
    case cache = "CACHE"
    case log = "LOG"
    case checkpoint = "CHECKPOINT"
}

public enum DataStructureType: String, CaseIterable {
    case btree = "BTREE"
    case art = "ART"
    case lsm = "LSM"
    case hash = "HASH"
    case skipList = "SKIPLIST"
    case fractalTree = "FRACTALTREE"
    case heap = "HEAP"
    case array = "ARRAY"
    case linkedList = "LINKEDLIST"
    case redBlackTree = "REDBLACKTREE"
    case avlTree = "AVLTREE"
    case splayTree = "SPLAYTREE"
    case treap = "TREAP"
    case bPlusTree = "BPLUSTREE"
    case bStarTree = "BSTARTREE"
    case rTree = "RTREE"
    case quadTree = "QUADTREE"
    case kdTree = "KDTREE"
    case trie = "TRIE"
    case suffixTree = "SUFFIXTREE"
    case segmentTree = "SEGMENTTREE"
    case fenwickTree = "FENWICKTREE"
    case sparseTable = "SPARSETABLE"
    case disjointSet = "DISJOINTSET"
    case bloomFilter = "BLOOMFILTER"
    case cuckooFilter = "CUCKOOFILTER"
    case countMinSketch = "COUNTMINSKETCH"
    case hyperLogLog = "HYPERLOGLOG"
}

public enum ChoiceReason: String, CaseIterable {
    case performance = "PERFORMANCE"
    case memoryEfficiency = "MEMORY_EFFICIENCY"
    case concurrency = "CONCURRENCY"
    case durability = "DURABILITY"
    case consistency = "CONSISTENCY"
    case scalability = "SCALABILITY"
    case maintenance = "MAINTENANCE"
    case compatibility = "COMPATIBILITY"
    case userPreference = "USER_PREFERENCE"
    case systemDefault = "SYSTEM_DEFAULT"
    case workloadOptimization = "WORKLOAD_OPTIMIZATION"
    case dataCharacteristics = "DATA_CHARACTERISTICS"
    case accessPattern = "ACCESS_PATTERN"
    case sizeConstraints = "SIZE_CONSTRAINTS"
    case latencyRequirements = "LATENCY_REQUIREMENTS"
    case throughputRequirements = "THROUGHPUT_REQUIREMENTS"
}

public enum ChoiceStatus: String, CaseIterable {
    case active = "ACTIVE"
    case deprecated = "DEPRECATED"
    case replaced = "REPLACED"
    case experimental = "EXPERIMENTAL"
    case underEvaluation = "UNDER_EVALUATION"
    case failed = "FAILED"
}

// MARK: - Performance Metrics

/// Represents performance metrics for data structure evaluation
public struct DataStructurePerformanceMetrics {
    public let insertTime: TimeInterval
    public let deleteTime: TimeInterval
    public let searchTime: TimeInterval
    public let updateTime: TimeInterval
    public let scanTime: TimeInterval
    public let memoryUsage: UInt64
    public let diskUsage: UInt64
    public let cacheHitRatio: Double
    public let concurrencyScore: Double
    public let durabilityScore: Double
    public let consistencyScore: Double
    public let scalabilityScore: Double
    public let maintenanceScore: Double
    public let overallScore: Double
    public let measuredAt: Date
    
    public init(insertTime: TimeInterval, deleteTime: TimeInterval, searchTime: TimeInterval, 
                updateTime: TimeInterval, scanTime: TimeInterval, memoryUsage: UInt64, 
                diskUsage: UInt64, cacheHitRatio: Double, concurrencyScore: Double, 
                durabilityScore: Double, consistencyScore: Double, scalabilityScore: Double, 
                maintenanceScore: Double, overallScore: Double, measuredAt: Date) {
        self.insertTime = insertTime
        self.deleteTime = deleteTime
        self.searchTime = searchTime
        self.updateTime = updateTime
        self.scanTime = scanTime
        self.memoryUsage = memoryUsage
        self.diskUsage = diskUsage
        self.cacheHitRatio = cacheHitRatio
        self.concurrencyScore = concurrencyScore
        self.durabilityScore = durabilityScore
        self.consistencyScore = consistencyScore
        self.scalabilityScore = scalabilityScore
        self.maintenanceScore = maintenanceScore
        self.overallScore = overallScore
        self.measuredAt = measuredAt
    }
}

// MARK: - Data Structure Configuration

/// Represents configuration for a data structure
public struct DataStructureConfiguration {
    public let parameters: [String: Any]
    public let tuningSettings: TuningSettings
    public let optimizationFlags: OptimizationFlags
    public let memorySettings: DataStructureMemorySettings
    public let concurrencySettings: ConcurrencySettings
    public let durabilitySettings: DurabilitySettings
    
    public init(parameters: [String: Any] = [:], tuningSettings: TuningSettings, 
                optimizationFlags: OptimizationFlags, memorySettings: DataStructureMemorySettings, 
                concurrencySettings: ConcurrencySettings, durabilitySettings: DurabilitySettings) {
        self.parameters = parameters
        self.tuningSettings = tuningSettings
        self.optimizationFlags = optimizationFlags
        self.memorySettings = memorySettings
        self.concurrencySettings = concurrencySettings
        self.durabilitySettings = durabilitySettings
    }
}

// MARK: - Tuning Settings

/// Represents tuning settings for data structures
public struct TuningSettings {
    public let pageSize: UInt32
    public let fillFactor: Double
    public let splitThreshold: Double
    public let mergeThreshold: Double
    public let rebalanceThreshold: Double
    public let compressionLevel: Int
    public let bloomFilterBits: Int
    public let cacheSize: UInt64
    public let bufferSize: UInt64
    public let batchSize: UInt32
    
    public init(pageSize: UInt32 = 8192, fillFactor: Double = 0.75, splitThreshold: Double = 0.9, 
                mergeThreshold: Double = 0.3, rebalanceThreshold: Double = 0.6, 
                compressionLevel: Int = 6, bloomFilterBits: Int = 10, cacheSize: UInt64 = 1024 * 1024, 
                bufferSize: UInt64 = 64 * 1024, batchSize: UInt32 = 1000) {
        self.pageSize = pageSize
        self.fillFactor = fillFactor
        self.splitThreshold = splitThreshold
        self.mergeThreshold = mergeThreshold
        self.rebalanceThreshold = rebalanceThreshold
        self.compressionLevel = compressionLevel
        self.bloomFilterBits = bloomFilterBits
        self.cacheSize = cacheSize
        self.bufferSize = bufferSize
        self.batchSize = batchSize
    }
}

// MARK: - Optimization Flags

/// Represents optimization flags for data structures
public struct OptimizationFlags {
    public let enableCompression: Bool
    public let enableDeduplication: Bool
    public let enableCaching: Bool
    public let enablePrefetching: Bool
    public let enableParallelism: Bool
    public let enableVectorization: Bool
    public let enableSIMD: Bool
    public let enableMemoryMapping: Bool
    public let enableLockFree: Bool
    public let enableLockElision: Bool
    
    public init(enableCompression: Bool = true, enableDeduplication: Bool = false, 
                enableCaching: Bool = true, enablePrefetching: Bool = true, 
                enableParallelism: Bool = true, enableVectorization: Bool = false, 
                enableSIMD: Bool = false, enableMemoryMapping: Bool = false, 
                enableLockFree: Bool = false, enableLockElision: Bool = false) {
        self.enableCompression = enableCompression
        self.enableDeduplication = enableDeduplication
        self.enableCaching = enableCaching
        self.enablePrefetching = enablePrefetching
        self.enableParallelism = enableParallelism
        self.enableVectorization = enableVectorization
        self.enableSIMD = enableSIMD
        self.enableMemoryMapping = enableMemoryMapping
        self.enableLockFree = enableLockFree
        self.enableLockElision = enableLockElision
    }
}

// MARK: - Memory Settings

/// Represents memory settings for data structures
public struct DataStructureMemorySettings {
    public let maxMemoryBytes: UInt64
    public let allocationStrategy: AllocationStrategy
    public let garbageCollection: GarbageCollectionSettings
    public let memoryPool: MemoryPoolSettings
    public let alignment: UInt32
    public let prefetchDistance: UInt32
    
    public init(maxMemoryBytes: UInt64, allocationStrategy: AllocationStrategy, 
                garbageCollection: GarbageCollectionSettings, memoryPool: MemoryPoolSettings, 
                alignment: UInt32 = 8, prefetchDistance: UInt32 = 64) {
        self.maxMemoryBytes = maxMemoryBytes
        self.allocationStrategy = allocationStrategy
        self.garbageCollection = garbageCollection
        self.memoryPool = memoryPool
        self.alignment = alignment
        self.prefetchDistance = prefetchDistance
    }
}

public enum AllocationStrategy: String, CaseIterable {
    case firstFit = "FIRST_FIT"
    case bestFit = "BEST_FIT"
    case worstFit = "WORST_FIT"
    case buddy = "BUDDY"
    case slab = "SLAB"
    case pool = "POOL"
    case stack = "STACK"
    case heap = "HEAP"
}

// MARK: - Garbage Collection Settings

/// Represents garbage collection settings
public struct GarbageCollectionSettings {
    public let enabled: Bool
    public let algorithm: GCAlgorithm
    public let threshold: Double
    public let interval: TimeInterval
    public let concurrent: Bool
    public let incremental: Bool
    public let generational: Bool
    
    public init(enabled: Bool = true, algorithm: GCAlgorithm = .markAndSweep, 
                threshold: Double = 0.8, interval: TimeInterval = 60, concurrent: Bool = true, 
                incremental: Bool = true, generational: Bool = true) {
        self.enabled = enabled
        self.algorithm = algorithm
        self.threshold = threshold
        self.interval = interval
        self.concurrent = concurrent
        self.incremental = incremental
        self.generational = generational
    }
}

public enum GCAlgorithm: String, CaseIterable {
    case markAndSweep = "MARK_AND_SWEEP"
    case markAndCompact = "MARK_AND_COMPACT"
    case copying = "COPYING"
    case referenceCounting = "REFERENCE_COUNTING"
    case generational = "GENERATIONAL"
    case concurrent = "CONCURRENT"
    case incremental = "INCREMENTAL"
}

// MARK: - Memory Pool Settings

/// Represents memory pool settings
public struct MemoryPoolSettings {
    public let enabled: Bool
    public let poolSize: UInt64
    public let blockSize: UInt32
    public let maxBlocks: UInt32
    public let growthFactor: Double
    public let shrinkThreshold: Double
    
    public init(enabled: Bool = true, poolSize: UInt64 = 1024 * 1024, blockSize: UInt32 = 4096, 
                maxBlocks: UInt32 = 1000, growthFactor: Double = 1.5, 
                shrinkThreshold: Double = 0.3) {
        self.enabled = enabled
        self.poolSize = poolSize
        self.blockSize = blockSize
        self.maxBlocks = maxBlocks
        self.growthFactor = growthFactor
        self.shrinkThreshold = shrinkThreshold
    }
}

// MARK: - Concurrency Settings

/// Represents concurrency settings for data structures
public struct ConcurrencySettings {
    public let lockingStrategy: LockingStrategy
    public let isolationLevel: DataStructureIsolationLevel
    public let deadlockDetection: Bool
    public let lockTimeout: TimeInterval
    public let maxLocks: UInt32
    public let lockEscalation: Bool
    public let lockUpgrade: Bool
    public let lockDowngrade: Bool
    
    public init(lockingStrategy: LockingStrategy = .twoPhase, 
                isolationLevel: DataStructureIsolationLevel = .readCommitted, deadlockDetection: Bool = true, 
                lockTimeout: TimeInterval = 30, maxLocks: UInt32 = 10000, 
                lockEscalation: Bool = true, lockUpgrade: Bool = true, 
                lockDowngrade: Bool = true) {
        self.lockingStrategy = lockingStrategy
        self.isolationLevel = isolationLevel
        self.deadlockDetection = deadlockDetection
        self.lockTimeout = lockTimeout
        self.maxLocks = maxLocks
        self.lockEscalation = lockEscalation
        self.lockUpgrade = lockUpgrade
        self.lockDowngrade = lockDowngrade
    }
}

public enum LockingStrategy: String, CaseIterable {
    case twoPhase = "TWO_PHASE"
    case optimistic = "OPTIMISTIC"
    case pessimistic = "PESSIMISTIC"
    case hybrid = "HYBRID"
    case lockFree = "LOCK_FREE"
    case softwareTransactionalMemory = "STM"
    case hardwareTransactionalMemory = "HTM"
}

public enum DataStructureIsolationLevel: String, CaseIterable {
    case readUncommitted = "READ_UNCOMMITTED"
    case readCommitted = "READ_COMMITTED"
    case repeatableRead = "REPEATABLE_READ"
    case serializable = "SERIALIZABLE"
    case snapshot = "SNAPSHOT"
}

// MARK: - Durability Settings

/// Represents durability settings for data structures
public struct DurabilitySettings {
    public let writeAheadLog: Bool
    public let checkpointInterval: TimeInterval
    public let syncMode: SyncMode
    public let fsync: Bool
    public let checksum: Bool
    public let compression: Bool
    public let encryption: Bool
    public let replication: ReplicationSettings
    
    public init(writeAheadLog: Bool = true, checkpointInterval: TimeInterval = 300, 
                syncMode: SyncMode = .full, fsync: Bool = true, checksum: Bool = true, 
                compression: Bool = false, encryption: Bool = false, 
                replication: ReplicationSettings) {
        self.writeAheadLog = writeAheadLog
        self.checkpointInterval = checkpointInterval
        self.syncMode = syncMode
        self.fsync = fsync
        self.checksum = checksum
        self.compression = compression
        self.encryption = encryption
        self.replication = replication
    }
}

public enum SyncMode: String, CaseIterable {
    case off = "OFF"
    case normal = "NORMAL"
    case full = "FULL"
    case extra = "EXTRA"
}

// MARK: - Replication Settings

/// Represents replication settings
public struct ReplicationSettings {
    public let enabled: Bool
    public let factor: UInt32
    public let strategy: ReplicationStrategy
    public let consistency: ConsistencyLevel
    public let timeout: TimeInterval
    public let retryCount: UInt32
    
    public init(enabled: Bool = false, factor: UInt32 = 3, 
                strategy: ReplicationStrategy = .synchronous, 
                consistency: ConsistencyLevel = .strong, timeout: TimeInterval = 5, 
                retryCount: UInt32 = 3) {
        self.enabled = enabled
        self.factor = factor
        self.strategy = strategy
        self.consistency = consistency
        self.timeout = timeout
        self.retryCount = retryCount
    }
}

public enum ReplicationStrategy: String, CaseIterable {
    case synchronous = "SYNCHRONOUS"
    case asynchronous = "ASYNCHRONOUS"
    case semiSynchronous = "SEMI_SYNCHRONOUS"
    case eventual = "EVENTUAL"
}

public enum ConsistencyLevel: String, CaseIterable {
    case eventual = "EVENTUAL"
    case weak = "WEAK"
    case strong = "STRONG"
    case strict = "STRICT"
}

// MARK: - Data Structure Alternative

/// Represents an alternative data structure that was considered
public struct DataStructureAlternative {
    public let structureType: DataStructureType
    public let performanceMetrics: DataStructurePerformanceMetrics
    public let configuration: DataStructureConfiguration
    public let score: Double
    public let reason: String
    
    public init(structureType: DataStructureType, performanceMetrics: DataStructurePerformanceMetrics, 
                configuration: DataStructureConfiguration, score: Double, reason: String) {
        self.structureType = structureType
        self.performanceMetrics = performanceMetrics
        self.configuration = configuration
        self.score = score
        self.reason = reason
    }
}

// MARK: - Data Structure Choice Manager

/// Manages data structure choices in the catalog
public class DataStructureChoiceManager {
    private let database: Database
    private let logger = Logger(subsystem: "com.colibridb.catalog", category: "datastructure")
    
    public init(database: Database) {
        self.database = database
    }
    
    // MARK: - Choice Management
    
    /// Records a data structure choice
    public func recordChoice(_ choice: DataStructureChoice) throws {
        logger.info("Recording data structure choice: \(choice.chosenStructure.rawValue) for \(choice.objectName)")
        // Implementation would insert into data structure choices table
    }
    
    /// Gets data structure choices for an object
    public func getChoices(for objectId: UUID) throws -> [DataStructureChoice] {
        // Implementation would query data structure choices table
        return []
    }
    
    /// Gets data structure choices by type
    public func getChoices(by structureType: DataStructureType) throws -> [DataStructureChoice] {
        // Implementation would query data structure choices table
        return []
    }
    
    /// Updates a data structure choice
    public func updateChoice(_ choice: DataStructureChoice) throws {
        logger.info("Updating data structure choice: \(choice.id)")
        // Implementation would update data structure choices table
    }
    
    /// Deletes a data structure choice
    public func deleteChoice(_ choiceId: UUID) throws {
        logger.info("Deleting data structure choice: \(choiceId)")
        // Implementation would delete from data structure choices table
    }
    
    // MARK: - Evaluation
    
    /// Evaluates data structure choices for an object
    public func evaluateChoices(for objectId: UUID, objectType: DataStructureObjectType, 
                               workload: WorkloadProfile) throws -> [DataStructureChoice] {
        logger.info("Evaluating data structure choices for object: \(objectId)")
        // Implementation would evaluate different data structures
        return []
    }
    
    /// Recommends data structure for an object
    public func recommendDataStructure(for objectId: UUID, objectType: DataStructureObjectType, 
                                     workload: WorkloadProfile) throws -> DataStructureChoice? {
        logger.info("Recommending data structure for object: \(objectId)")
        // Implementation would recommend best data structure
        return nil
    }
    
    // MARK: - Analysis
    
    /// Analyzes data structure performance
    public func analyzePerformance(_ choiceId: UUID) throws -> PerformanceAnalysis {
        logger.info("Analyzing performance for choice: \(choiceId)")
        // Implementation would analyze performance
        return PerformanceAnalysis(choiceId: choiceId, metrics: DataStructurePerformanceMetrics(
            insertTime: 0, deleteTime: 0, searchTime: 0, updateTime: 0, scanTime: 0,
            memoryUsage: 0, diskUsage: 0, cacheHitRatio: 0, concurrencyScore: 0,
            durabilityScore: 0, consistencyScore: 0, scalabilityScore: 0,
            maintenanceScore: 0, overallScore: 0, measuredAt: Date()
        ), recommendations: [], bottlenecks: [], optimizationOpportunities: [], analyzedAt: Date())
    }
    
    /// Gets data structure statistics
    public func getDataStructureStatistics() throws -> DataStructureStatistics {
        logger.info("Getting data structure statistics")
        // Implementation would calculate statistics
        return DataStructureStatistics(
            totalChoices: 0,
            structureTypeCounts: [:],
            averagePerformance: DataStructurePerformanceMetrics(
                insertTime: 0, deleteTime: 0, searchTime: 0, updateTime: 0, scanTime: 0,
                memoryUsage: 0, diskUsage: 0, cacheHitRatio: 0, concurrencyScore: 0,
                durabilityScore: 0, consistencyScore: 0, scalabilityScore: 0,
                maintenanceScore: 0, overallScore: 0, measuredAt: Date()
            ),
            lastUpdated: Date()
        )
    }
}

// MARK: - Workload Profile

/// Represents a workload profile for data structure evaluation
public struct WorkloadProfile {
    public let readRatio: Double
    public let writeRatio: Double
    public let updateRatio: Double
    public let deleteRatio: Double
    public let scanRatio: Double
    public let pointQueryRatio: Double
    public let rangeQueryRatio: Double
    public let concurrentUsers: UInt32
    public let dataSize: UInt64
    public let growthRate: Double
    public let accessPattern: AccessPattern
    public let consistencyRequirements: ConsistencyLevel
    public let latencyRequirements: LatencyRequirements
    public let throughputRequirements: ThroughputRequirements
    
    public init(readRatio: Double, writeRatio: Double, updateRatio: Double, deleteRatio: Double, 
                scanRatio: Double, pointQueryRatio: Double, rangeQueryRatio: Double, 
                concurrentUsers: UInt32, dataSize: UInt64, growthRate: Double, 
                accessPattern: AccessPattern, consistencyRequirements: ConsistencyLevel, 
                latencyRequirements: LatencyRequirements, throughputRequirements: ThroughputRequirements) {
        self.readRatio = readRatio
        self.writeRatio = writeRatio
        self.updateRatio = updateRatio
        self.deleteRatio = deleteRatio
        self.scanRatio = scanRatio
        self.pointQueryRatio = pointQueryRatio
        self.rangeQueryRatio = rangeQueryRatio
        self.concurrentUsers = concurrentUsers
        self.dataSize = dataSize
        self.growthRate = growthRate
        self.accessPattern = accessPattern
        self.consistencyRequirements = consistencyRequirements
        self.latencyRequirements = latencyRequirements
        self.throughputRequirements = throughputRequirements
    }
}

public enum AccessPattern: String, CaseIterable {
    case random = "RANDOM"
    case sequential = "SEQUENTIAL"
    case clustered = "CLUSTERED"
    case skewed = "SKEWED"
    case uniform = "UNIFORM"
    case hotSpot = "HOT_SPOT"
    case temporal = "TEMPORAL"
    case spatial = "SPATIAL"
}

// MARK: - Latency Requirements

/// Represents latency requirements
public struct LatencyRequirements {
    public let maxReadLatency: TimeInterval
    public let maxWriteLatency: TimeInterval
    public let maxUpdateLatency: TimeInterval
    public let maxDeleteLatency: TimeInterval
    public let maxScanLatency: TimeInterval
    public let p99ReadLatency: TimeInterval
    public let p99WriteLatency: TimeInterval
    
    public init(maxReadLatency: TimeInterval, maxWriteLatency: TimeInterval, 
                maxUpdateLatency: TimeInterval, maxDeleteLatency: TimeInterval, 
                maxScanLatency: TimeInterval, p99ReadLatency: TimeInterval, 
                p99WriteLatency: TimeInterval) {
        self.maxReadLatency = maxReadLatency
        self.maxWriteLatency = maxWriteLatency
        self.maxUpdateLatency = maxUpdateLatency
        self.maxDeleteLatency = maxDeleteLatency
        self.maxScanLatency = maxScanLatency
        self.p99ReadLatency = p99ReadLatency
        self.p99WriteLatency = p99WriteLatency
    }
}

// MARK: - Throughput Requirements

/// Represents throughput requirements
public struct ThroughputRequirements {
    public let minReadsPerSecond: UInt64
    public let minWritesPerSecond: UInt64
    public let minUpdatesPerSecond: UInt64
    public let minDeletesPerSecond: UInt64
    public let minScansPerSecond: UInt64
    public let peakReadsPerSecond: UInt64
    public let peakWritesPerSecond: UInt64
    
    public init(minReadsPerSecond: UInt64, minWritesPerSecond: UInt64, 
                minUpdatesPerSecond: UInt64, minDeletesPerSecond: UInt64, 
                minScansPerSecond: UInt64, peakReadsPerSecond: UInt64, 
                peakWritesPerSecond: UInt64) {
        self.minReadsPerSecond = minReadsPerSecond
        self.minWritesPerSecond = minWritesPerSecond
        self.minUpdatesPerSecond = minUpdatesPerSecond
        self.minDeletesPerSecond = minDeletesPerSecond
        self.minScansPerSecond = minScansPerSecond
        self.peakReadsPerSecond = peakReadsPerSecond
        self.peakWritesPerSecond = peakWritesPerSecond
    }
}

// MARK: - Performance Analysis

/// Represents performance analysis results
public struct PerformanceAnalysis {
    public let choiceId: UUID
    public let metrics: DataStructurePerformanceMetrics
    public let recommendations: [PerformanceRecommendation]
    public let bottlenecks: [Bottleneck]
    public let optimizationOpportunities: [OptimizationOpportunity]
    public let analyzedAt: Date
    
    public init(choiceId: UUID, metrics: DataStructurePerformanceMetrics, 
                recommendations: [PerformanceRecommendation], bottlenecks: [Bottleneck], 
                optimizationOpportunities: [OptimizationOpportunity], analyzedAt: Date) {
        self.choiceId = choiceId
        self.metrics = metrics
        self.recommendations = recommendations
        self.bottlenecks = bottlenecks
        self.optimizationOpportunities = optimizationOpportunities
        self.analyzedAt = analyzedAt
    }
}

// MARK: - Performance Recommendation

/// Represents a performance recommendation
public struct PerformanceRecommendation {
    public let type: RecommendationType
    public let priority: RecommendationPriority
    public let message: String
    public let expectedImprovement: Double
    public let implementation: String
    
    public init(type: RecommendationType, priority: RecommendationPriority, message: String, 
                expectedImprovement: Double, implementation: String) {
        self.type = type
        self.priority = priority
        self.message = message
        self.expectedImprovement = expectedImprovement
        self.implementation = implementation
    }
}

// MARK: - Bottleneck

/// Represents a performance bottleneck
public struct Bottleneck {
    public let type: BottleneckType
    public let severity: BottleneckSeverity
    public let description: String
    public let impact: Double
    public let solution: String
    
    public init(type: BottleneckType, severity: BottleneckSeverity, description: String, 
                impact: Double, solution: String) {
        self.type = type
        self.severity = severity
        self.description = description
        self.impact = impact
        self.solution = solution
    }
}

public enum BottleneckType: String, CaseIterable {
    case cpu = "CPU"
    case memory = "MEMORY"
    case disk = "DISK"
    case network = "NETWORK"
    case locking = "LOCKING"
    case contention = "CONTENTION"
    case algorithm = "ALGORITHM"
    case dataStructure = "DATA_STRUCTURE"
    case configuration = "CONFIGURATION"
}

public enum BottleneckSeverity: String, CaseIterable {
    case low = "LOW"
    case medium = "MEDIUM"
    case high = "HIGH"
    case critical = "CRITICAL"
}

// MARK: - Optimization Opportunity

/// Represents an optimization opportunity
public struct OptimizationOpportunity {
    public let type: OptimizationType
    public let potentialGain: Double
    public let effort: EffortLevel
    public let description: String
    public let implementation: String
    
    public init(type: OptimizationType, potentialGain: Double, effort: EffortLevel, 
                description: String, implementation: String) {
        self.type = type
        self.potentialGain = potentialGain
        self.effort = effort
        self.description = description
        self.implementation = implementation
    }
}

public enum OptimizationType: String, CaseIterable {
    case algorithm = "ALGORITHM"
    case dataStructure = "DATA_STRUCTURE"
    case memory = "MEMORY"
    case concurrency = "CONCURRENCY"
    case caching = "CACHING"
    case compression = "COMPRESSION"
    case indexing = "INDEXING"
    case partitioning = "PARTITIONING"
    case configuration = "CONFIGURATION"
}

public enum EffortLevel: String, CaseIterable {
    case low = "LOW"
    case medium = "MEDIUM"
    case high = "HIGH"
    case veryHigh = "VERY_HIGH"
}

// MARK: - Data Structure Statistics

/// Represents data structure statistics
public struct DataStructureStatistics {
    public let totalChoices: UInt64
    public let structureTypeCounts: [DataStructureType: UInt64]
    public let averagePerformance: DataStructurePerformanceMetrics
    public let lastUpdated: Date
    
    public init(totalChoices: UInt64, structureTypeCounts: [DataStructureType: UInt64], 
                averagePerformance: DataStructurePerformanceMetrics, lastUpdated: Date) {
        self.totalChoices = totalChoices
        self.structureTypeCounts = structureTypeCounts
        self.averagePerformance = averagePerformance
        self.lastUpdated = lastUpdated
    }
}
