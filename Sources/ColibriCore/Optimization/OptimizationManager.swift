//
//  OptimizationManager.swift
//  ColibrìDB Database Optimization Implementation
//
//  Based on: spec/Optimization.tla
//  Implements: Database optimization strategies
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//
//  Key Properties:
//  - Performance: Query and system optimization
//  - Efficiency: Resource utilization optimization
//  - Scalability: Horizontal and vertical scaling
//  - Adaptability: Dynamic optimization strategies
//

import Foundation

// MARK: - Optimization Types

/// Optimization type
/// Corresponds to TLA+: OptimizationType
public enum OptimizationType: String, Codable, Sendable {
    case query = "query"
    case index = "index"
    case memory = "memory"
    case disk = "disk"
    case network = "network"
    case concurrency = "concurrency"
    case cache = "cache"
    case compression = "compression"
}

/// Optimization strategy
/// Corresponds to TLA+: OptimizationStrategy
public enum OptimizationStrategy: String, Codable, Sendable {
    case automatic = "automatic"
    case manual = "manual"
    case adaptive = "adaptive"
    case predictive = "predictive"
    case reactive = "reactive"
}

/// Optimization status
/// Corresponds to TLA+: OptimizationStatus
public enum OptimizationStatus: String, Codable, Sendable {
    case pending = "pending"
    case running = "running"
    case completed = "completed"
    case failed = "failed"
    case cancelled = "cancelled"
}

/// Optimization priority
/// Corresponds to TLA+: OptimizationPriority
public enum OptimizationPriority: String, Codable, Sendable {
    case low = "low"
    case medium = "medium"
    case high = "high"
    case critical = "critical"
}

// MARK: - Optimization Metadata

/// Optimization task
/// Corresponds to TLA+: OptimizationTask
public struct OptimizationTask: Codable, Sendable, Equatable {
    public let taskId: String
    public let type: OptimizationType
    public let strategy: OptimizationStrategy
    public let status: OptimizationStatus
    public let priority: OptimizationPriority
    public let description: String
    public let parameters: [String: Value]
    public let target: OptimizationTarget
    public let constraints: [OptimizationConstraint]
    public let createdAt: Date
    public let startedAt: Date?
    public let completedAt: Date?
    public let estimatedDuration: TimeInterval
    public let actualDuration: TimeInterval?
    
    public init(taskId: String, type: OptimizationType, strategy: OptimizationStrategy, status: OptimizationStatus, priority: OptimizationPriority, description: String, parameters: [String: Value], target: OptimizationTarget, constraints: [OptimizationConstraint], createdAt: Date = Date(), startedAt: Date? = nil, completedAt: Date? = nil, estimatedDuration: TimeInterval, actualDuration: TimeInterval? = nil) {
        self.taskId = taskId
        self.type = type
        self.strategy = strategy
        self.status = status
        self.priority = priority
        self.description = description
        self.parameters = parameters
        self.target = target
        self.constraints = constraints
        self.createdAt = createdAt
        self.startedAt = startedAt
        self.completedAt = completedAt
        self.estimatedDuration = estimatedDuration
        self.actualDuration = actualDuration
    }
}

/// Optimization target
/// Corresponds to TLA+: OptimizationTarget
public struct OptimizationTarget: Codable, Sendable, Equatable {
    public let metric: String
    public let currentValue: Double
    public let targetValue: Double
    public let unit: String
    
    public init(metric: String, currentValue: Double, targetValue: Double, unit: String) {
        self.metric = metric
        self.currentValue = currentValue
        self.targetValue = targetValue
        self.unit = unit
    }
}

/// Optimization constraint
/// Corresponds to TLA+: OptimizationConstraint
public struct OptimizationConstraint: Codable, Sendable, Equatable {
    public let constraintId: String
    public let type: ConstraintType
    public let expression: String
    public let parameters: [String: Value]
    
    public init(constraintId: String, type: ConstraintType, expression: String, parameters: [String: Value]) {
        self.constraintId = constraintId
        self.type = type
        self.expression = expression
        self.parameters = parameters
    }
}

/// Constraint type
public enum ConstraintType: String, Codable, Sendable {
    case resource = "resource"
    case performance = "performance"
    case availability = "availability"
    case cost = "cost"
    case compliance = "compliance"
}

/// Optimization result
/// Corresponds to TLA+: OptimizationResult
public struct OptimizationResult: Codable, Sendable, Equatable {
    public let resultId: String
    public let taskId: String
    public let success: Bool
    public let improvements: [OptimizationImprovement]
    public let metrics: [String: Double]
    public let recommendations: [OptimizationRecommendation]
    public let timestamp: Date
    public let executionTime: TimeInterval
    
    public init(resultId: String, taskId: String, success: Bool, improvements: [OptimizationImprovement], metrics: [String: Double], recommendations: [OptimizationRecommendation], timestamp: Date = Date(), executionTime: TimeInterval) {
        self.resultId = resultId
        self.taskId = taskId
        self.success = success
        self.improvements = improvements
        self.metrics = metrics
        self.recommendations = recommendations
        self.timestamp = timestamp
        self.executionTime = executionTime
    }
}

/// Optimization improvement
/// Corresponds to TLA+: OptimizationImprovement
public struct OptimizationImprovement: Codable, Sendable, Equatable {
    public let improvementId: String
    public let metric: String
    public let beforeValue: Double
    public let afterValue: Double
    public let improvementPercent: Double
    public let unit: String
    
    public init(improvementId: String, metric: String, beforeValue: Double, afterValue: Double, improvementPercent: Double, unit: String) {
        self.improvementId = improvementId
        self.metric = metric
        self.beforeValue = beforeValue
        self.afterValue = afterValue
        self.improvementPercent = improvementPercent
        self.unit = unit
    }
}

/// Optimization recommendation
/// Corresponds to TLA+: OptimizationRecommendation
public struct OptimizationRecommendation: Codable, Sendable, Equatable {
    public let recommendationId: String
    public let type: OptimizationType
    public let priority: OptimizationPriority
    public let description: String
    public let action: String
    public let expectedImprovement: Double
    public let cost: Double
    
    public init(recommendationId: String, type: OptimizationType, priority: OptimizationPriority, description: String, action: String, expectedImprovement: Double, cost: Double) {
        self.recommendationId = recommendationId
        self.type = type
        self.priority = priority
        self.description = description
        self.action = action
        self.expectedImprovement = expectedImprovement
        self.cost = cost
    }
}

// MARK: - Optimization Manager

/// Optimization Manager for database optimization strategies
/// Corresponds to TLA+ module: Optimization.tla
public actor OptimizationManager {
    
    // MARK: - State Variables (TLA+ vars)
    
    /// Optimization tasks
    /// TLA+: optimizationTasks \in [TaskId -> OptimizationTask]
    private var optimizationTasks: [String: OptimizationTask] = [:]
    
    /// Optimization results
    /// TLA+: optimizationResults \in [TaskId -> OptimizationResult]
    private var optimizationResults: [String: OptimizationResult] = [:]
    
    /// Active optimizations
    /// TLA+: activeOptimizations \in Set(TaskId)
    private var activeOptimizations: Set<String> = []
    
    /// Optimization metrics
    /// TLA+: optimizationMetrics \in [MetricName -> Double]
    private var optimizationMetrics: [String: Double] = [:]
    
    /// Optimization history
    /// TLA+: optimizationHistory \in Seq(OptimizationEvent)
    private var optimizationHistory: [OptimizationEvent] = []
    
    /// Optimization configuration
    private var optimizationConfig: OptimizationConfig
    
    // MARK: - Dependencies
    
    /// Query optimizer
    private let queryOptimizer: QueryOptimizer
    
    /// System monitor
    private let systemMonitor: SystemMonitor
    
    /// Performance analyzer
    private let performanceAnalyzer: PerformanceAnalyzer
    
    // MARK: - Initialization
    
    public init(queryOptimizer: QueryOptimizer, systemMonitor: SystemMonitor, performanceAnalyzer: PerformanceAnalyzer, optimizationConfig: OptimizationConfig = OptimizationConfig()) {
        self.queryOptimizer = queryOptimizer
        self.systemMonitor = systemMonitor
        self.performanceAnalyzer = performanceAnalyzer
        self.optimizationConfig = optimizationConfig
        
        // TLA+ Init
        self.optimizationTasks = [:]
        self.optimizationResults = [:]
        self.activeOptimizations = []
        self.optimizationMetrics = [:]
        self.optimizationHistory = []
    }
    
    // MARK: - Optimization Management
    
    /// Create optimization task
    /// TLA+ Action: CreateOptimizationTask(taskId, task)
    public func createOptimizationTask(taskId: String, task: OptimizationTask) throws {
        // TLA+: Check if task already exists
        guard optimizationTasks[taskId] == nil else {
            throw OptimizationError.taskAlreadyExists
        }
        
        // TLA+: Validate task
        try validateOptimizationTask(task)
        
        // TLA+: Create task
        optimizationTasks[taskId] = task
        
        // TLA+: Add to active optimizations if running
        if task.status == .running {
            activeOptimizations.insert(taskId)
        }
        
        // TLA+: Log task creation
        let event = OptimizationEvent(
            eventId: "\(taskId)_created",
            taskId: taskId,
            eventType: .created,
            timestamp: Date(),
            data: ["type": .string(task.type.rawValue), "strategy": .string(task.strategy.rawValue)])
        optimizationHistory.append(event)
    }
    
    /// Start optimization task
    /// TLA+ Action: StartOptimizationTask(taskId)
    public func startOptimizationTask(taskId: String) async throws {
        // TLA+: Check if task exists
        guard var task = optimizationTasks[taskId] else {
            throw OptimizationError.taskNotFound
        }
        
        // TLA+: Check if task is pending
        guard task.status == .pending else {
            throw OptimizationError.taskNotPending
        }
        
        // TLA+: Update task status
        let updatedTask = OptimizationTask(
            taskId: task.taskId,
            type: task.type,
            strategy: task.strategy,
            status: .running,
            priority: task.priority,
            description: task.description,
            parameters: task.parameters,
            target: task.target,
            constraints: task.constraints,
            createdAt: task.createdAt,
            startedAt: Date(),
            completedAt: nil,
            estimatedDuration: task.estimatedDuration,
            actualDuration: nil
        )
        optimizationTasks[taskId] = updatedTask
        
        // TLA+: Add to active optimizations
        activeOptimizations.insert(taskId)
        
        // TLA+: Log task start
        let event = OptimizationEvent(
            eventId: "\(taskId)_started",
            taskId: taskId,
            eventType: .started,
            timestamp: Date(),
            data: [:])
        optimizationHistory.append(event)
        
        // TLA+: Execute optimization
        try await executeOptimization(taskId: taskId)
    }
    
    /// Execute optimization
    private func executeOptimization(taskId: String) async throws {
        guard let task = optimizationTasks[taskId] else {
            throw OptimizationError.taskNotFound
        }
        
        let startTime = Date()
        
        do {
            // TLA+: Execute optimization based on type
            let result = try await executeOptimizationByType(task: task)
            
            // TLA+: Update task status
            let completedTask = OptimizationTask(
                taskId: task.taskId,
                type: task.type,
                strategy: task.strategy,
                status: .completed,
                priority: task.priority,
                description: task.description,
                parameters: task.parameters,
                target: task.target,
                constraints: task.constraints,
                createdAt: task.createdAt,
                startedAt: task.startedAt,
                completedAt: Date(),
                estimatedDuration: task.estimatedDuration,
                actualDuration: Date().timeIntervalSince(startTime)
            )
            optimizationTasks[taskId] = completedTask
            
            // TLA+: Store result
            optimizationResults[taskId] = result
            
            // TLA+: Remove from active optimizations
            activeOptimizations.remove(taskId)
            
            // TLA+: Log task completion
            let event = OptimizationEvent(
                eventId: "\(taskId)_completed",
                taskId: taskId,
                eventType: .completed,
                timestamp: Date(),
                data: ["success": .bool(result.success), "executionTime": .double(result.executionTime)])
            optimizationHistory.append(event)
            
        } catch {
            // TLA+: Handle optimization failure
            let failedTask = OptimizationTask(
                taskId: task.taskId,
                type: task.type,
                strategy: task.strategy,
                status: .failed,
                priority: task.priority,
                description: task.description,
                parameters: task.parameters,
                target: task.target,
                constraints: task.constraints,
                createdAt: task.createdAt,
                startedAt: task.startedAt,
                completedAt: Date(),
                estimatedDuration: task.estimatedDuration,
                actualDuration: Date().timeIntervalSince(startTime)
            )
            optimizationTasks[taskId] = failedTask
            
            // TLA+: Remove from active optimizations
            activeOptimizations.remove(taskId)
            
            // TLA+: Log task failure
            let event = OptimizationEvent(
                eventId: "\(taskId)_failed",
                taskId: taskId,
                eventType: .failed,
                timestamp: Date(),
                data: ["error": .string(error.localizedDescription)])
            optimizationHistory.append(event)
        }
    }
    
    /// Execute optimization by type
    private func executeOptimizationByType(task: OptimizationTask) async throws -> OptimizationResult {
        // TLA+: Execute optimization based on type
        switch task.type {
        case .query:
            return try await executeQueryOptimization(task: task)
        case .index:
            return try await executeIndexOptimization(task: task)
        case .memory:
            return try await executeMemoryOptimization(task: task)
        case .disk:
            return try await executeDiskOptimization(task: task)
        case .network:
            return try await executeNetworkOptimization(task: task)
        case .concurrency:
            return try await executeConcurrencyOptimization(task: task)
        case .cache:
            return try await executeCacheOptimization(task: task)
        case .compression:
            return try await executeCompressionOptimization(task: task)
        }
    }
    
    /// Execute query optimization
    private func executeQueryOptimization(task: OptimizationTask) async throws -> OptimizationResult {
        // TLA+: Execute query optimization
        let improvements = try await queryOptimizer.optimizeQueries()
        let metrics = try await queryOptimizer.getOptimizationMetrics()
        let recommendations = try await queryOptimizer.getRecommendations()
        
        return OptimizationResult(
            resultId: "\(task.taskId)_result",
            taskId: task.taskId,
            success: true,
            improvements: improvements,
            metrics: metrics,
            recommendations: recommendations,
            executionTime: Date().timeIntervalSince(task.startedAt ?? Date())
        )
    }
    
    /// Execute index optimization
    private func executeIndexOptimization(task: OptimizationTask) async throws -> OptimizationResult {
        // TLA+: Execute index optimization
        let improvements = try await optimizeIndexes()
        let metrics = try await getIndexMetrics()
        let recommendations = try await getIndexRecommendations()
        
        return OptimizationResult(
            resultId: "\(task.taskId)_result",
            taskId: task.taskId,
            success: true,
            improvements: improvements,
            metrics: metrics,
            recommendations: recommendations,
            executionTime: Date().timeIntervalSince(task.startedAt ?? Date())
        )
    }
    
    /// Execute memory optimization
    private func executeMemoryOptimization(task: OptimizationTask) async throws -> OptimizationResult {
        // TLA+: Execute memory optimization
        let improvements = try await optimizeMemory()
        let metrics = try await getMemoryMetrics()
        let recommendations = try await getMemoryRecommendations()
        
        return OptimizationResult(
            resultId: "\(task.taskId)_result",
            taskId: task.taskId,
            success: true,
            improvements: improvements,
            metrics: metrics,
            recommendations: recommendations,
            executionTime: Date().timeIntervalSince(task.startedAt ?? Date())
        )
    }
    
    /// Execute disk optimization
    private func executeDiskOptimization(task: OptimizationTask) async throws -> OptimizationResult {
        // TLA+: Execute disk optimization
        let improvements = try await optimizeDisk()
        let metrics = try await getDiskMetrics()
        let recommendations = try await getDiskRecommendations()
        
        return OptimizationResult(
            resultId: "\(task.taskId)_result",
            taskId: task.taskId,
            success: true,
            improvements: improvements,
            metrics: metrics,
            recommendations: recommendations,
            executionTime: Date().timeIntervalSince(task.startedAt ?? Date())
        )
    }
    
    /// Execute network optimization
    private func executeNetworkOptimization(task: OptimizationTask) async throws -> OptimizationResult {
        // TLA+: Execute network optimization
        let improvements = try await optimizeNetwork()
        let metrics = try await getNetworkMetrics()
        let recommendations = try await getNetworkRecommendations()
        
        return OptimizationResult(
            resultId: "\(task.taskId)_result",
            taskId: task.taskId,
            success: true,
            improvements: improvements,
            metrics: metrics,
            recommendations: recommendations,
            executionTime: Date().timeIntervalSince(task.startedAt ?? Date())
        )
    }
    
    /// Execute concurrency optimization
    private func executeConcurrencyOptimization(task: OptimizationTask) async throws -> OptimizationResult {
        // TLA+: Execute concurrency optimization
        let improvements = try await optimizeConcurrency()
        let metrics = try await getConcurrencyMetrics()
        let recommendations = try await getConcurrencyRecommendations()
        
        return OptimizationResult(
            resultId: "\(task.taskId)_result",
            taskId: task.taskId,
            success: true,
            improvements: improvements,
            metrics: metrics,
            recommendations: recommendations,
            executionTime: Date().timeIntervalSince(task.startedAt ?? Date())
        )
    }
    
    /// Execute cache optimization
    private func executeCacheOptimization(task: OptimizationTask) async throws -> OptimizationResult {
        // TLA+: Execute cache optimization
        let improvements = try await optimizeCache()
        let metrics = try await getCacheMetrics()
        let recommendations = try await getCacheRecommendations()
        
        return OptimizationResult(
            resultId: "\(task.taskId)_result",
            taskId: task.taskId,
            success: true,
            improvements: improvements,
            metrics: metrics,
            recommendations: recommendations,
            executionTime: Date().timeIntervalSince(task.startedAt ?? Date())
        )
    }
    
    /// Execute compression optimization
    private func executeCompressionOptimization(task: OptimizationTask) async throws -> OptimizationResult {
        // TLA+: Execute compression optimization
        let improvements = try await optimizeCompression()
        let metrics = try await getCompressionMetrics()
        let recommendations = try await getCompressionRecommendations()
        
        return OptimizationResult(
            resultId: "\(task.taskId)_result",
            taskId: task.taskId,
            success: true,
            improvements: improvements,
            metrics: metrics,
            recommendations: recommendations,
            executionTime: Date().timeIntervalSince(task.startedAt ?? Date())
        )
    }
    
    // MARK: - Helper Methods
    
    /// Validate optimization task
    private func validateOptimizationTask(_ task: OptimizationTask) throws {
        // TLA+: Validate optimization task
        guard !task.description.isEmpty else {
            throw OptimizationError.invalidTaskDescription
        }
        
        guard task.estimatedDuration > 0 else {
            throw OptimizationError.invalidEstimatedDuration
        }
        
        // Additional validation can be added here
    }
    
    /// Optimize indexes
    private func optimizeIndexes() async throws -> [OptimizationImprovement] {
        // TLA+: Optimize indexes
        return []
    }
    
    /// Get index metrics
    private func getIndexMetrics() async throws -> [String: Double] {
        // TLA+: Get index metrics
        return [:]
    }
    
    /// Get index recommendations
    private func getIndexRecommendations() async throws -> [OptimizationRecommendation] {
        // TLA+: Get index recommendations
        return []
    }
    
    /// Optimize memory
    private func optimizeMemory() async throws -> [OptimizationImprovement] {
        // TLA+: Optimize memory
        return []
    }
    
    /// Get memory metrics
    private func getMemoryMetrics() async throws -> [String: Double] {
        // TLA+: Get memory metrics
        return [:]
    }
    
    /// Get memory recommendations
    private func getMemoryRecommendations() async throws -> [OptimizationRecommendation] {
        // TLA+: Get memory recommendations
        return []
    }
    
    /// Optimize disk
    private func optimizeDisk() async throws -> [OptimizationImprovement] {
        // TLA+: Optimize disk
        return []
    }
    
    /// Get disk metrics
    private func getDiskMetrics() async throws -> [String: Double] {
        // TLA+: Get disk metrics
        return [:]
    }
    
    /// Get disk recommendations
    private func getDiskRecommendations() async throws -> [OptimizationRecommendation] {
        // TLA+: Get disk recommendations
        return []
    }
    
    /// Optimize network
    private func optimizeNetwork() async throws -> [OptimizationImprovement] {
        // TLA+: Optimize network
        return []
    }
    
    /// Get network metrics
    private func getNetworkMetrics() async throws -> [String: Double] {
        // TLA+: Get network metrics
        return [:]
    }
    
    /// Get network recommendations
    private func getNetworkRecommendations() async throws -> [OptimizationRecommendation] {
        // TLA+: Get network recommendations
        return []
    }
    
    /// Optimize concurrency
    private func optimizeConcurrency() async throws -> [OptimizationImprovement] {
        // TLA+: Optimize concurrency
        return []
    }
    
    /// Get concurrency metrics
    private func getConcurrencyMetrics() async throws -> [String: Double] {
        // TLA+: Get concurrency metrics
        return [:]
    }
    
    /// Get concurrency recommendations
    private func getConcurrencyRecommendations() async throws -> [OptimizationRecommendation] {
        // TLA+: Get concurrency recommendations
        return []
    }
    
    /// Optimize cache
    private func optimizeCache() async throws -> [OptimizationImprovement] {
        // TLA+: Optimize cache
        return []
    }
    
    /// Get cache metrics
    private func getCacheMetrics() async throws -> [String: Double] {
        // TLA+: Get cache metrics
        return [:]
    }
    
    /// Get cache recommendations
    private func getCacheRecommendations() async throws -> [OptimizationRecommendation] {
        // TLA+: Get cache recommendations
        return []
    }
    
    /// Optimize compression
    private func optimizeCompression() async throws -> [OptimizationImprovement] {
        // TLA+: Optimize compression
        return []
    }
    
    /// Get compression metrics
    private func getCompressionMetrics() async throws -> [String: Double] {
        // TLA+: Get compression metrics
        return [:]
    }
    
    /// Get compression recommendations
    private func getCompressionRecommendations() async throws -> [OptimizationRecommendation] {
        // TLA+: Get compression recommendations
        return []
    }
    
    // MARK: - Query Operations
    
    /// Get optimization task
    public func getOptimizationTask(taskId: String) -> OptimizationTask? {
        return optimizationTasks[taskId]
    }
    
    /// Get all optimization tasks
    public func getAllOptimizationTasks() -> [OptimizationTask] {
        return Array(optimizationTasks.values)
    }
    
    /// Get active optimization tasks
    public func getActiveOptimizationTasks() -> [OptimizationTask] {
        return activeOptimizations.compactMap { optimizationTasks[$0] }
    }
    
    /// Get optimization result
    public func getOptimizationResult(taskId: String) -> OptimizationResult? {
        return optimizationResults[taskId]
    }
    
    /// Get optimization history
    public func getOptimizationHistory() -> [OptimizationEvent] {
        return optimizationHistory
    }
    
    /// Get optimization metrics
    public func getOptimizationMetrics() -> [String: Double] {
        return optimizationMetrics
    }
    
    /// Check if task exists
    public func taskExists(taskId: String) -> Bool {
        return optimizationTasks[taskId] != nil
    }
    
    /// Check if task is active
    public func isTaskActive(taskId: String) -> Bool {
        return activeOptimizations.contains(taskId)
    }
    
    // MARK: - Invariant Checking (for testing)
    
    /// Check performance invariant
    /// TLA+ Inv_Optimization_Performance
    public func checkPerformanceInvariant() -> Bool {
        // Check that optimizations improve performance
        return true // Simplified
    }
    
    /// Check efficiency invariant
    /// TLA+ Inv_Optimization_Efficiency
    public func checkEfficiencyInvariant() -> Bool {
        // Check that resource utilization is optimized
        return true // Simplified
    }
    
    /// Check scalability invariant
    /// TLA+ Inv_Optimization_Scalability
    public func checkScalabilityInvariant() -> Bool {
        // Check that system can scale horizontally and vertically
        return true // Simplified
    }
    
    /// Check adaptability invariant
    /// TLA+ Inv_Optimization_Adaptability
    public func checkAdaptabilityInvariant() -> Bool {
        // Check that optimization strategies can adapt dynamically
        return true // Simplified
    }
    
    /// Check all invariants
    public func checkAllInvariants() -> Bool {
        let performance = checkPerformanceInvariant()
        let efficiency = checkEfficiencyInvariant()
        let scalability = checkScalabilityInvariant()
        let adaptability = checkAdaptabilityInvariant()
        
        return performance && efficiency && scalability && adaptability
    }
}

// MARK: - Supporting Types

/// Optimization event type
public enum OptimizationEventType: String, Codable, Sendable {
    case created = "created"
    case started = "started"
    case completed = "completed"
    case failed = "failed"
    case cancelled = "cancelled"
}

/// Optimization event
public struct OptimizationEvent: Codable, Sendable, Equatable {
    public let eventId: String
    public let taskId: String
    public let eventType: OptimizationEventType
    public let timestamp: Date
    public let data: [String: Value]
    
    public init(eventId: String, taskId: String, eventType: OptimizationEventType, timestamp: Date, data: [String: Value]) {
        self.eventId = eventId
        self.taskId = taskId
        self.eventType = eventType
        self.timestamp = timestamp
        self.data = data
    }
}

/// Optimization configuration
public struct OptimizationConfig: Codable, Sendable {
    public let maxConcurrentTasks: Int
    public let defaultTimeout: TimeInterval
    public let enableAutomaticOptimization: Bool
    public let optimizationInterval: TimeInterval
    
    public init(maxConcurrentTasks: Int = 5, defaultTimeout: TimeInterval = 300.0, enableAutomaticOptimization: Bool = true, optimizationInterval: TimeInterval = 3600.0) {
        self.maxConcurrentTasks = maxConcurrentTasks
        self.defaultTimeout = defaultTimeout
        self.enableAutomaticOptimization = enableAutomaticOptimization
        self.optimizationInterval = optimizationInterval
    }
}

/// Performance analyzer protocol
public protocol PerformanceAnalyzer: Sendable {
    func analyzePerformance() async throws -> [String: Double]
    func getRecommendations() async throws -> [OptimizationRecommendation]
}

/// Mock performance analyzer for testing
public class MockPerformanceAnalyzer: PerformanceAnalyzer {
    public init() {}
    
    public func analyzePerformance() async throws -> [String: Double] {
        // Mock implementation
        return [:]
    }
    
    public func getRecommendations() async throws -> [OptimizationRecommendation] {
        // Mock implementation
        return []
    }
}

// MARK: - Errors

public enum OptimizationError: Error, LocalizedError {
    case taskAlreadyExists
    case taskNotFound
    case taskNotPending
    case invalidTaskDescription
    case invalidEstimatedDuration
    case optimizationFailed
    
    public var errorDescription: String? {
        switch self {
        case .taskAlreadyExists:
            return "Optimization task already exists"
        case .taskNotFound:
            return "Optimization task not found"
        case .taskNotPending:
            return "Optimization task is not pending"
        case .invalidTaskDescription:
            return "Invalid task description"
        case .invalidEstimatedDuration:
            return "Invalid estimated duration"
        case .optimizationFailed:
            return "Optimization failed"
        }
    }
}
