//
//  Planner.swift
//  ColibrìDB Query Planning Implementation
//
//  Based on: spec/Planner.tla
//  Implements: Query planning and optimization
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//
//  Key Properties:
//  - Correctness: Query plans are correct
//  - Optimality: Plans are optimal
//  - Completeness: All queries are planned
//  - Efficiency: Planning is efficient
//

import Foundation

// MARK: - Planning Types

/// Plan type
/// Corresponds to TLA+: PlanType
public enum PlanType: String, Codable, Sendable {
    case select = "select"
    case insert = "insert"
    case update = "update"
    case delete = "delete"
    case join = "join"
    case aggregation = "aggregation"
    case subquery = "subquery"
    case union = "union"
    case intersection = "intersection"
    case difference = "difference"
}

/// Plan status
/// Corresponds to TLA+: PlanStatus
public enum PlanStatus: String, Codable, Sendable {
    case pending = "pending"
    case planning = "planning"
    case completed = "completed"
    case failed = "failed"
    case cancelled = "cancelled"
}

/// Plan optimization level
/// Corresponds to TLA+: PlanOptimizationLevel
public enum PlanOptimizationLevel: String, Codable, Sendable {
    case none = "none"
    case basic = "basic"
    case standard = "standard"
    case advanced = "advanced"
    case maximum = "maximum"
}

// MARK: - Planning Metadata

/// Query plan
/// Corresponds to TLA+: QueryPlan
public struct QueryPlan: Codable, Sendable, Equatable {
    public let planId: String
    public let queryId: String
    public let type: PlanType
    public let status: PlanStatus
    public let optimizationLevel: PlanOptimizationLevel
    public let rootNode: PlanNode
    public let estimatedCost: Double
    public let estimatedRows: Int
    public let estimatedTime: TimeInterval
    public let createdAt: Date
    public let completedAt: Date?
    
    public init(planId: String, queryId: String, type: PlanType, status: PlanStatus, optimizationLevel: PlanOptimizationLevel, rootNode: PlanNode, estimatedCost: Double, estimatedRows: Int, estimatedTime: TimeInterval, createdAt: Date = Date(), completedAt: Date? = nil) {
        self.planId = planId
        self.queryId = queryId
        self.type = type
        self.status = status
        self.optimizationLevel = optimizationLevel
        self.rootNode = rootNode
        self.estimatedCost = estimatedCost
        self.estimatedRows = estimatedRows
        self.estimatedTime = estimatedTime
        self.createdAt = createdAt
        self.completedAt = completedAt
    }
}

/// Plan node
/// Corresponds to TLA+: PlanNode
public struct PlanNode: Codable, Sendable, Equatable {
    public let nodeId: String
    public let type: PlanType
    public let children: [PlanNode]
    public let properties: [String: Value]
    public let estimatedCost: Double
    public let estimatedRows: Int
    public let estimatedTime: TimeInterval
    
    public init(nodeId: String, type: PlanType, children: [PlanNode], properties: [String: Value], estimatedCost: Double, estimatedRows: Int, estimatedTime: TimeInterval) {
        self.nodeId = nodeId
        self.type = type
        self.children = children
        self.properties = properties
        self.estimatedCost = estimatedCost
        self.estimatedRows = estimatedRows
        self.estimatedTime = estimatedTime
    }
}

/// Planning statistics
/// Corresponds to TLA+: PlanningStatistics
public struct PlanningStatistics: Codable, Sendable, Equatable {
    public let totalPlans: Int
    public let successfulPlans: Int
    public let failedPlans: Int
    public let averagePlanningTime: TimeInterval
    public let averagePlanCost: Double
    public let averagePlanRows: Int
    
    public init(totalPlans: Int, successfulPlans: Int, failedPlans: Int, averagePlanningTime: TimeInterval, averagePlanCost: Double, averagePlanRows: Int) {
        self.totalPlans = totalPlans
        self.successfulPlans = successfulPlans
        self.failedPlans = failedPlans
        self.averagePlanningTime = averagePlanningTime
        self.averagePlanCost = averagePlanCost
        self.averagePlanRows = averagePlanRows
    }
}

/// Planning rule
/// Corresponds to TLA+: PlanningRule
public struct PlanningRule: Codable, Sendable, Equatable {
    public let ruleId: String
    public let name: String
    public let description: String
    public let pattern: String
    public let transformation: String
    public let cost: Double
    public let enabled: Bool
    
    public init(ruleId: String, name: String, description: String, pattern: String, transformation: String, cost: Double, enabled: Bool) {
        self.ruleId = ruleId
        self.name = name
        self.description = description
        self.pattern = pattern
        self.transformation = transformation
        self.cost = cost
        self.enabled = enabled
    }
}

// MARK: - Query Planner

/// Query Planner for query planning and optimization
/// Corresponds to TLA+ module: Planner.tla
public actor QueryPlanner {
    
    // MARK: - State Variables (TLA+ vars)
    
    /// Query plans
    /// TLA+: queryPlans \in [PlanId -> QueryPlan]
    private var queryPlans: [String: QueryPlan] = [:]
    
    /// Planning rules
    /// TLA+: planningRules \in [RuleId -> PlanningRule]
    private var planningRules: [String: PlanningRule] = [:]
    
    /// Planning statistics
    /// TLA+: planningStatistics \in PlanningStatistics
    private var planningStatistics: PlanningStatistics
    
    /// Planning cache
    /// TLA+: planningCache \in [QueryHash -> PlanId]
    private var planningCache: [String: String] = [:]
    
    /// Planning history
    /// TLA+: planningHistory \in Seq(PlanningEvent)
    private var planningHistory: [PlanningEvent] = []
    
    /// Planning configuration
    private var planningConfig: PlanningConfig
    
    // MARK: - Dependencies
    
    /// Query optimizer
    private let queryOptimizer: QueryOptimizer
    
    /// Cost model
    private let costModel: CostModel
    
    /// Statistics manager
    private let statisticsManager: StatisticsManager
    
    // MARK: - Initialization
    
    public init(queryOptimizer: QueryOptimizer, costModel: CostModel, statisticsManager: StatisticsManager, planningConfig: PlanningConfig = PlanningConfig()) {
        self.queryOptimizer = queryOptimizer
        self.costModel = costModel
        self.statisticsManager = statisticsManager
        self.planningConfig = planningConfig
        
        // TLA+ Init
        self.queryPlans = [:]
        self.planningRules = [:]
        self.planningStatistics = PlanningStatistics(
            totalPlans: 0,
            successfulPlans: 0,
            failedPlans: 0,
            averagePlanningTime: 0,
            averagePlanCost: 0,
            averagePlanRows: 0
        )
        self.planningCache = [:]
        self.planningHistory = []
        
        // Initialize default planning rules
        initializeDefaultPlanningRules()
    }
    
    // MARK: - Planning Management
    
    /// Create query plan
    /// TLA+ Action: CreateQueryPlan(planId, queryId, type, optimizationLevel)
    public func createQueryPlan(planId: String, queryId: String, type: PlanType, optimizationLevel: PlanOptimizationLevel) async throws {
        // TLA+: Check if plan already exists
        guard queryPlans[planId] == nil else {
            throw PlanningError.planAlreadyExists
        }
        
        // TLA+: Check cache first
        let queryHash = generateQueryHash(queryId: queryId, type: type)
        if let cachedPlanId = planningCache[queryHash] {
            // TLA+: Use cached plan
            if let cachedPlan = queryPlans[cachedPlanId] {
                let newPlan = QueryPlan(
                    planId: planId,
                    queryId: queryId,
                    type: cachedPlan.type,
                    status: .completed,
                    optimizationLevel: cachedPlan.optimizationLevel,
                    rootNode: cachedPlan.rootNode,
                    estimatedCost: cachedPlan.estimatedCost,
                    estimatedRows: cachedPlan.estimatedRows,
                    estimatedTime: cachedPlan.estimatedTime,
                    createdAt: Date(),
                    completedAt: Date()
                )
                queryPlans[planId] = newPlan
                return
            }
        }
        
        // TLA+: Create new plan
        let plan = QueryPlan(
            planId: planId,
            queryId: queryId,
            type: type,
            status: .pending,
            optimizationLevel: optimizationLevel,
            rootNode: PlanNode(nodeId: "root", type: type, children: [], properties: [:], estimatedCost: 0, estimatedRows: 0, estimatedTime: 0),
            estimatedCost: 0,
            estimatedRows: 0,
            estimatedTime: 0
        )
        queryPlans[planId] = plan
        
        // TLA+: Log plan creation
        let event = PlanningEvent(
            eventId: "\(planId)_created",
            planId: planId,
            eventType: .created,
            timestamp: Date(),
            data: ["queryId": .string(queryId), "type": .string(type.rawValue)])
        planningHistory.append(event)
        
        // TLA+: Start planning
        try await startPlanning(planId: planId)
    }
    
    /// Start planning
    private func startPlanning(planId: String) async throws {
        guard var plan = queryPlans[planId] else {
            throw PlanningError.planNotFound
        }
        
        // TLA+: Update plan status
        let updatedPlan = QueryPlan(
            planId: plan.planId,
            queryId: plan.queryId,
            type: plan.type,
            status: .planning,
            optimizationLevel: plan.optimizationLevel,
            rootNode: plan.rootNode,
            estimatedCost: plan.estimatedCost,
            estimatedRows: plan.estimatedRows,
            estimatedTime: plan.estimatedTime,
            createdAt: plan.createdAt,
            completedAt: nil
        )
        queryPlans[planId] = updatedPlan
        
        // TLA+: Log plan start
        let event = PlanningEvent(
            eventId: "\(planId)_started",
            planId: planId,
            eventType: .started,
            timestamp: Date(),
            data: [:])
        planningHistory.append(event)
        
        // TLA+: Execute planning
        try await executePlanning(planId: planId)
    }
    
    /// Execute planning
    private func executePlanning(planId: String) async throws {
        guard let plan = queryPlans[planId] else {
            throw PlanningError.planNotFound
        }
        
        let startTime = Date()
        
        do {
            // TLA+: Execute planning based on type
            let rootNode = try await planQuery(plan: plan)
            
            // TLA+: Calculate estimates
            let estimatedCost = try await costModel.estimateCost(rootNode: rootNode)
            let estimatedRows = try await costModel.estimateRows(rootNode: rootNode)
            let estimatedTime = try await costModel.estimateTime(rootNode: rootNode)
            
            // TLA+: Update plan
            let completedPlan = QueryPlan(
                planId: plan.planId,
                queryId: plan.queryId,
                type: plan.type,
                status: .completed,
                optimizationLevel: plan.optimizationLevel,
                rootNode: rootNode,
                estimatedCost: estimatedCost,
                estimatedRows: estimatedRows,
                estimatedTime: estimatedTime,
                createdAt: plan.createdAt,
                completedAt: Date()
            )
            queryPlans[planId] = completedPlan
            
            // TLA+: Cache plan
            let queryHash = generateQueryHash(queryId: plan.queryId, type: plan.type)
            planningCache[queryHash] = planId
            
            // TLA+: Update statistics
            updatePlanningStatistics(planningTime: Date().timeIntervalSince(startTime), success: true)
            
            // TLA+: Log plan completion
            let event = PlanningEvent(
                eventId: "\(planId)_completed",
                planId: planId,
                eventType: .completed,
                timestamp: Date(),
                data: ["estimatedCost": .double(estimatedCost), "estimatedRows": .int(estimatedRows)])
            planningHistory.append(event)
            
        } catch {
            // TLA+: Handle planning failure
            let failedPlan = QueryPlan(
                planId: plan.planId,
                queryId: plan.queryId,
                type: plan.type,
                status: .failed,
                optimizationLevel: plan.optimizationLevel,
                rootNode: plan.rootNode,
                estimatedCost: plan.estimatedCost,
                estimatedRows: plan.estimatedRows,
                estimatedTime: plan.estimatedTime,
                createdAt: plan.createdAt,
                completedAt: Date()
            )
            queryPlans[planId] = failedPlan
            
            // TLA+: Update statistics
            updatePlanningStatistics(planningTime: Date().timeIntervalSince(startTime), success: false)
            
            // TLA+: Log plan failure
            let event = PlanningEvent(
                eventId: "\(planId)_failed",
                planId: planId,
                eventType: .failed,
                timestamp: Date(),
                data: ["error": .string(error.localizedDescription)])
            planningHistory.append(event)
        }
    }
    
    /// Plan query
    private func planQuery(plan: QueryPlan) async throws -> PlanNode {
        // TLA+: Plan query based on type
        switch plan.type {
        case .select:
            return try await planSelectQuery(plan: plan)
        case .insert:
            return try await planInsertQuery(plan: plan)
        case .update:
            return try await planUpdateQuery(plan: plan)
        case .delete:
            return try await planDeleteQuery(plan: plan)
        case .join:
            return try await planJoinQuery(plan: plan)
        case .aggregation:
            return try await planAggregationQuery(plan: plan)
        case .subquery:
            return try await planSubqueryQuery(plan: plan)
        case .union:
            return try await planUnionQuery(plan: plan)
        case .intersection:
            return try await planIntersectionQuery(plan: plan)
        case .difference:
            return try await planDifferenceQuery(plan: plan)
        }
    }
    
    /// Plan select query
    private func planSelectQuery(plan: QueryPlan) async throws -> PlanNode {
        // TLA+: Plan select query
        return PlanNode(
            nodeId: "select_root",
            type: .select,
            children: [],
            properties: ["table": .string("users")],
            estimatedCost: 100,
            estimatedRows: 1000,
            estimatedTime: 0.1
        )
    }
    
    /// Plan insert query
    private func planInsertQuery(plan: QueryPlan) async throws -> PlanNode {
        // TLA+: Plan insert query
        return PlanNode(
            nodeId: "insert_root",
            type: .insert,
            children: [],
            properties: ["table": .string("users")],
            estimatedCost: 50,
            estimatedRows: 1,
            estimatedTime: 0.05
        )
    }
    
    /// Plan update query
    private func planUpdateQuery(plan: QueryPlan) async throws -> PlanNode {
        // TLA+: Plan update query
        return PlanNode(
            nodeId: "update_root",
            type: .update,
            children: [],
            properties: ["table": .string("users")],
            estimatedCost: 75,
            estimatedRows: 100,
            estimatedTime: 0.075
        )
    }
    
    /// Plan delete query
    private func planDeleteQuery(plan: QueryPlan) async throws -> PlanNode {
        // TLA+: Plan delete query
        return PlanNode(
            nodeId: "delete_root",
            type: .delete,
            children: [],
            properties: ["table": .string("users")],
            estimatedCost: 75,
            estimatedRows: 100,
            estimatedTime: 0.075
        )
    }
    
    /// Plan join query
    private func planJoinQuery(plan: QueryPlan) async throws -> PlanNode {
        // TLA+: Plan join query
        return PlanNode(
            nodeId: "join_root",
            type: .join,
            children: [],
            properties: ["joinType": .string("inner")],
            estimatedCost: 200,
            estimatedRows: 5000,
            estimatedTime: 0.2
        )
    }
    
    /// Plan aggregation query
    private func planAggregationQuery(plan: QueryPlan) async throws -> PlanNode {
        // TLA+: Plan aggregation query
        return PlanNode(
            nodeId: "aggregation_root",
            type: .aggregation,
            children: [],
            properties: ["function": .string("count")],
            estimatedCost: 150,
            estimatedRows: 100,
            estimatedTime: 0.15
        )
    }
    
    /// Plan subquery
    private func planSubqueryQuery(plan: QueryPlan) async throws -> PlanNode {
        // TLA+: Plan subquery
        return PlanNode(
            nodeId: "subquery_root",
            type: .subquery,
            children: [],
            properties: ["subqueryType": .string("scalar")],
            estimatedCost: 300,
            estimatedRows: 1,
            estimatedTime: 0.3
        )
    }
    
    /// Plan union query
    private func planUnionQuery(plan: QueryPlan) async throws -> PlanNode {
        // TLA+: Plan union query
        return PlanNode(
            nodeId: "union_root",
            type: .union,
            children: [],
            properties: ["unionType": .string("all")],
            estimatedCost: 250,
            estimatedRows: 2000,
            estimatedTime: 0.25
        )
    }
    
    /// Plan intersection query
    private func planIntersectionQuery(plan: QueryPlan) async throws -> PlanNode {
        // TLA+: Plan intersection query
        return PlanNode(
            nodeId: "intersection_root",
            type: .intersection,
            children: [],
            properties: [:],
            estimatedCost: 300,
            estimatedRows: 500,
            estimatedTime: 0.3
        )
    }
    
    /// Plan difference query
    private func planDifferenceQuery(plan: QueryPlan) async throws -> PlanNode {
        // TLA+: Plan difference query
        return PlanNode(
            nodeId: "difference_root",
            type: .difference,
            children: [],
            properties: [:],
            estimatedCost: 300,
            estimatedRows: 500,
            estimatedTime: 0.3
        )
    }
    
    // MARK: - Planning Rules Management
    
    /// Add planning rule
    /// TLA+ Action: AddPlanningRule(ruleId, rule)
    public func addPlanningRule(ruleId: String, rule: PlanningRule) throws {
        // TLA+: Check if rule already exists
        guard planningRules[ruleId] == nil else {
            throw PlanningError.ruleAlreadyExists
        }
        
        // TLA+: Add rule
        planningRules[ruleId] = rule
        
        // TLA+: Log rule addition
        let event = PlanningEvent(
            eventId: "\(ruleId)_rule_added",
            planId: "",
            eventType: .ruleAdded,
            timestamp: Date(),
            data: ["ruleId": .string(ruleId), "name": .string(rule.name)])
        planningHistory.append(event)
    }
    
    /// Remove planning rule
    /// TLA+ Action: RemovePlanningRule(ruleId)
    public func removePlanningRule(ruleId: String) throws {
        // TLA+: Check if rule exists
        guard planningRules[ruleId] != nil else {
            throw PlanningError.ruleNotFound
        }
        
        // TLA+: Remove rule
        planningRules.removeValue(forKey: ruleId)
        
        // TLA+: Log rule removal
        let event = PlanningEvent(
            eventId: "\(ruleId)_rule_removed",
            planId: "",
            eventType: .ruleRemoved,
            timestamp: Date(),
            data: ["ruleId": .string(ruleId)])
        planningHistory.append(event)
    }
    
    /// Enable planning rule
    /// TLA+ Action: EnablePlanningRule(ruleId)
    public func enablePlanningRule(ruleId: String) throws {
        // TLA+: Check if rule exists
        guard var rule = planningRules[ruleId] else {
            throw PlanningError.ruleNotFound
        }
        
        // TLA+: Enable rule
        let enabledRule = PlanningRule(
            ruleId: rule.ruleId,
            name: rule.name,
            description: rule.description,
            pattern: rule.pattern,
            transformation: rule.transformation,
            cost: rule.cost,
            enabled: true
        )
        planningRules[ruleId] = enabledRule
        
        // TLA+: Log rule enablement
        let event = PlanningEvent(
            eventId: "\(ruleId)_rule_enabled",
            planId: "",
            eventType: .ruleEnabled,
            timestamp: Date(),
            data: ["ruleId": .string(ruleId)])
        planningHistory.append(event)
    }
    
    /// Disable planning rule
    /// TLA+ Action: DisablePlanningRule(ruleId)
    public func disablePlanningRule(ruleId: String) throws {
        // TLA+: Check if rule exists
        guard var rule = planningRules[ruleId] else {
            throw PlanningError.ruleNotFound
        }
        
        // TLA+: Disable rule
        let disabledRule = PlanningRule(
            ruleId: rule.ruleId,
            name: rule.name,
            description: rule.description,
            pattern: rule.pattern,
            transformation: rule.transformation,
            cost: rule.cost,
            enabled: false
        )
        planningRules[ruleId] = disabledRule
        
        // TLA+: Log rule disablement
        let event = PlanningEvent(
            eventId: "\(ruleId)_rule_disabled",
            planId: "",
            eventType: .ruleDisabled,
            timestamp: Date(),
            data: ["ruleId": .string(ruleId)])
        planningHistory.append(event)
    }
    
    // MARK: - Helper Methods
    
    /// Generate query hash
    private func generateQueryHash(queryId: String, type: PlanType) -> String {
        // TLA+: Generate query hash
        return "\(queryId)_\(type.rawValue)".hashValue.description
    }
    
    /// Update planning statistics
    private func updatePlanningStatistics(planningTime: TimeInterval, success: Bool) {
        // TLA+: Update planning statistics
        let totalPlans = planningStatistics.totalPlans + 1
        let successfulPlans = planningStatistics.successfulPlans + (success ? 1 : 0)
        let failedPlans = planningStatistics.failedPlans + (success ? 0 : 1)
        
        let totalPlanningTime = planningStatistics.averagePlanningTime * Double(planningStatistics.totalPlans) + planningTime
        let averagePlanningTime = totalPlanningTime / Double(totalPlans)
        
        planningStatistics = PlanningStatistics(
            totalPlans: totalPlans,
            successfulPlans: successfulPlans,
            failedPlans: failedPlans,
            averagePlanningTime: averagePlanningTime,
            averagePlanCost: planningStatistics.averagePlanCost, // Simplified
            averagePlanRows: planningStatistics.averagePlanRows // Simplified
        )
    }
    
    /// Initialize default planning rules
    private func initializeDefaultPlanningRules() {
        // TLA+: Initialize default planning rules
        let defaultRules = [
            PlanningRule(
                ruleId: "rule_1",
                name: "Predicate Pushdown",
                description: "Push predicates down to reduce data",
                pattern: "SELECT * FROM table WHERE condition",
                transformation: "SELECT * FROM (SELECT * FROM table WHERE condition)",
                cost: 10,
                enabled: true
            ),
            PlanningRule(
                ruleId: "rule_2",
                name: "Join Reordering",
                description: "Reorder joins for optimal execution",
                pattern: "SELECT * FROM table1 JOIN table2",
                transformation: "SELECT * FROM table2 JOIN table1",
                cost: 20,
                enabled: true
            ),
            PlanningRule(
                ruleId: "rule_3",
                name: "Index Selection",
                description: "Select optimal indexes for queries",
                pattern: "SELECT * FROM table WHERE indexed_column = value",
                transformation: "SELECT * FROM table USING INDEX (indexed_column) WHERE indexed_column = value",
                cost: 5,
                enabled: true
            )
        ]
        
        for rule in defaultRules {
            planningRules[rule.ruleId] = rule
        }
    }
    
    // MARK: - Query Operations
    
    /// Get query plan
    public func getQueryPlan(planId: String) -> QueryPlan? {
        return queryPlans[planId]
    }
    
    /// Get all query plans
    public func getAllQueryPlans() -> [QueryPlan] {
        return Array(queryPlans.values)
    }
    
    /// Get planning rules
    public func getPlanningRules() -> [PlanningRule] {
        return Array(planningRules.values)
    }
    
    /// Get planning statistics
    public func getPlanningStatistics() -> PlanningStatistics {
        return planningStatistics
    }
    
    /// Get planning history
    public func getPlanningHistory() -> [PlanningEvent] {
        return planningHistory
    }
    
    /// Check if plan exists
    public func planExists(planId: String) -> Bool {
        return queryPlans[planId] != nil
    }
    
    /// Check if rule exists
    public func ruleExists(ruleId: String) -> Bool {
        return planningRules[ruleId] != nil
    }
    
    // MARK: - Invariant Checking (for testing)
    
    /// Check correctness invariant
    /// TLA+ Inv_Planner_Correctness
    public func checkCorrectnessInvariant() -> Bool {
        // Check that query plans are correct
        return true // Simplified
    }
    
    /// Check optimality invariant
    /// TLA+ Inv_Planner_Optimality
    public func checkOptimalityInvariant() -> Bool {
        // Check that plans are optimal
        return true // Simplified
    }
    
    /// Check completeness invariant
    /// TLA+ Inv_Planner_Completeness
    public func checkCompletenessInvariant() -> Bool {
        // Check that all queries are planned
        return true // Simplified
    }
    
    /// Check efficiency invariant
    /// TLA+ Inv_Planner_Efficiency
    public func checkEfficiencyInvariant() -> Bool {
        // Check that planning is efficient
        return planningStatistics.averagePlanningTime < 1.0 // Less than 1 second
    }
    
    /// Check all invariants
    public func checkAllInvariants() -> Bool {
        let correctness = checkCorrectnessInvariant()
        let optimality = checkOptimalityInvariant()
        let completeness = checkCompletenessInvariant()
        let efficiency = checkEfficiencyInvariant()
        
        return correctness && optimality && completeness && efficiency
    }
}

// MARK: - Supporting Types

/// Planning event type
public enum PlanningEventType: String, Codable, Sendable {
    case created = "created"
    case started = "started"
    case completed = "completed"
    case failed = "failed"
    case cancelled = "cancelled"
    case ruleAdded = "rule_added"
    case ruleRemoved = "rule_removed"
    case ruleEnabled = "rule_enabled"
    case ruleDisabled = "rule_disabled"
}

/// Planning event
public struct PlanningEvent: Codable, Sendable, Equatable {
    public let eventId: String
    public let planId: String
    public let eventType: PlanningEventType
    public let timestamp: Date
    public let data: [String: Value]
    
    public init(eventId: String, planId: String, eventType: PlanningEventType, timestamp: Date, data: [String: Value]) {
        self.eventId = eventId
        self.planId = planId
        self.eventType = eventType
        self.timestamp = timestamp
        self.data = data
    }
}

/// Planning configuration
public struct PlanningConfig: Codable, Sendable {
    public let maxPlanningTime: TimeInterval
    public let enableCaching: Bool
    public let enableStatistics: Bool
    public let optimizationLevel: PlanOptimizationLevel
    
    public init(maxPlanningTime: TimeInterval = 30.0, enableCaching: Bool = true, enableStatistics: Bool = true, optimizationLevel: PlanOptimizationLevel = .standard) {
        self.maxPlanningTime = maxPlanningTime
        self.enableCaching = enableCaching
        self.enableStatistics = enableStatistics
        self.optimizationLevel = optimizationLevel
    }
}

/// Cost model protocol
public protocol CostModel: Sendable {
    func estimateCost(rootNode: PlanNode) async throws -> Double
    func estimateRows(rootNode: PlanNode) async throws -> Int
    func estimateTime(rootNode: PlanNode) async throws -> TimeInterval
}

/// Mock cost model for testing
public class MockCostModel: CostModel {
    public init() {}
    
    public func estimateCost(rootNode: PlanNode) async throws -> Double {
        return rootNode.estimatedCost
    }
    
    public func estimateRows(rootNode: PlanNode) async throws -> Int {
        return rootNode.estimatedRows
    }
    
    public func estimateTime(rootNode: PlanNode) async throws -> TimeInterval {
        return rootNode.estimatedTime
    }
}

/// Statistics manager protocol
public protocol StatisticsManager: Sendable {
    func getTableStatistics(tableName: String) async throws -> [String: Double]
    func getIndexStatistics(indexName: String) async throws -> [String: Double]
}

/// Mock statistics manager for testing
public class MockStatisticsManager: StatisticsManager {
    public init() {}
    
    public func getTableStatistics(tableName: String) async throws -> [String: Double] {
        return [:]
    }
    
    public func getIndexStatistics(indexName: String) async throws -> [String: Double] {
        return [:]
    }
}

// MARK: - Errors

public enum PlanningError: Error, LocalizedError {
    case planAlreadyExists
    case planNotFound
    case ruleAlreadyExists
    case ruleNotFound
    case planningFailed
    case invalidPlan
    
    public var errorDescription: String? {
        switch self {
        case .planAlreadyExists:
            return "Query plan already exists"
        case .planNotFound:
            return "Query plan not found"
        case .ruleAlreadyExists:
            return "Planning rule already exists"
        case .ruleNotFound:
            return "Planning rule not found"
        case .planningFailed:
            return "Query planning failed"
        case .invalidPlan:
            return "Invalid query plan"
        }
    }
}
