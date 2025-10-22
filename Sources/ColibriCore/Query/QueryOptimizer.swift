//
//  QueryOptimizer.swift
//  ColibrìDB Query Optimizer
//
//  Based on: spec/QueryOptimizer.tla
//  Implements: Cost-based query optimization
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//
//  Based on: "Access Path Selection in a Relational Database" (Selinger et al., 1979)
//

import Foundation

/// Query optimizer for cost-based optimization
/// Corresponds to TLA+ module: QueryOptimizer.tla
public actor QueryOptimizer {
    // MARK: - Dependencies
    
    private let catalog: Catalog
    private let statistics: StatisticsManager
    
    // MARK: - Cost Model Constants
    
    /// Cost per page I/O
    private static let costPerPageIO: Double = 1.0
    
    /// Cost per CPU operation
    private static let costPerCPU: Double = 0.01
    
    /// Cost per tuple
    private static let costPerTuple: Double = 0.001
    
    // MARK: - Initialization
    
    public init(catalog: Catalog, statistics: StatisticsManager) {
        self.catalog = catalog
        self.statistics = statistics
    }
    
    // MARK: - Query Optimization
    
    /// Optimize a logical query plan
    /// TLA+ Action: Optimize(logicalPlan)
    public func optimize(logical plan: LogicalPlan) async -> PlanNode {
        // Step 1: Generate candidate physical plans
        let candidates = await generateCandidates(logical: plan)
        
        // Step 2: Estimate cost for each candidate
        var bestPlan: PlanNode?
        var bestCost = Double.infinity
        
        for candidate in candidates {
            let cost = await estimateCost(plan: candidate)
            if cost < bestCost {
                bestCost = cost
                bestPlan = candidate
            }
        }
        
        return bestPlan ?? PlanNode(planId: "default", queryId: plan.table, rootNode: "scan", nodes: [:], cost: 0, estimatedRows: 0, estimatedCost: 0)
    }
    
    // MARK: - Plan Generation
    
    /// Generate candidate physical plans
    private func generateCandidates(logical plan: LogicalPlan) async -> [PlanNode] {
        var candidates: [PlanNode] = []
        
        // Generate scan plans
        candidates.append(PlanNode(planId: "scan_\(plan.table)", queryId: plan.table, rootNode: "scan", nodes: [:], cost: 0, estimatedRows: 0, estimatedCost: 0))
        
        // Generate index scan plans if applicable
        if let indexes = await catalog.getTable(plan.table)?.indexes {
            for index in indexes {
                if let key = plan.filterKey {
                    candidates.append(PlanNode(planId: "index_\(index.name)", queryId: plan.table, rootNode: "indexScan", nodes: [:], cost: 0, estimatedRows: 0, estimatedCost: 0))
                }
            }
        }
        
        // Apply filters
        if let predicate = plan.predicate {
            candidates = candidates.map { candidate in
                PlanNode(planId: "filter_\(candidate.planId)", queryId: candidate.queryId, rootNode: "filter", nodes: [:], cost: candidate.cost, estimatedRows: candidate.estimatedRows, estimatedCost: candidate.estimatedCost)
            }
        }
        
        // Apply projections
        if let columns = plan.projection {
            candidates = candidates.map { candidate in
                PlanNode(planId: "project_\(candidate.planId)", queryId: candidate.queryId, rootNode: "project", nodes: [:], cost: candidate.cost, estimatedRows: candidate.estimatedRows, estimatedCost: candidate.estimatedCost)
            }
        }
        
        // Apply sorts
        if let sortColumns = plan.sortColumns {
            candidates = candidates.map { candidate in
                PlanNode(planId: "sort_\(candidate.planId)", queryId: candidate.queryId, rootNode: "sort", nodes: [:], cost: candidate.cost, estimatedRows: candidate.estimatedRows, estimatedCost: candidate.estimatedCost)
            }
        }
        
        // Apply limits
        if let limit = plan.limit {
            candidates = candidates.map { candidate in
                PlanNode(planId: "limit_\(candidate.planId)", queryId: candidate.queryId, rootNode: "limit", nodes: [:], cost: candidate.cost, estimatedRows: min(candidate.estimatedRows, limit), estimatedCost: candidate.estimatedCost)
            }
        }
        
        return candidates
    }
    
    // MARK: - Cost Estimation
    
    /// Estimate cost of a physical plan
    /// TLA+ Function: EstimateCost(plan)
    private func estimateCost(plan: PlanNode) async -> Double {
        switch plan.rootNode {
        case "scan":
            return await estimateScanCost(table: plan.queryId)
            
        case "indexScan":
            return await estimateIndexScanCost(table: plan.queryId, index: "default")
            
        case "filter":
            let selectivity = 0.1  // Assume 10% selectivity
            return plan.estimatedCost + (plan.estimatedCost * selectivity * Self.costPerTuple)
            
        case "project":
            return plan.estimatedCost + (plan.estimatedCost * Self.costPerCPU)
            
        case "join":
            return await estimateJoinCost(left: plan, right: plan)
            
        case "aggregate":
            return plan.estimatedCost + (plan.estimatedCost * 0.5)  // Hash aggregation overhead
            
        case "sort":
            let cardinality = plan.estimatedRows
            let sortCost = Double(cardinality) * log2(Double(cardinality)) * Self.costPerCPU
            return plan.estimatedCost + sortCost
            
        case "limit":
            return plan.estimatedCost * 0.1  // Assume early termination
            
        default:
            return plan.estimatedCost
        }
    }
    
    /// Estimate scan cost
    private func estimateScanCost(table: String) async -> Double {
        let pageCount = await statistics.getPageCount(table: table)
        return Double(pageCount) * Self.costPerPageIO
    }
    
    /// Estimate index scan cost
    private func estimateIndexScanCost(table: String, index: String) async -> Double {
        let indexHeight = await statistics.getIndexHeight(table: table, index: index)
        let resultPages = await statistics.getResultPages(table: table, index: index)
        
        // Cost = tree traversal + result fetch
        return Double(indexHeight + resultPages) * Self.costPerPageIO
    }
    
    /// Estimate join cost
    private func estimateJoinCost(left: PlanNode, right: PlanNode) async -> Double {
        let leftCost = await estimateCost(plan: left)
        let rightCost = await estimateCost(plan: right)
        let leftCard = await estimateCardinality(plan: left)
        let rightCard = await estimateCardinality(plan: right)
        
        // Nested loop join cost: left + (left_card * right)
        let nestedLoopCost = leftCost + (Double(leftCard) * rightCost)
        
        // Hash join cost: left + right + hash_build
        let hashJoinCost = leftCost + rightCost + (Double(leftCard + rightCard) * Self.costPerTuple)
        
        // Return minimum
        return min(nestedLoopCost, hashJoinCost)
    }
    
    /// Estimate cardinality (row count)
    private func estimateCardinality(plan: PlanNode) async -> Int {
        switch plan.rootNode {
        case "scan":
            return await statistics.getRowCount(table: plan.queryId)
            
        case "indexScan":
            return await statistics.getRowCount(table: plan.queryId) / 10  // Assume 10% selectivity
            
        case "filter":
            return plan.estimatedRows / 10  // Assume 10% selectivity
            
        case "project":
            return plan.estimatedRows
            
        case "join":
            return plan.estimatedRows  // Use estimated rows from plan
            
        case "aggregate":
            return plan.estimatedRows / 100  // Assume groups
            
        case "sort":
            return plan.estimatedRows
            
        case "limit":
            return plan.estimatedRows
            
        default:
            return plan.estimatedRows
        }
    }
}

// MARK: - Supporting Types

/// Logical query plan
public struct LogicalPlan {
    public let table: String
    public let predicate: ((Row) -> Bool)?
    public let filterKey: Value?
    public let projection: [String]?
    public let sortColumns: [String]?
    public let limit: Int?
    
    public init(
        table: String,
        predicate: ((Row) -> Bool)? = nil,
        filterKey: Value? = nil,
        projection: [String]? = nil,
        sortColumns: [String]? = nil,
        limit: Int? = nil
    ) {
        self.table = table
        self.predicate = predicate
        self.filterKey = filterKey
        self.projection = projection
        self.sortColumns = sortColumns
        self.limit = limit
    }
}

/// Query optimizer statistics manager interface
public actor QueryOptimizerStatisticsManager {
    private var tableStats: [String: QueryOptimizerTableStatistics] = [:]
    
    public init() {}
    
    public func getPageCount(table: String) -> Int {
        return tableStats[table]?.pageCount ?? 100
    }
    
    public func getRowCount(table: String) -> Int {
        return tableStats[table]?.rowCount ?? 1000
    }
    
    public func getIndexHeight(table: String, index: String) -> Int {
        return 3  // Typical B+Tree height
    }
    
    public func getResultPages(table: String, index: String) -> Int {
        return 10  // Estimated result pages
    }
    
    public func updateStatistics(table: String, stats: QueryOptimizerTableStatistics) {
        tableStats[table] = stats
    }
}

/// Query optimizer table statistics
public struct QueryOptimizerTableStatistics {
    public let pageCount: Int
    public let rowCount: Int
    public let avgRowSize: Int
    
    public init(pageCount: Int, rowCount: Int, avgRowSize: Int) {
        self.pageCount = pageCount
        self.rowCount = rowCount
        self.avgRowSize = avgRowSize
    }
}

