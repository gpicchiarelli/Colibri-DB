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
    public func optimize(logical plan: LogicalPlan) async -> QueryPlanNode {
        // Step 1: Generate candidate physical plans
        let candidates = await generateCandidates(logical: plan)
        
        // Step 2: Estimate cost for each candidate
        var bestPlan: QueryPlanNode?
        var bestCost = Double.infinity
        
        for candidate in candidates {
            let cost = await estimateCost(plan: candidate)
            if cost < bestCost {
                bestCost = cost
                bestPlan = candidate
            }
        }
        
        return bestPlan ?? .scan(table: plan.table)
    }
    
    // MARK: - Plan Generation
    
    /// Generate candidate physical plans
    private func generateCandidates(logical plan: LogicalPlan) async -> [QueryPlanNode] {
        var candidates: [QueryPlanNode] = []
        
        // Generate scan plans
        candidates.append(.scan(table: plan.table))
        
        // Generate index scan plans if applicable
        if let indexes = await catalog.getTable(plan.table)?.indexes {
            for index in indexes {
                if let key = plan.filterKey {
                    candidates.append(.indexScan(table: plan.table, index: index.name, key: key))
                }
            }
        }
        
        // Apply filters
        if let predicate = plan.predicate {
            candidates = candidates.map { candidate in
                .filter(predicate: predicate, child: candidate)
            }
        }
        
        // Apply projections
        if let columns = plan.projection {
            candidates = candidates.map { candidate in
                .project(columns: columns, child: candidate)
            }
        }
        
        // Apply sorts
        if let sortColumns = plan.sortColumns {
            candidates = candidates.map { candidate in
                .sort(columns: sortColumns, child: candidate)
            }
        }
        
        // Apply limits
        if let limit = plan.limit {
            candidates = candidates.map { candidate in
                .limit(count: limit, child: candidate)
            }
        }
        
        return candidates
    }
    
    // MARK: - Cost Estimation
    
    /// Estimate cost of a physical plan
    /// TLA+ Function: EstimateCost(plan)
    private func estimateCost(plan: QueryPlanNode) async -> Double {
        switch plan {
        case .scan(let table):
            return await estimateScanCost(table: table)
            
        case .indexScan(let table, let index, _):
            return await estimateIndexScanCost(table: table, index: index)
            
        case .filter(_, let child):
            let childCost = await estimateCost(plan: child)
            let selectivity = 0.1  // Assume 10% selectivity
            return childCost + (childCost * selectivity * Self.costPerTuple)
            
        case .project(_, let child):
            let childCost = await estimateCost(plan: child)
            return childCost + (childCost * Self.costPerCPU)
            
        case .join(let left, let right, _):
            return await estimateJoinCost(left: left, right: right)
            
        case .aggregate(_, _, let child):
            let childCost = await estimateCost(plan: child)
            return childCost + (childCost * 0.5)  // Hash aggregation overhead
            
        case .sort(_, let child):
            let childCost = await estimateCost(plan: child)
            let cardinality = await estimateCardinality(plan: child)
            let sortCost = Double(cardinality) * log2(Double(cardinality)) * Self.costPerCPU
            return childCost + sortCost
            
        case .limit(_, let child):
            return await estimateCost(plan: child) * 0.1  // Assume early termination
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
    private func estimateJoinCost(left: QueryPlanNode, right: QueryPlanNode) async -> Double {
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
    private func estimateCardinality(plan: QueryPlanNode) async -> Int {
        switch plan {
        case .scan(let table):
            return await statistics.getRowCount(table: table)
            
        case .indexScan(let table, _, _):
            return await statistics.getRowCount(table: table) / 10  // Assume 10% selectivity
            
        case .filter(_, let child):
            let childCard = await estimateCardinality(plan: child)
            return childCard / 10  // Assume 10% selectivity
            
        case .project(_, let child):
            return await estimateCardinality(plan: child)
            
        case .join(let left, let right, _):
            let leftCard = await estimateCardinality(plan: left)
            let rightCard = await estimateCardinality(plan: right)
            return leftCard * rightCard / 10  // Assume 10% join selectivity
            
        case .aggregate(_, _, let child):
            return await estimateCardinality(plan: child) / 100  // Assume groups
            
        case .sort(_, let child):
            return await estimateCardinality(plan: child)
            
        case .limit(let count, _):
            return count
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

/// Statistics manager interface
public actor StatisticsManager {
    private var tableStats: [String: TableStatistics] = [:]
    
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
    
    public func updateStatistics(table: String, stats: TableStatistics) {
        tableStats[table] = stats
    }
}

/// Table statistics
public struct TableStatistics {
    public let pageCount: Int
    public let rowCount: Int
    public let avgRowSize: Int
    
    public init(pageCount: Int, rowCount: Int, avgRowSize: Int) {
        self.pageCount = pageCount
        self.rowCount = rowCount
        self.avgRowSize = avgRowSize
    }
}

