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

// MARK: - Query Plan Node

/// Physical query plan node
public indirect enum QueryPlanNode: Sendable {
    case scan(table: String)
    case indexScan(table: String, index: String, key: String)
    case filter(column: String?, predicate: @Sendable (Row) -> Bool, child: QueryPlanNode)
    case project(columns: [String], child: QueryPlanNode)
    case sort(columns: [String], child: QueryPlanNode)
    case limit(count: Int, child: QueryPlanNode)
    case join(left: QueryPlanNode, right: QueryPlanNode, condition: String)
    case aggregate(function: String, column: String, child: QueryPlanNode)
}

/// Query optimizer for cost-based optimization
/// Corresponds to TLA+ module: QueryOptimizer.tla
public actor QueryOptimizer {
    // MARK: - Dependencies
    
    /// Catalog Manager - **Catalog-First**: Query Optimizer MUST use Catalog for:
    /// - Table metadata (columns, constraints) for validation
    /// - Index metadata for index selection
    /// - Statistics for cost estimation
    /// - All metadata comes from Catalog (single source of truth)
    private let catalog: Catalog
    private let statistics: StatisticsMaintenanceManager
    
    // MARK: - Cost Model Constants
    
    /// Cost per page I/O
    private static let costPerPageIO: Double = 1.0
    
    /// Cost per CPU operation
    private static let costPerCPU: Double = 0.01
    
    /// Cost per tuple
    private static let costPerTuple: Double = 0.001
    
    // MARK: - Initialization
    
    /// Initialize Query Optimizer
    /// - Parameters:
    ///   - catalog: **Catalog-First**: Catalog Manager (REQUIRED)
    ///   - statistics: Statistics Maintenance Manager
    public init(catalog: Catalog, statistics: StatisticsMaintenanceManager) {
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
        
        // **Catalog-First**: Get indexes from Catalog for index selection
        // Note: Catalog wrapper returns TableDefinition, we need to get indexes from CatalogManager
        let catalogManager = await catalog.getCatalogManager()
        let indexes = await catalogManager.getIndexes(for: plan.table)
        
        // Generate index scan plans if applicable
        for index in indexes {
            if let key = plan.filterKey,
               let filterColumn = plan.filterColumn,
               index.columns.contains(filterColumn) {
                candidates.append(.indexScan(
                    table: plan.table,
                    index: index.name,
                    key: encodeFilterValue(key)
                ))
            }
        }
        
        // Apply filters
        if let predicate = plan.predicate {
            candidates = candidates.map { candidate in
                .filter(column: plan.filterColumn, predicate: predicate, child: candidate)
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
            
        case .filter(let column, _, let child):
            let childCost = await estimateCost(plan: child)
            if let table = baseTable(of: child), let column {
                let selectivity = await equalitySelectivity(table: table, column: column)
                let childCard = await estimateCardinality(plan: child)
                return childCost + (Double(childCard) * selectivity * Self.costPerTuple)
            }
            return childCost * 1.1
            
        case .project(_, let child):
            let childCost = await estimateCost(plan: child)
            return childCost + (childCost * Self.costPerCPU)
            
        case .join(let left, let right, _):
            return await estimateJoinCost(left: left, right: right)
            
        case .aggregate(_, _, let child):
            let childCost = await estimateCost(plan: child)
            return childCost + (childCost * 0.5)
            
        case .sort(_, let child):
            let childCost = await estimateCost(plan: child)
            let cardinality = await estimateCardinality(plan: child)
            let sortCost = Double(max(cardinality, 1)) * log2(Double(max(cardinality, 1))) * Self.costPerCPU
            return childCost + sortCost
            
        case .limit(_, let child):
            let childCost = await estimateCost(plan: child)
            return childCost * 0.1
        }
    }
    
    /// Estimate scan cost
    private func estimateScanCost(table: String) async -> Double {
        if let stats = await statistics.getTableStatistics(table) {
            return Double(max(Int(stats.pageCount), 1)) * Self.costPerPageIO
        }
        return 100.0 * Self.costPerPageIO
    }
    
    /// Estimate index scan cost
    private func estimateIndexScanCost(table: String, index: String) async -> Double {
        if let stats = await statistics.getTableStatistics(table) {
            let rowCount = max(Int(stats.rowCount), 1)
            let traversalCost = 3 * Self.costPerPageIO  // assume B+Tree height 3
            let fetchCost = Double(rowCount) * 0.1 * Self.costPerTuple
            return traversalCost + fetchCost
        }
        return await estimateScanCost(table: table) * 0.3
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
            if let stats = await statistics.getTableStatistics(table) {
                return max(Int(stats.rowCount), 1)
            }
            return 1000
            
        case .indexScan(let table, _, _):
            let base = await estimateCardinality(plan: .scan(table: table))
            return max(base / 10, 1)
            
        case .filter(let column, _, let child):
            let childCard = await estimateCardinality(plan: child)
            if let table = baseTable(of: child), let column {
                let sel = await equalitySelectivity(table: table, column: column)
                return max(Int(Double(childCard) * sel), 1)
            }
            return max(childCard / 10, 1)
            
        case .project(_, let child):
            return await estimateCardinality(plan: child)
            
        case .join(let left, let right, _):
            let leftCard = await estimateCardinality(plan: left)
            let rightCard = await estimateCardinality(plan: right)
            return max((leftCard * rightCard) / 10, 1)
            
        case .aggregate(_, _, let child):
            return max(await estimateCardinality(plan: child) / 100, 1)
            
        case .sort(_, let child):
            return await estimateCardinality(plan: child)
            
        case .limit(let count, _):
            return count
        }
    }
    
    private func encodeFilterValue(_ value: Value) -> String {
        switch value {
        case .int(let v): return String(v)
        case .double(let v): return String(v)
        case .bool(let v): return v ? "1" : "0"
        case .string(let v): return v
        case .decimal(let v): return NSDecimalNumber(decimal: v).stringValue
        case .date(let v): return String(v.timeIntervalSince1970)
        case .bytes(let data): return data.base64EncodedString()
        case .null: return "NULL"
        }
    }
    
    private func baseTable(of plan: QueryPlanNode) -> String? {
        switch plan {
        case .scan(let table):
            return table
        case .indexScan(let table, _, _):
            return table
        case .filter(_, _, let child),
             .project(_, let child),
             .sort(_, let child),
             .limit(_, let child),
             .aggregate(_, _, let child):
            return baseTable(of: child)
        case .join(let left, _, _):
            return baseTable(of: left)
        }
    }
    
    private func equalitySelectivity(table: String, column: String) async -> Double {
        let selectivity = await statistics.estimateSelectivity(table: table, column: column, predicate: "=")
        return min(max(selectivity, 0.0001), 1.0)
    }
}

// MARK: - Supporting Types

/// Logical query plan
public struct LogicalPlan: @unchecked Sendable {
    public let table: String
    public let predicate: (@Sendable (Row) -> Bool)?
    public let filterKey: Value?
    public let filterColumn: String?
    public let projection: [String]?
    public let sortColumns: [String]?
    public let limit: Int?
    
    public init(
        table: String,
        predicate: (@Sendable (Row) -> Bool)? = nil,
        filterKey: Value? = nil,
        filterColumn: String? = nil,
        projection: [String]? = nil,
        sortColumns: [String]? = nil,
        limit: Int? = nil
    ) {
        self.table = table
        self.predicate = predicate
        self.filterKey = filterKey
        self.filterColumn = filterColumn
        self.projection = projection
        self.sortColumns = sortColumns
        self.limit = limit
    }
}


