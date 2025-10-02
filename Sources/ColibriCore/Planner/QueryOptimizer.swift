//
//  QueryOptimizer.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: 🚀 Query optimization utilities for enhanced performance

import Foundation
import os.log

/// 🚀 OPTIMIZATION: Query optimization utilities
public final class QueryOptimizer {
    
    /// 🚀 OPTIMIZATION: Plan cache for frequently executed queries
    private static nonisolated(unsafe) var planCache: [String: (plan: PlanOperator, timestamp: Date, hitCount: Int)] = [:]
    private static let planCacheMaxSize = 500
    private static let planCacheTimeout: TimeInterval = 1800 // 30 minutes
    private static let planCacheLock = NSLock()
    
    /// 🚀 OPTIMIZATION: Generate cache key for query request
    public static func generateCacheKey(for request: QueryRequest) -> String {
        var components: [String] = []
        
        // Root table and predicates
        components.append("table:\(request.root.name)")
        components.append("predicates:\(request.root.predicates.count)")
        
        // Joins
        components.append("joins:\(request.joins.count)")
        for join in request.joins {
            components.append("join:\(join.table.name)")
        }
        
        // Order by
        if !request.orderBy.isEmpty {
            components.append("orderBy:\(request.orderBy.count)")
        }
        
        // Limit
        if let limit = request.limit {
            components.append("limit:\(limit)")
        }
        
        return components.joined(separator: "|")
    }
    
    /// 🚀 OPTIMIZATION: Get cached plan if available and valid
    public static func getCachedPlan(key: String) -> PlanOperator? {
        planCacheLock.lock()
        defer { planCacheLock.unlock() }
        
        guard let cached = planCache[key] else { return nil }
        
        let age = Date().timeIntervalSince(cached.timestamp)
        if age > planCacheTimeout {
            planCache.removeValue(forKey: key)
            return nil
        }
        
        // Update hit count and timestamp
        planCache[key] = (plan: cached.plan, timestamp: Date(), hitCount: cached.hitCount + 1)
        
        print("🚀 Plan cache hit for key: \(key)")
        return cached.plan
    }
    
    /// 🚀 OPTIMIZATION: Cache a plan
    public static func cachePlan(_ plan: PlanOperator, key: String) {
        planCacheLock.lock()
        defer { planCacheLock.unlock() }
        
        planCache[key] = (plan: plan, timestamp: Date(), hitCount: 0)
        
        // Evict old entries if cache is full
        if planCache.count > planCacheMaxSize {
            let sortedEntries = planCache.sorted { 
                // Sort by hit count (descending) then by timestamp (ascending)
                if $0.value.hitCount != $1.value.hitCount {
                    return $0.value.hitCount > $1.value.hitCount
                }
                return $0.value.timestamp < $1.value.timestamp
            }
            
            let toRemove = sortedEntries.suffix(planCacheMaxSize / 4) // Remove 25%
            for (key, _) in toRemove {
                planCache.removeValue(forKey: key)
            }
        }
        
        print("🚀 Plan cached for key: \(key)")
    }
    
    /// 🚀 OPTIMIZATION: Apply predicate pushdown optimization
    public static func applyPredicatePushdown(_ request: QueryRequest) -> QueryRequest {
        var optimizedRequest = request
        
        // Simple predicate pushdown: move equality predicates to appropriate tables
        for (_, join) in request.joins.enumerated() {
            var rootPredicates = optimizedRequest.root.predicates
            var joinPredicates = join.table.predicates
            
            // Move predicates that reference join columns
            rootPredicates = rootPredicates.filter { predicate in
                if join.rightColumns.contains(predicate.column) {
                    joinPredicates.append(predicate)
                    return false
                }
                return true
            }
            
            optimizedRequest.root.predicates = rootPredicates
            // Note: We can't modify join.table.predicates directly due to immutability
            // This would require a more complex rewrite
        }
        
        return optimizedRequest
    }
    
    /// 🚀 OPTIMIZATION: Estimate join selectivity
    public static func estimateJoinSelectivity(_ join: QueryJoinSpec) -> Double {
        var selectivity = 0.1 // Default 10% selectivity
        
        // Adjust based on predicates
        for predicate in join.table.predicates {
            if let hint = predicate.selectivityHint {
                selectivity *= hint
            } else {
                switch predicate.op {
                case .equals:
                    selectivity *= 0.1
                case .greaterOrEqual, .lessOrEqual:
                    selectivity *= 0.3
                }
            }
        }
        
        return max(0.001, min(1.0, selectivity))
    }
    
    /// 🚀 OPTIMIZATION: Estimate row count for simple operators
    public static func estimateRowCount(_ planOperator: PlanOperator, database: Database) -> Int {
        switch planOperator {
        case let tableScan as TableScanOperator:
            let stats = try? database.getTableStatistics(tableScan.table)
            return Int(stats?.rowCount ?? 1000)
        case let indexScan as IndexScanOperator:
            let stats = try? database.getTableStatistics(indexScan.table)
            let baseRows = Int(stats?.rowCount ?? 1000)
            return max(1, Int(Double(baseRows) * 0.1)) // Assume 10% selectivity
        default:
            return 1000 // Default estimate
        }
    }
    
    /// 🚀 OPTIMIZATION: Clear plan cache
    public static func clearPlanCache() {
        planCacheLock.lock()
        defer { planCacheLock.unlock() }
        planCache.removeAll()
        print("🚀 Query plan cache cleared")
    }
    
    /// 🚀 OPTIMIZATION: Get plan cache statistics
    public static func getPlanCacheStats() -> (size: Int, hitRate: Double, oldestEntry: TimeInterval?) {
        planCacheLock.lock()
        defer { planCacheLock.unlock() }
        
        let totalHits = planCache.values.map { $0.hitCount }.reduce(0, +)
        let hitRate = planCache.isEmpty ? 0.0 : Double(totalHits) / Double(planCache.count)
        
        let oldestTimestamp = planCache.values.map { $0.timestamp }.min()
        let oldestAge = oldestTimestamp.map { Date().timeIntervalSince($0) }
        
        return (size: planCache.count, hitRate: hitRate, oldestEntry: oldestAge)
    }
    
    /// 🚀 OPTIMIZATION: Enhanced cost calculation with memory factor
    public static func enhancedCost(of planOperator: PlanOperator, costModel: CostModel) -> (cpu: Double, io: Double, memory: Double) {
        let baseCost = costModel.cost(of: planOperator)
        
        // Estimate memory usage
        let memoryCost: Double
        switch planOperator {
        case is HashJoinOperator:
            memoryCost = 10000.0 // Hash joins need significant memory
        case is SortOperator:
            memoryCost = 5000.0 // Sorts need memory for sorting
        default:
            memoryCost = 1000.0 // Default memory usage
        }
        
        return (cpu: baseCost.cpu, io: baseCost.io, memory: memoryCost)
    }
    
    /// 🚀 OPTIMIZATION: Suggest optimal parallelism level
    public static func suggestParallelism(for request: QueryRequest, database: Database) -> Int? {
        // Simple heuristic: use parallelism for large tables
        let stats = try? database.getTableStatistics(request.root.name)
        let rowCount = Int(stats?.rowCount ?? 0)
        
        if rowCount > 100000 {
            return min(4, max(2, rowCount / 50000)) // 2-4 threads for large tables
        }
        
        return nil // No parallelism for small tables
    }
}

// MARK: - 🚀 OPTIMIZATION: Enhanced QueryPlanner Extension

extension QueryPlanner {
    
    /// 🚀 OPTIMIZATION: Plan with caching and optimizations
    public func planWithOptimizations(request: QueryRequest, context: ExecutionContext) throws -> PlanOperator {
        let cacheKey = QueryOptimizer.generateCacheKey(for: request)
        
        // Check cache first
        if let cachedPlan = QueryOptimizer.getCachedPlan(key: cacheKey) {
            return cachedPlan
        }
        
        let startTime = Date()
        
        // Apply optimizations
        let optimizedRequest = QueryOptimizer.applyPredicatePushdown(request)
        
        // Use original planning logic
        let plan = try self.plan(request: optimizedRequest, context: context)
        
        // Cache the plan
        QueryOptimizer.cachePlan(plan, key: cacheKey)
        
        let duration = Date().timeIntervalSince(startTime)
        print("🚀 Query planned with optimizations in \(String(format: "%.3f", duration))s")
        
        return plan
    }
}

// MARK: - 🚀 OPTIMIZATION: Performance Monitoring

/// 🚀 OPTIMIZATION: Query performance monitor
public final class QueryPerformanceMonitor {
    // Disable concurrency warning as we use explicit locking
    nonisolated(unsafe) private static var queryStats: [String: (count: Int, totalTime: TimeInterval, avgTime: TimeInterval)] = [:]
    private static let statsLock = NSLock()
    
    /// Record query execution time
    public static func recordExecution(query: String, duration: TimeInterval) {
        statsLock.lock()
        defer { statsLock.unlock() }
        
        if var stats = queryStats[query] {
            stats.count += 1
            stats.totalTime += duration
            stats.avgTime = stats.totalTime / Double(stats.count)
            queryStats[query] = stats
        } else {
            queryStats[query] = (count: 1, totalTime: duration, avgTime: duration)
        }
    }
    
    /// Get performance statistics
    public static func getStats() -> [(query: String, count: Int, avgTime: TimeInterval)] {
        statsLock.lock()
        defer { statsLock.unlock() }
        
        return queryStats.map { (query: $0.key, count: $0.value.count, avgTime: $0.value.avgTime) }
            .sorted { $0.avgTime > $1.avgTime } // Sort by average time descending
    }
    
    /// Clear statistics
    public static func clearStats() {
        statsLock.lock()
        defer { statsLock.unlock() }
        queryStats.removeAll()
        print("🚀 Query performance statistics cleared")
    }
}
