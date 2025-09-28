//
//  Database+Planner.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// Theme: Planner facade exposing cost-based execution to the database API.

import Foundation

extension Database {
    /// Executes a query request through the Volcano planner/executor pipeline.
    /// - Parameters:
    ///   - request: Logical query request.
    ///   - tid: Optional transaction identifier to run within.
    /// - Returns: Array of rows (qualified column dictionary) representing the result set.
    public func executeQuery(_ request: QueryRequest, tid: UInt64? = nil) throws -> [[String: Value]] {
        if request.useMaterializedCache, let key = request.cacheKey {
            materializedViewLock.lock()
            if let cached = materializedViewCache[key] {
                materializedViewLock.unlock()
                return cached
            }
            materializedViewLock.unlock()
        }

        let planner = QueryPlanner(database: self)
        let context = ExecutionContext(database: self, transactionId: tid)
        let op = try planner.plan(request: request, context: context)
        let rows = try op.materialize(context: context)
        let result = rows.map { $0.values }

        if let key: String = request.cacheKey {
            materializedViewLock.lock()
            materializedViewCache[key] = result
            materializedViewLock.unlock()
        }
        return result
    }

    /// Clears a cached materialized view entry.
    /// - Parameter key: Cache key to invalidate.
    public func invalidateMaterializedView(key: String) {
        materializedViewLock.lock()
        materializedViewCache.removeValue(forKey: key)
        materializedViewLock.unlock()
    }
}
