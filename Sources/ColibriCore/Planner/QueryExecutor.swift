//
//  QueryExecutor.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-26.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Query execution engine implementing the Volcano model.

import Foundation
import os.log

/// Query execution engine
public final class QueryExecutor {
    private let logger = Logger(subsystem: "com.colibridb.query", category: "executor")
    private let database: Database
    private let planner: QueryPlanner
    private let costModel: CostModel
    
    public init(database: Database) {
        self.database = database
        self.planner = QueryPlanner(database: database)
        self.costModel = CostModel(database: database)
    }
    
    /// Executes a query request
    public func execute(request: QueryRequest, context: ExecutionContext) throws -> QueryResult {
        logger.info("Executing query: \(request.root.name)")
        
        let startTime = Date()
        defer {
            let duration = Date().timeIntervalSince(startTime)
            logger.info("Query completed in \(duration)s")
        }
        
        // Plan the query
        let plan = try planner.plan(request: request, context: context)
        
        // Execute the plan
        let result = try executePlan(plan, context: context)
        
        return result
    }
    
    /// Executes a plan operator
    private func executePlan(_ plan: PlanOperator, context: ExecutionContext) throws -> QueryResult {
        var rows: [PlanRow] = []
        
        try plan.open(context: context)
        defer { try? plan.close() }
        
        while let row = try plan.next() {
            rows.append(row)
        }
        
        return QueryResult(rows: rows, executionTime: Date().timeIntervalSince1970)
    }
    
    /// Executes a simple SELECT query
    public func executeSelect(table: String, columns: [String]? = nil, whereClause: String? = nil, context: ExecutionContext) throws -> QueryResult {
        logger.info("Executing SELECT on table: \(table)")
        
        // Parse WHERE clause if provided
        var predicates: [QueryPredicate] = []
        if let whereClause = whereClause {
            predicates = try parseWhereClause(whereClause)
        }
        
        // Create query request
        let tableRef = QueryTableRef(
            name: table,
            predicates: predicates,
            projection: columns
        )
        
        let request = QueryRequest(root: tableRef)
        
        return try execute(request: request, context: context)
    }
    
    /// Executes a simple INSERT query
    public func executeInsert(table: String, values: [String: Value], context: ExecutionContext) throws -> InsertResult {
        logger.info("Executing INSERT into table: \(table)")
        
        let startTime = Date()
        defer {
            let duration = Date().timeIntervalSince(startTime)
            logger.info("INSERT completed in \(duration)s")
        }
        
        // Insert the row
        let rid = try database.insert(into: table, row: values)
        
        return InsertResult(rid: rid, executionTime: Date().timeIntervalSince1970)
    }
    
    /// Executes a simple UPDATE query
    public func executeUpdate(table: String, values: [String: Value], whereClause: String? = nil, context: ExecutionContext) throws -> UpdateResult {
        logger.info("Executing UPDATE on table: \(table)")
        
        let startTime = Date()
        defer {
            let duration = Date().timeIntervalSince(startTime)
            logger.info("UPDATE completed in \(duration)s")
        }
        
        // Parse WHERE clause if provided
        var predicates: [QueryPredicate] = []
        if let whereClause = whereClause {
            predicates = try parseWhereClause(whereClause)
        }
        
        // Find rows to update
        let tableRef = QueryTableRef(name: table, predicates: predicates)
        let request = QueryRequest(root: tableRef)
        let result = try execute(request: request, context: context)
        
        var updatedCount = 0
        for row in result.rows {
            // Update the row
            // Row modification not supported in MVP
            // updatedRow[key] = value
            
            // This would need to be implemented in the database
            // For now, just count the rows
            updatedCount += 1
        }
        
        return UpdateResult(updatedCount: updatedCount, executionTime: Date().timeIntervalSince1970)
    }
    
    /// Executes a simple DELETE query
    public func executeDelete(table: String, whereClause: String? = nil, context: ExecutionContext) throws -> DeleteResult {
        logger.info("Executing DELETE from table: \(table)")
        
        let startTime = Date()
        defer {
            let duration = Date().timeIntervalSince(startTime)
            logger.info("DELETE completed in \(duration)s")
        }
        
        // Parse WHERE clause if provided
        var predicates: [QueryPredicate] = []
        if let whereClause = whereClause {
            predicates = try parseWhereClause(whereClause)
        }
        
        // Find rows to delete
        let tableRef = QueryTableRef(name: table, predicates: predicates)
        let request = QueryRequest(root: tableRef)
        let result = try execute(request: request, context: context)
        
        var deletedCount = 0
        for row in result.rows {
            // Delete the row
            // This would need to be implemented in the database
            // For now, just count the rows
            deletedCount += 1
        }
        
        return DeleteResult(deletedCount: deletedCount, executionTime: Date().timeIntervalSince1970)
    }
    
    /// Parses a WHERE clause into predicates
    private func parseWhereClause(_ whereClause: String) throws -> [QueryPredicate] {
        // Simple WHERE clause parser
        // This is a basic implementation - a full parser would be more complex
        
        let tokens = whereClause.components(separatedBy: .whitespacesAndNewlines).filter { !$0.isEmpty }
        var predicates: [QueryPredicate] = []
        
        var i = 0
        while i < tokens.count {
            let column = tokens[i]
            i += 1
            
            guard i < tokens.count else { break }
            let operatorToken = tokens[i]
            i += 1
            
            guard i < tokens.count else { break }
            let valueToken = tokens[i]
            i += 1
            
            let op: QueryPredicateOperator
            switch operatorToken.uppercased() {
            case "=", "==":
                op = .equals
            case ">=":
                op = .greaterOrEqual
            case "<=":
                op = .lessOrEqual
            case ">":
                op = .greaterOrEqual
            case "<":
                op = .lessOrEqual
            default:
                throw QueryExecutionError.invalidPredicate
            }
            
            let value = parseValue(valueToken)
            let predicate = QueryPredicate(column: column, op: op, value: value)
            predicates.append(predicate)
            
            // Skip AND/OR if present
            if i < tokens.count && (tokens[i].uppercased() == "AND" || tokens[i].uppercased() == "OR") {
                i += 1
            }
        }
        
        return predicates
    }
    
    /// Parses a value string into a Value type
    private func parseValue(_ value: String) -> Value {
        if value.uppercased() == "NULL" {
            return .null
        }
        
        if value.hasPrefix("'") && value.hasSuffix("'") {
            let startIndex = value.index(after: value.startIndex)
            let endIndex = value.index(before: value.endIndex)
            return .string(String(value[startIndex..<endIndex]))
        }
        
        if let intValue = Int64(value) {
            return .int(intValue)
        }
        
        if let doubleValue = Double(value) {
            return .double(doubleValue)
        }
        
        if value.uppercased() == "TRUE" {
            return .bool(true)
        }
        if value.uppercased() == "FALSE" {
            return .bool(false)
        }
        
        return .string(value)
    }
}

/// Query result
public struct QueryResult {
    public let rows: [PlanRow]
    public let executionTime: TimeInterval
    public let rowCount: Int
    
    public init(rows: [PlanRow], executionTime: TimeInterval) {
        self.rows = rows
        self.executionTime = executionTime
        self.rowCount = rows.count
    }
}

/// Insert result
public struct InsertResult {
    public let rid: RID
    public let executionTime: TimeInterval
    
    public init(rid: RID, executionTime: TimeInterval) {
        self.rid = rid
        self.executionTime = executionTime
    }
}

/// Update result
public struct UpdateResult {
    public let updatedCount: Int
    public let executionTime: TimeInterval
    
    public init(updatedCount: Int, executionTime: TimeInterval) {
        self.updatedCount = updatedCount
        self.executionTime = executionTime
    }
}

/// Delete result
public struct DeleteResult {
    public let deletedCount: Int
    public let executionTime: TimeInterval
    
    public init(deletedCount: Int, executionTime: TimeInterval) {
        self.deletedCount = deletedCount
        self.executionTime = executionTime
    }
}

/// Query execution statistics
public struct QueryExecutionStats {
    public let totalTime: TimeInterval
    public let planningTime: TimeInterval
    public let executionTime: TimeInterval
    public let rowsProcessed: Int
    public let memoryUsed: Int
    public let ioOperations: Int
    
    public init(totalTime: TimeInterval, planningTime: TimeInterval, executionTime: TimeInterval, rowsProcessed: Int, memoryUsed: Int, ioOperations: Int) {
        self.totalTime = totalTime
        self.planningTime = planningTime
        self.executionTime = executionTime
        self.rowsProcessed = rowsProcessed
        self.memoryUsed = memoryUsed
        self.ioOperations = ioOperations
    }
}

/// Query execution context with additional options
public struct AdvancedExecutionContext {
    public let database: Database
    public let transactionId: UInt64
    public let isolationLevel: IsolationLevel
    public let timeout: TimeInterval?
    
    public let maxMemory: Int?
    public let parallelism: Int?
    public let useCache: Bool
    public let cacheTimeout: TimeInterval?
    
    public init(database: Database, 
                transactionId: UInt64? = nil, 
                isolationLevel: IsolationLevel = .readCommitted, 
                timeout: TimeInterval? = nil,
                maxMemory: Int? = nil,
                parallelism: Int? = nil,
                useCache: Bool = true,
                cacheTimeout: TimeInterval? = 300) {
        self.database = database
        self.transactionId = transactionId ?? 0
        self.isolationLevel = isolationLevel
        self.timeout = timeout
        self.maxMemory = maxMemory
        self.parallelism = parallelism
        self.useCache = useCache
        self.cacheTimeout = cacheTimeout
    }
}

/// Query cache for result caching
public final class QueryCache {
    private var cache: [String: (result: QueryResult, timestamp: TimeInterval)] = [:]
    private let maxSize: Int
    private let timeout: TimeInterval
    private let lock = NSLock()
    
    public init(maxSize: Int = 1000, timeout: TimeInterval = 300) {
        self.maxSize = maxSize
        self.timeout = timeout
    }
    
    public func get(key: String) -> QueryResult? {
        lock.lock()
        defer { lock.unlock() }
        
        guard let entry = cache[key] else { return nil }
        
        // Check if entry has expired
        if Date().timeIntervalSince1970 - entry.timestamp > timeout {
            cache.removeValue(forKey: key)
            return nil
        }
        
        return entry.result
    }
    
    public func set(key: String, result: QueryResult) {
        lock.lock()
        defer { lock.unlock() }
        
        // Remove oldest entries if cache is full
        if cache.count >= maxSize {
            let oldestKey = cache.min { $0.value.timestamp < $1.value.timestamp }?.key
            if let key = oldestKey {
                cache.removeValue(forKey: key)
            }
        }
        
        cache[key] = (result: result, timestamp: Date().timeIntervalSince1970)
    }
    
    public func clear() {
        lock.lock()
        defer { lock.unlock() }
        cache.removeAll()
    }
    
    public func remove(key: String) {
        lock.lock()
        defer { lock.unlock() }
        cache.removeValue(forKey: key)
    }
}

/// Query execution monitor for performance monitoring
public final class QueryExecutionMonitor {
    private let logger = Logger(subsystem: "com.colibridb.query", category: "monitor")
    private var activeQueries: [String: QueryExecutionStats] = [:]
    private let lock = NSLock()
    
    public init() {}
    
    public func startQuery(_ queryId: String) {
        lock.lock()
        defer { lock.unlock() }
        
        let stats = QueryExecutionStats(
            totalTime: 0,
            planningTime: 0,
            executionTime: 0,
            rowsProcessed: 0,
            memoryUsed: 0,
            ioOperations: 0
        )
        activeQueries[queryId] = stats
    }
    
    public func endQuery(_ queryId: String, stats: QueryExecutionStats) {
        lock.lock()
        defer { lock.unlock() }
        
        activeQueries.removeValue(forKey: queryId)
        logger.info("Query \(queryId) completed: \(stats.totalTime)s, \(stats.rowsProcessed) rows")
    }
    
    public func getActiveQueries() -> [String: QueryExecutionStats] {
        lock.lock()
        defer { lock.unlock() }
        return activeQueries
    }
    
    public func getQueryStats(_ queryId: String) -> QueryExecutionStats? {
        lock.lock()
        defer { lock.unlock() }
        return activeQueries[queryId]
    }
}
