//
//  QueryExecutorManager.swift
//  ColibrìDB Query Executor Manager
//
//  Based on: spec/QueryExecutor.tla
//  Implements: Query execution pipeline with operators
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//

import Foundation

// MARK: - Query Executor Manager

/// Query Executor Manager for database query execution
/// Corresponds to TLA+ module: QueryExecutor.tla
public actor SQLQueryExecutorManager {
    
    // MARK: - State Variables (TLA+ vars)
    
    /// Scan states
    /// TLA+: scanState \in [String -> QueryScanState]
    private var scanStates: [String: QueryScanState] = [:]
    
    /// Join states
    /// TLA+: joinState \in [String -> QueryJoinState]
    private var joinStates: [String: QueryJoinState] = [:]
    
    /// Sort states
    /// TLA+: sortState \in [String -> QuerySortState]
    private var sortStates: [String: QuerySortState] = [:]
    
    /// Projection states
    /// TLA+: projectionState \in [String -> QueryProjectionState]
    private var projectionStates: [String: QueryProjectionState] = [:]
    
    /// Select states
    /// TLA+: selectState \in [String -> QuerySelectState]
    private var selectStates: [String: QuerySelectState] = [:]
    
    /// Output buffers
    /// TLA+: outputBuffer \in [String -> Seq(Row)]
    private var outputBuffers: [String: [Row]] = [:]
    
    /// Pipeline active
    /// TLA+: pipelineActive \in BOOLEAN
    private var pipelineActive: Bool = false
    
    // MARK: - Dependencies
    
    /// Storage manager
    private let storageManager: StorageManagerActor
    
    /// Index manager
    private let indexManager: IndexManagerActor
    
    // MARK: - Initialization
    
    public init(storageManager: StorageManagerActor, indexManager: IndexManagerActor) {
        self.storageManager = storageManager
        self.indexManager = indexManager
        
        // TLA+ Init
        self.scanStates = [:]
        self.joinStates = [:]
        self.sortStates = [:]
        self.projectionStates = [:]
        self.selectStates = [:]
        self.outputBuffers = [:]
        self.pipelineActive = false
    }
    
    // MARK: - Pipeline Operations
    
    /// Start pipeline
    /// TLA+ Action: StartPipeline()
    public func startPipeline() async {
        pipelineActive = true
    }
    
    /// Stop pipeline
    /// TLA+ Action: StopPipeline()
    public func stopPipeline() async {
        pipelineActive = false
    }
    
    // MARK: - Scan Operator
    
    /// Create scan operator
    /// TLA+ Action: CreateScanOperator(operatorId, table)
    public func createScanOperator(operatorId: String, table: String) async throws {
        let scanState = QueryScanState(
            table: table,
            currentRID: nil,
            exhausted: false
        )
        scanStates[operatorId] = scanState
    }
    
    /// Execute scan operator
    /// TLA+ Action: ExecuteScanOperator(operatorId)
    public func executeScanOperator(operatorId: String) async throws {
        guard var scanState = scanStates[operatorId] else {
            throw QueryExecutorError.operatorNotFound
        }
        
        // TLA+: Scan table
        while !scanState.exhausted {
            if let row = try await fetchNextRow(tableName: scanState.table, rid: scanState.currentRID ?? RID(pageID: 0, slotID: 0)) {
                outputBuffers[operatorId, default: []].append(row)
                // Update RID (simplified)
                scanState.currentRID = RID(pageID: (scanState.currentRID?.pageID ?? 0) + 1, slotID: 0)
            } else {
                scanState.exhausted = true
            }
        }
        
        scanStates[operatorId] = scanState
    }
    
    // MARK: - Join Operator
    
    /// Create join operator
    /// TLA+ Action: CreateJoinOperator(operatorId, leftTable, rightTable)
    public func createJoinOperator(operatorId: String, leftTable: String, rightTable: String) async throws {
        let joinState = QueryJoinState(
            leftTable: leftTable,
            rightTable: rightTable,
            exhausted: false
        )
        joinStates[operatorId] = joinState
    }
    
    /// Execute join operator
    /// TLA+ Action: ExecuteJoinOperator(operatorId)
    public func executeJoinOperator(operatorId: String) async throws {
        guard var joinState = joinStates[operatorId] else {
            throw QueryExecutorError.operatorNotFound
        }
        
        // TLA+: Join tables (simplified nested loop)
        let leftTable = joinState.leftTable
        let rightTable = joinState.rightTable
        
        while !joinState.exhausted {
            if let leftRow = try await fetchNextRow(tableName: leftTable, rid: RID(pageID: 0, slotID: 0)) {
                if let rightRow = try await fetchNextRow(tableName: rightTable, rid: RID(pageID: 0, slotID: 0)) {
                    var joinedRow = leftRow
                    joinedRow.merge(rightRow) { (_, new) in new }
                    outputBuffers[operatorId, default: []].append(joinedRow)
                }
            }
            joinState.exhausted = true
        }
        
        joinStates[operatorId] = joinState
    }
    
    // MARK: - Aggregate Operator
    
    /// Execute aggregate operator
    /// TLA+ Action: ExecuteAggregateOperator(operatorId, function)
    public func executeAggregateOperator(operatorId: String, function: String) async throws {
        guard let inputRows = outputBuffers[operatorId] else {
            throw QueryExecutorError.operatorNotFound
        }
        
        switch function {
        case "count":
            outputBuffers[operatorId] = [["count": Value.int(Int64(inputRows.count))]]
        case "sum":
            var sum: Int64 = 0
            for row in inputRows {
                for (_, value) in row {
                    if case .int(let val) = value {
                        sum += val
                        break
                    }
                }
            }
            outputBuffers[operatorId] = [["sum": Value.int(sum)]]
        case "avg":
            var sum: Double = 0.0
            var count = 0
            for row in inputRows {
                for (_, value) in row {
                    if case .int(let val) = value {
                        sum += Double(val)
                        count += 1
                        break
                    }
                }
            }
            let avg = count > 0 ? sum / Double(count) : 0.0
            outputBuffers[operatorId] = [["avg": Value.double(avg)]]
        case "min":
            var minVal: Int64? = nil
            for row in inputRows {
                for (_, value) in row {
                    if case .int(let val) = value {
                        minVal = minVal.map { min($0, val) } ?? val
                        break
                    }
                }
            }
            outputBuffers[operatorId] = [["min": Value.int(minVal ?? 0)]]
        case "max":
            var maxVal: Int64? = nil
            for row in inputRows {
                for (_, value) in row {
                    if case .int(let val) = value {
                        maxVal = maxVal.map { max($0, val) } ?? val
                        break
                    }
                }
            }
            outputBuffers[operatorId] = [["max": Value.int(maxVal ?? 0)]]
        default:
            break
        }
    }
    
    // MARK: - Sort Operator
    
    /// Create sort operator
    /// TLA+ Action: CreateSortOperator(operatorId, column)
    public func createSortOperator(operatorId: String, column: String) async throws {
        let sortState = QuerySortState(
            column: column,
            ascending: true
        )
        sortStates[operatorId] = sortState
    }
    
    /// Execute sort operator
    /// TLA+ Action: ExecuteSortOperator(operatorId)
    public func executeSortOperator(operatorId: String) async throws {
        guard let sortState = sortStates[operatorId],
              var inputRows = outputBuffers[operatorId] else {
            throw QueryExecutorError.operatorNotFound
        }
        
        inputRows.sort { row1, row2 in
            compareRows(row1: row1, row2: row2, column: sortState.column)
        }
        
        outputBuffers[operatorId] = inputRows
    }
    
    // MARK: - Projection Operator
    
    /// Create projection operator
    /// TLA+ Action: CreateProjectionOperator(operatorId, columns)
    public func createProjectionOperator(operatorId: String, columns: [String]) async throws {
        let projectionState = QueryProjectionState(columns: columns)
        projectionStates[operatorId] = projectionState
    }
    
    /// Execute projection operator
    /// TLA+ Action: ExecuteProjectionOperator(operatorId)
    public func executeProjectionOperator(operatorId: String) async throws {
        guard let projectionState = projectionStates[operatorId],
              let inputRows = outputBuffers[operatorId] else {
            throw QueryExecutorError.operatorNotFound
        }
        
        let projectedRows = inputRows.map { row in
            applyProjection(row: row, columns: projectionState.columns)
        }
        
        outputBuffers[operatorId] = projectedRows
    }
    
    // MARK: - Select Operator
    
    /// Create select operator
    /// TLA+ Action: CreateSelectOperator(operatorId, predicate)
    public func createSelectOperator(operatorId: String, predicate: String) async throws {
        let selectState = QuerySelectState(predicate: predicate)
        selectStates[operatorId] = selectState
    }
    
    /// Execute select operator
    /// TLA+ Action: ExecuteSelectOperator(operatorId)
    public func executeSelectOperator(operatorId: String) async throws {
        guard let selectState = selectStates[operatorId],
              let inputRows = outputBuffers[operatorId] else {
            throw QueryExecutorError.operatorNotFound
        }
        
        let selectedRows = inputRows.filter { row in
            applyPredicate(row: row, predicate: selectState.predicate)
        }
        
        outputBuffers[operatorId] = selectedRows
    }
    
    // MARK: - Helper Functions
    
    /// Fetch next row
    /// TLA+ Function: FetchNextRow(tableName, rid)
    private func fetchNextRow(tableName: String, rid: RID) async throws -> Row? {
        // TLA+: Fetch row from storage
        // Simplified implementation - would need proper storage integration
        return ["id": Value.int(Int64(rid.pageID)), "data": Value.string("mock_data")]
    }
    
    /// Apply predicate
    /// TLA+ Function: ApplyPredicate(row, predicate)
    private func applyPredicate(row: Row, predicate: String) -> Bool {
        // Simplified predicate evaluation
        return true
    }
    
    /// Apply projection
    /// TLA+ Function: ApplyProjection(row, columns)
    private func applyProjection(row: Row, columns: [String]) -> Row {
        var projected: Row = [:]
        for col in columns {
            if let value = row[col] {
                projected[col] = value
            }
        }
        return projected
    }
    
    /// Compare rows
    /// TLA+ Function: CompareRows(row1, row2, column)
    private func compareValues(_ value1: Value, _ value2: Value) -> Bool {
        switch (value1, value2) {
        case (.int(let v1), .int(let v2)):
            return v1 < v2
        case (.string(let v1), .string(let v2)):
            return v1 < v2
        case (.double(let v1), .double(let v2)):
            return v1 < v2
        default:
            return false
        }
    }
    
    private func compareRows(row1: Row, row2: Row, column: String) -> Bool {
        let value1 = row1[column] ?? Value.null
        let value2 = row2[column] ?? Value.null
        return compareValues(value1, value2)
    }
    
    // MARK: - Query Operations
    
    /// Get operator state
    public func getOperatorState(operatorId: String) -> [String: Any]? {
        if let scanState = scanStates[operatorId] {
            return ["type": "scan", "table": scanState.table, "exhausted": scanState.exhausted]
        }
        if let joinState = joinStates[operatorId] {
            return ["type": "join", "leftTable": joinState.leftTable, "rightTable": joinState.rightTable, "exhausted": joinState.exhausted]
        }
        if let sortState = sortStates[operatorId] {
            return ["type": "sort", "column": sortState.column, "ascending": sortState.ascending]
        }
        if let projectionState = projectionStates[operatorId] {
            return ["type": "projection", "columns": projectionState.columns]
        }
        if let selectState = selectStates[operatorId] {
            return ["type": "select", "predicate": selectState.predicate]
        }
        return nil
    }
    
    /// Get output buffer
    public func getOutputBuffer(operatorId: String) -> [Row] {
        return outputBuffers[operatorId] ?? []
    }
    
    /// Get all output buffers
    public func getOutputBuffers() -> [String: [Row]] {
        return outputBuffers
    }
    
    /// Clear output buffer
    public func clearOutputBuffer(operatorId: String) async {
        outputBuffers.removeValue(forKey: operatorId)
    }
    
    /// Clear all output buffers
    public func clearAllOutputBuffers() async {
        outputBuffers.removeAll()
    }
}

// MARK: - Supporting Types

/// Query scan state
public struct QueryScanState: Sendable {
    let table: String
    var currentRID: RID?
    var exhausted: Bool
}

/// Query join state
public struct QueryJoinState: Sendable {
    let leftTable: String
    let rightTable: String
    var exhausted: Bool
}

/// Query sort state
public struct QuerySortState: Sendable {
    let column: String
    let ascending: Bool
}

/// Query projection state
public struct QueryProjectionState: Sendable {
    let columns: [String]
}

/// Query select state
public struct QuerySelectState: Sendable {
    let predicate: String
}

/// Query executor error
public enum QueryExecutorError: Error, LocalizedError {
    case operatorNotFound
    case pipelineNotActive
    case invalidOperator
    
    public var errorDescription: String? {
        switch self {
        case .operatorNotFound:
            return "Operator not found"
        case .pipelineNotActive:
            return "Pipeline not active"
        case .invalidOperator:
            return "Invalid operator"
        }
    }
}
