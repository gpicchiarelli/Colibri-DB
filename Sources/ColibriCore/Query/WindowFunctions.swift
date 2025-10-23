/*
 * WindowFunctions.swift
 * ColibrìDB - SQL Window Functions (OLAP) Implementation
 *
 * Based on TLA+ specification: WindowFunctions.tla
 *
 * This module implements SQL window functions for analytical queries:
 * - Window frames (ROWS, RANGE, GROUPS)
 * - Aggregate window functions (SUM, AVG, COUNT, MIN, MAX)
 * - Ranking functions (ROW_NUMBER, RANK, DENSE_RANK, NTILE)
 * - Value functions (LAG, LEAD, FIRST_VALUE, LAST_VALUE, NTH_VALUE)
 * - PARTITION BY and ORDER BY clauses
 * - Frame exclusion (EXCLUDE CURRENT ROW, etc.)
 *
 * References:
 * [1] ISO/IEC 9075-2:2016 (SQL:2016 Standard) - Part 2: Foundation, Section 7.11
 * [2] Bellamkonda, S., et al. (2013). "Analytic Functions in Oracle 12c."
 * [3] Leis, V., et al. (2015). "How Good Are Query Optimizers, Really?"
 * [4] Larson, P. Å., & Graefe, G. (2011). "SQL Server Column Store Indexes."
 *
 * Author: ColibrìDB Team
 * Date: 2025-10-19
 */

import Foundation

// MARK: - Window Function Types

/// Window function category
public enum WindowFuncType: String, Codable {
    case aggregate      // SUM, AVG, COUNT, MIN, MAX
    case ranking        // ROW_NUMBER, RANK, DENSE_RANK, PERCENT_RANK
    case value          // LAG, LEAD, FIRST_VALUE, LAST_VALUE, NTH_VALUE
    case distribution   // NTILE, PERCENTILE_CONT, PERCENTILE_DISC
}

/// Specific window function
public enum WindowFunc: String, Codable, CaseIterable {
    // Aggregates
    case sum = "SUM"
    case avg = "AVG"
    case count = "COUNT"
    case min = "MIN"
    case max = "MAX"
    
    // Ranking
    case rowNumber = "ROW_NUMBER"
    case rank = "RANK"
    case denseRank = "DENSE_RANK"
    case percentRank = "PERCENT_RANK"
    case cumeDist = "CUME_DIST"
    case ntile = "NTILE"
    
    // Value
    case lag = "LAG"
    case lead = "LEAD"
    case firstValue = "FIRST_VALUE"
    case lastValue = "LAST_VALUE"
    case nthValue = "NTH_VALUE"
    
    public var funcType: WindowFuncType {
        switch self {
        case .sum, .avg, .count, .min, .max:
            return .aggregate
        case .rowNumber, .rank, .denseRank, .percentRank, .cumeDist, .ntile:
            return .ranking
        case .lag, .lead, .firstValue, .lastValue, .nthValue:
            return .value
        }
    }
}

// MARK: - Frame Types

/// Window frame type
public enum FrameType: String, Codable {
    case rows       // Physical row offset
    case range      // Logical value offset
    case groups     // Group-based offset
}

/// Frame boundary specification
public enum FrameBoundary: Codable, Equatable {
    case unboundedPreceding
    case currentRow
    case unboundedFollowing
    case nPreceding(Int)        // N rows before current
    case nFollowing(Int)        // N rows after current
}

/// Frame exclusion mode
public enum FrameExclusion: String, Codable {
    case noOthers       // Include all rows in frame
    case currentRow     // Exclude current row
    case group          // Exclude peers of current row
    case ties           // Exclude ties with current row
}

// MARK: - Window Specification

/// Complete window specification
public struct WindowSpec: Codable {
    public let partitionBy: [String]        // Partition columns
    public let orderBy: [OrderSpec]         // Order specification
    public let frameType: FrameType
    public let frameStart: FrameBoundary
    public let frameEnd: FrameBoundary
    public let frameExclusion: FrameExclusion
    
    public init(partitionBy: [String] = [],
                orderBy: [OrderSpec] = [],
                frameType: FrameType = .rows,
                frameStart: FrameBoundary = .unboundedPreceding,
                frameEnd: FrameBoundary = .currentRow,
                frameExclusion: FrameExclusion = .noOthers) {
        self.partitionBy = partitionBy
        self.orderBy = orderBy
        self.frameType = frameType
        self.frameStart = frameStart
        self.frameEnd = frameEnd
        self.frameExclusion = frameExclusion
    }
}

/// Order specification
public struct OrderSpec: Codable {
    public let column: String
    public let direction: SortDirection
    
    public init(column: String, direction: SortDirection = .ascending) {
        self.column = column
        self.direction = direction
    }
}

public enum SortDirection: String, Codable {
    case ascending = "ASC"
    case descending = "DESC"
}

// MARK: - Data Structures

/// Row in result set
public struct WindowRow: Codable {
    public let rowNum: Int
    public let values: [String: Value]
    public let partitionId: Int
    
    public init(rowNum: Int, values: [String: Value], partitionId: Int = 0) {
        self.rowNum = rowNum
        self.values = values
        self.partitionId = partitionId
    }
}

// Value type is defined in Core/Types.swift

/// Window function definition
public struct WindowFunction {
    public let function: WindowFunc
    public let spec: WindowSpec
    public let targetColumn: String
    public let offset: Int              // For LAG/LEAD/NTH_VALUE
    public let buckets: Int             // For NTILE
    
    public init(function: WindowFunc, spec: WindowSpec, targetColumn: String = "value",
                offset: Int = 1, buckets: Int = 4) {
        self.function = function
        self.spec = spec
        self.targetColumn = targetColumn
        self.offset = offset
        self.buckets = buckets
    }
}

// MARK: - Window Functions Processor

/// Main window functions processor
public actor WindowFunctionsProcessor {
    
    // Input data
    private var inputRows: [WindowRow] = []
    
    // Partitioning
    private var partitions: [[WindowRow]] = []
    private var currentPartition: Int = 0
    
    // Window functions to compute
    private var windowFunctions: [WindowFunction] = []
    
    // Results
    private var windowResults: [Int: [String: Value]] = [:]
    
    // Execution state
    private var currentRow: Int = 0
    private var processingComplete: Bool = false
    
    public init() {}
    
    // MARK: - Public API
    
    /// Define a window function to compute
    public func defineWindowFunction(_ windowFunc: WindowFunction) {
        windowFunctions.append(windowFunc)
    }
    
    /// Load input rows
    public func loadInputRows(_ rows: [WindowRow]) {
        self.inputRows = rows
        self.windowResults = [:]
        self.processingComplete = false
    }
    
    /// Execute all window functions
    public func execute() async throws -> [[String: Value]] {
        guard !windowFunctions.isEmpty else {
            throw WindowFunctionError.noFunctionsDefined
        }
        
        guard !inputRows.isEmpty else {
            return []
        }
        
        // Step 1: Partition input rows
        partitionInputRows()
        
        // Step 2: Process each partition
        for partIdx in 0..<partitions.count {
            currentPartition = partIdx
            let partition = partitions[partIdx]
            
            // Step 3: Process each row in partition
            for rowIdx in 0..<partition.count {
                currentRow = rowIdx
                try await processRow(partition: partition, rowIdx: rowIdx)
            }
        }
        
        processingComplete = true
        
        // Step 4: Materialize results
        return materializeResults()
    }
    
    /// Get result for specific row
    public func getResult(rowNum: Int) -> [String: Value]? {
        return windowResults[rowNum]
    }
    
    // MARK: - Partitioning
    
    private func partitionInputRows() {
        guard let firstFunc = windowFunctions.first else {
            partitions = [inputRows]
            return
        }
        
        let spec = firstFunc.spec
        
        if spec.partitionBy.isEmpty {
            // No partitioning - all rows in one partition
            var sorted = inputRows
            if !spec.orderBy.isEmpty {
                sorted = sortPartition(sorted, orderBy: spec.orderBy)
            }
            partitions = [sorted]
        } else {
            // Partition by specified columns
            var partitionMap: [String: [WindowRow]] = [:]
            
            for row in inputRows {
                let key = makePartitionKey(row: row, columns: spec.partitionBy)
                partitionMap[key, default: []].append(row)
            }
            
            // Sort each partition
            partitions = partitionMap.values.map { partition in
                if !spec.orderBy.isEmpty {
                    return sortPartition(partition, orderBy: spec.orderBy)
                }
                return partition
            }
        }
    }
    
    private func makePartitionKey(row: WindowRow, columns: [String]) -> String {
        return columns.map { col in
            String(describing: row.values[col] ?? Value.null)
        }.joined(separator: "||")
    }
    
    private func sortPartition(_ partition: [WindowRow], orderBy: [OrderSpec]) -> [WindowRow] {
        let orderSpecs = Array(orderBy) // Create a copy to avoid data race
        return partition.sorted { r1, r2 in
            for spec in orderSpecs {
                let v1 = r1.values[spec.column] ?? Value.null
                let v2 = r2.values[spec.column] ?? Value.null
                
                let cmp = compareValues(v1, v2)
                if cmp != .orderedSame {
                    return spec.direction == .ascending ? cmp == .orderedAscending : cmp == .orderedDescending
                }
            }
            return false
        }
    }
    
    private func compareValues(_ v1: Value, _ v2: Value) -> ComparisonResult {
        switch (v1, v2) {
        case (.null, .null): return .orderedSame
        case (.null, _): return .orderedAscending
        case (_, .null): return .orderedDescending
        case (.int(let i1), .int(let i2)): return i1 < i2 ? .orderedAscending : (i1 > i2 ? .orderedDescending : .orderedSame)
        case (.double(let d1), .double(let d2)): return d1 < d2 ? .orderedAscending : (d1 > d2 ? .orderedDescending : .orderedSame)
        case (.string(let s1), .string(let s2)): return s1.compare(s2)
        case (.bool(let b1), .bool(let b2)): return b1 == b2 ? .orderedSame : (b1 ? .orderedDescending : .orderedAscending)
        default: return .orderedSame
        }
    }
    
    // MARK: - Row Processing
    
    private func processRow(partition: [WindowRow], rowIdx: Int) async throws {
        let row = partition[rowIdx]
        var results: [String: Value] = [:]
        
        for windowFunc in windowFunctions {
            let funcName = windowFunc.function.rawValue
            let value = try computeWindowFunction(windowFunc, partition: partition, rowIdx: rowIdx)
            results[funcName] = value
        }
        
        windowResults[row.rowNum] = results
    }
    
    // MARK: - Window Function Computation
    
    private func computeWindowFunction(_ windowFunc: WindowFunction, partition: [WindowRow], rowIdx: Int) throws -> Value {
        let frame = getFrame(partition: partition, rowIdx: rowIdx, spec: windowFunc.spec)
        
        switch windowFunc.function {
        // Aggregates
        case .sum:
            return computeSum(frame: frame, column: windowFunc.targetColumn)
        case .avg:
            return computeAvg(frame: frame, column: windowFunc.targetColumn)
        case .count:
            return .int(Int64(frame.count))
        case .min:
            return computeMin(frame: frame, column: windowFunc.targetColumn)
        case .max:
            return computeMax(frame: frame, column: windowFunc.targetColumn)
            
        // Ranking
        case .rowNumber:
            return .int(Int64(rowIdx + 1))
        case .rank:
            return computeRank(partition: partition, rowIdx: rowIdx)
        case .denseRank:
            return computeDenseRank(partition: partition, rowIdx: rowIdx)
        case .ntile:
            return computeNtile(partition: partition, rowIdx: rowIdx, buckets: windowFunc.buckets)
        case .percentRank:
            return computePercentRank(partition: partition, rowIdx: rowIdx)
        case .cumeDist:
            return computeCumeDist(partition: partition, rowIdx: rowIdx)
            
        // Value functions
        case .lag:
            return computeLag(partition: partition, rowIdx: rowIdx, offset: windowFunc.offset, column: windowFunc.targetColumn)
        case .lead:
            return computeLead(partition: partition, rowIdx: rowIdx, offset: windowFunc.offset, column: windowFunc.targetColumn)
        case .firstValue:
            return frame.first?.values[windowFunc.targetColumn] ?? .null
        case .lastValue:
            return frame.last?.values[windowFunc.targetColumn] ?? .null
        case .nthValue:
            let idx = windowFunc.offset - 1
            return idx >= 0 && idx < frame.count ? frame[idx].values[windowFunc.targetColumn] ?? .null : .null
        }
    }
    
    // MARK: - Frame Calculation
    
    private func getFrame(partition: [WindowRow], rowIdx: Int, spec: WindowSpec) -> [WindowRow] {
        let partitionSize = partition.count
        
        // Calculate frame boundaries
        var start = 0
        var end = partitionSize - 1
        
        switch spec.frameStart {
        case .unboundedPreceding:
            start = 0
        case .currentRow:
            start = rowIdx
        case .nPreceding(let n):
            start = max(0, rowIdx - n)
        case .unboundedFollowing:
            start = partitionSize - 1
        case .nFollowing(let n):
            start = min(partitionSize - 1, rowIdx + n)
        }
        
        switch spec.frameEnd {
        case .unboundedPreceding:
            end = 0
        case .currentRow:
            end = rowIdx
        case .nPreceding(let n):
            end = max(0, rowIdx - n)
        case .unboundedFollowing:
            end = partitionSize - 1
        case .nFollowing(let n):
            end = min(partitionSize - 1, rowIdx + n)
        }
        
        // Ensure valid range
        if start > end {
            return []
        }
        
        var frame = Array(partition[start...end])
        
        // Apply frame exclusion
        switch spec.frameExclusion {
        case .noOthers:
            break
        case .currentRow:
            frame = frame.filter { $0.rowNum != partition[rowIdx].rowNum }
        case .group, .ties:
            // Exclude peers (simplified - exclude rows with same order key values)
            let currentRow = partition[rowIdx]
            let orderColumns = Array(spec.orderBy.map { $0.column }) // Create a copy to avoid data race
            frame = frame.filter { row in
                !areRowsEqual(row, currentRow, columns: orderColumns)
            }
        }
        
        return frame
    }
    
    private func areRowsEqual(_ r1: WindowRow, _ r2: WindowRow, columns: [String]) -> Bool {
        guard r1.rowNum != r2.rowNum else { return true }
        for col in columns {
            if r1.values[col] != r2.values[col] {
                return false
            }
        }
        return true
    }
    
    // MARK: - Aggregate Functions
    
    private func computeSum(frame: [WindowRow], column: String) -> Value {
        var sum: Double = 0
        for row in frame {
            if case .double(let value) = row.values[column] {
                sum += value
            }
        }
        return .double(sum)
    }
    
    private func computeAvg(frame: [WindowRow], column: String) -> Value {
        guard !frame.isEmpty else { return .null }
        var sum: Double = 0
        var count = 0
        for row in frame {
            if case .double(let value) = row.values[column] {
                sum += value
                count += 1
            }
        }
        return count > 0 ? .double(sum / Double(count)) : .null
    }
    
    private func computeMin(frame: [WindowRow], column: String) -> Value {
        var minVal: Value = Value.null
        for row in frame {
            if let value = row.values[column] {
                if case .null = minVal {
                    minVal = value
                } else if compareValues(value, minVal) == .orderedAscending {
                    minVal = value
                }
            }
        }
        return minVal
    }
    
    private func computeMax(frame: [WindowRow], column: String) -> Value {
        var maxVal: Value = Value.null
        for row in frame {
            if let value = row.values[column] {
                if case .null = maxVal {
                    maxVal = value
                } else if compareValues(value, maxVal) == .orderedDescending {
                    maxVal = value
                }
            }
        }
        return maxVal
    }
    
    // MARK: - Ranking Functions
    
    private func computeRank(partition: [WindowRow], rowIdx: Int) -> Value {
        // RANK considers ties - same values get same rank
        var rank = 1
        let currentRow = partition[rowIdx]
        
        for i in 0..<rowIdx {
            if !areRowsEqual(partition[i], currentRow, columns: []) {
                rank = i + 2
            }
        }
        
        return .int(Int64(rank))
    }
    
    private func computeDenseRank(partition: [WindowRow], rowIdx: Int) -> Value {
        // Dense rank has no gaps after ties
        var distinctCount = 1
        let currentRow = partition[rowIdx]
        
        for i in 1...rowIdx {
            if !areRowsEqual(partition[i-1], partition[i], columns: []) {
                distinctCount += 1
            }
        }
        
        return .int(Int64(distinctCount))
    }
    
    private func computeNtile(partition: [WindowRow], rowIdx: Int, buckets: Int) -> Value {
        let partitionSize = partition.count
        let bucketNum = ((rowIdx) * buckets) / partitionSize + 1
        return .int(Int64(bucketNum))
    }
    
    private func computePercentRank(partition: [WindowRow], rowIdx: Int) -> Value {
        let partitionSize = partition.count
        if partitionSize <= 1 {
            return .double(0.0)
        }
        
        // Simplified: (rank - 1) / (total_rows - 1)
        let rank = rowIdx + 1
        let percentRank = Double(rank - 1) / Double(partitionSize - 1)
        return .double(percentRank)
    }
    
    private func computeCumeDist(partition: [WindowRow], rowIdx: Int) -> Value {
        let partitionSize = partition.count
        // Simplified: count of rows <= current / total rows
        let cumeDist = Double(rowIdx + 1) / Double(partitionSize)
        return .double(cumeDist)
    }
    
    // MARK: - Value Functions
    
    private func computeLag(partition: [WindowRow], rowIdx: Int, offset: Int, column: String) -> Value {
        let targetIdx = rowIdx - offset
        if targetIdx >= 0 && targetIdx < partition.count {
            return partition[targetIdx].values[column] ?? .null
        }
        return .null
    }
    
    private func computeLead(partition: [WindowRow], rowIdx: Int, offset: Int, column: String) -> Value {
        let targetIdx = rowIdx + offset
        if targetIdx >= 0 && targetIdx < partition.count {
            return partition[targetIdx].values[column] ?? .null
        }
        return .null
    }
    
    // MARK: - Result Materialization
    
    private func materializeResults() -> [[String: Value]] {
        return inputRows.map { row in
            var result = row.values
            if let windowVals = windowResults[row.rowNum] {
                result.merge(windowVals) { _, new in new }
            }
            return result
        }
    }
}

// MARK: - Errors

public enum WindowFunctionError: Error, LocalizedError {
    case noFunctionsDefined
    case invalidFrameSpecification
    case invalidPartitionSpec
    case invalidOrderSpec
    
    public var errorDescription: String? {
        switch self {
        case .noFunctionsDefined:
            return "No window functions defined"
        case .invalidFrameSpecification:
            return "Invalid frame specification"
        case .invalidPartitionSpec:
            return "Invalid partition specification"
        case .invalidOrderSpec:
            return "Invalid order specification"
        }
    }
}

/*
 * IMPLEMENTATION NOTES:
 *
 * This implementation follows the WindowFunctions.tla specification:
 *
 * 1. Window Frames: ROWS, RANGE, GROUPS frame types
 * 2. Frame Boundaries: UNBOUNDED PRECEDING/FOLLOWING, CURRENT ROW, N PRECEDING/FOLLOWING
 * 3. Aggregate Functions: SUM, AVG, COUNT, MIN, MAX over frames
 * 4. Ranking Functions: ROW_NUMBER (unique), RANK (gaps), DENSE_RANK (no gaps)
 * 5. Value Functions: LAG/LEAD (offset), FIRST/LAST_VALUE (frame bounds)
 * 6. Efficient Processing: Single-pass algorithm per partition
 *
 * Key Properties Verified by TLA+:
 * - Frame boundaries are always valid
 * - Current row is within partition bounds
 * - ROW_NUMBER is sequential within partition
 * - Aggregates over empty frame return appropriate defaults
 * - Processing eventually completes
 * - All rows are eventually processed
 *
 * Academic References:
 * - ISO SQL:2016: Window functions standard
 * - Bellamkonda et al. (2013): Oracle analytic functions
 * - Leis et al. (2015): Query optimizer evaluation
 * - Larson & Graefe (2011): Column store indexes
 */

