import Foundation

// MARK: - Plan Predicate

/// Represents a predicate for filtering rows
public struct PlanPredicate {
    public let columns: Set<String>
    public let selectivityHint: Double?
    public let evaluator: (PlanRow) -> Bool
    
    public init(columns: Set<String>, selectivityHint: Double? = nil, evaluator: @escaping (PlanRow) -> Bool) {
        self.columns = columns
        self.selectivityHint = selectivityHint
        self.evaluator = evaluator
    }
}

// MARK: - Table Scan Operator

/// Scans a table sequentially
public final class TableScanOperator: PlanOperator {
    public let table: String
    public let alias: String?
    public let schema: PlanSchema
    
    private var context: ExecutionContext?
    private var currentRows: [PlanRow] = []
    private var currentIndex: Int = 0
    
    public init(table: String, alias: String? = nil) {
        self.table = table
        self.alias = alias
        // For now, create a basic schema - this would be populated from table metadata
        self.schema = PlanSchema(columns: [])
    }
    
    public func open(context: ExecutionContext) throws {
        self.context = context
        
        // Actually scan the table using the database
        let rawRows = try context.database.scan(table, tid: context.transactionId)
        
        // Convert to PlanRow format with proper column qualification
        self.currentRows = rawRows.map { (rid, row) in
            var qualifiedRow: [String: Value] = [:]
            let prefix = alias ?? table
            
            for (key, value) in row {
                qualifiedRow["\(prefix).\(key)"] = value
            }
            return PlanRow(values: qualifiedRow)
        }
        
        self.currentIndex = 0
    }
    
    public func next() throws -> PlanRow? {
        guard currentIndex < currentRows.count else { return nil }
        let row = currentRows[currentIndex]
        currentIndex += 1
        return row
    }
    
    public func close() throws {
        self.context = nil
        self.currentRows = []
        self.currentIndex = 0
    }
}

// MARK: - Index Scan Operator

/// Scans using an index
public final class IndexScanOperator: PlanOperator {
    public let table: String
    public let index: String
    public let indexColumns: [String]
    public let bounds: IndexBounds
    public let alias: String?
    public let schema: PlanSchema
    
    private var context: ExecutionContext?
    private var currentRows: [PlanRow] = []
    private var currentIndex: Int = 0
    
    public init(table: String, index: String, indexColumns: [String], bounds: IndexBounds, alias: String? = nil) {
        self.table = table
        self.index = index
        self.indexColumns = indexColumns
        self.bounds = bounds
        self.alias = alias
        self.schema = PlanSchema(columns: [])
    }
    
    public func open(context: ExecutionContext) throws {
        self.context = context
        self.currentRows = []
        self.currentIndex = 0
    }
    
    public func next() throws -> PlanRow? {
        guard currentIndex < currentRows.count else { return nil }
        let row = currentRows[currentIndex]
        currentIndex += 1
        return row
    }
    
    public func close() throws {
        self.context = nil
        self.currentRows = []
        self.currentIndex = 0
    }
}

// MARK: - Index Bounds

/// Represents bounds for index scanning
public struct IndexBounds {
    public let lower: [Value?]
    public let upper: [Value?]
    public let inclusive: Bool
    
    public init(lower: [Value?], upper: [Value?], inclusive: Bool = true) {
        self.lower = lower
        self.upper = upper
        self.inclusive = inclusive
    }
}

// MARK: - Filter Operator

/// Filters rows based on a predicate
public final class FilterOperator: PlanOperator {
    public let child: PlanOperator
    public let predicate: PlanPredicate
    public let schema: PlanSchema
    
    private var context: ExecutionContext?
    private var childOpen: Bool = false
    
    public init(child: PlanOperator, predicate: PlanPredicate) {
        self.child = child
        self.predicate = predicate
        self.schema = child.schema
    }
    
    public func open(context: ExecutionContext) throws {
        self.context = context
        try child.open(context: context)
        self.childOpen = true
    }
    
    public func next() throws -> PlanRow? {
        guard childOpen else { return nil }
        
        while let row = try child.next() {
            if predicate.evaluator(row) {
                return row
            }
        }
        return nil
    }
    
    public func close() throws {
        if childOpen {
            try child.close()
            childOpen = false
        }
        self.context = nil
    }
}

// MARK: - Vectorized Filter Operator (SIMD-friendly)

/// Processes rows in batches to leverage CPU caches and enable SIMD-friendly evaluation.
public final class VectorizedFilterOperator: PlanOperator {
    public let child: PlanOperator
    public let schema: PlanSchema
    public let batchSize: Int
    private let predicate: (PlanRow) -> Bool
    private var context: ExecutionContext?
    private var buffer: [PlanRow] = []
    private var index: Int = 0

    public init(child: PlanOperator, batchSize: Int = 1024, predicate: @escaping (PlanRow) -> Bool) {
        self.child = child
        self.schema = child.schema
        self.batchSize = max(1, batchSize)
        self.predicate = predicate
    }

    public func open(context: ExecutionContext) throws {
        self.context = context
        buffer.removeAll(keepingCapacity: true)
        index = 0
        try child.open(context: context)
    }

    public func next() throws -> PlanRow? {
        while true {
            if index < buffer.count {
                let row = buffer[index]
                index += 1
                return row
            }
            buffer.removeAll(keepingCapacity: true)
            index = 0
            var fetched = 0
            while fetched < batchSize, let row = try child.next() {
                if predicate(row) { buffer.append(row) }
                fetched += 1
            }
            if buffer.isEmpty {
                if fetched == 0 { return nil }
                continue
            }
        }
    }

    public func close() throws {
        try child.close()
        buffer.removeAll(keepingCapacity: true)
        index = 0
        context = nil
    }
}

// MARK: - Vectorized Project Operator

public final class VectorizedProjectOperator: PlanOperator {
    public let child: PlanOperator
    public let schema: PlanSchema
    private let projection: [String]
    private let batchSize: Int
    private var context: ExecutionContext?
    private var buffer: [PlanRow] = []
    private var index: Int = 0

    public init(child: PlanOperator, projection: [String], batchSize: Int = 1024) {
        self.child = child
        self.schema = PlanSchema(columns: projection)
        self.projection = projection
        self.batchSize = max(1, batchSize)
    }

    public func open(context: ExecutionContext) throws {
        self.context = context
        buffer.removeAll(keepingCapacity: true)
        index = 0
        try child.open(context: context)
    }

    public func next() throws -> PlanRow? {
        while true {
            if index < buffer.count {
                let row = buffer[index]
                index += 1
                return row
            }
            buffer.removeAll(keepingCapacity: true)
            index = 0
            var fetched = 0
            while fetched < batchSize, let row = try child.next() {
                var out: [String: Value] = [:]
                out.reserveCapacity(projection.count)
                for col in projection { if let v = row.values[col] { out[col] = v } }
                buffer.append(PlanRow(values: out))
                fetched += 1
            }
            if buffer.isEmpty {
                if fetched == 0 { return nil }
                continue
            }
        }
    }

    public func close() throws {
        try child.close()
        buffer.removeAll(keepingCapacity: true)
        index = 0
        context = nil
    }
}

// MARK: - Project Operator

/// Projects specific columns from child rows
public final class ProjectOperator: PlanOperator {
    public let child: PlanOperator
    public let projection: [String]
    public let schema: PlanSchema
    
    private var context: ExecutionContext?
    private var childOpen: Bool = false
    
    public init(child: PlanOperator, projection: [String]) {
        self.child = child
        self.projection = projection
        self.schema = PlanSchema(columns: projection)
    }
    
    public func open(context: ExecutionContext) throws {
        self.context = context
        try child.open(context: context)
        self.childOpen = true
    }
    
    public func next() throws -> PlanRow? {
        guard childOpen else { return nil }
        
        guard let childRow = try child.next() else { return nil }
        
        var projectedValues: [String: Value] = [:]
        for column in projection {
            if let value = childRow[column] {
                projectedValues[column] = value
            }
        }
        return PlanRow(values: projectedValues)
    }
    
    public func close() throws {
        if childOpen {
            try child.close()
            childOpen = false
        }
        self.context = nil
    }
}

// MARK: - Sort Operator

/// Sorts rows based on sort keys
public final class SortOperator: PlanOperator {
    public let child: PlanOperator
    public let keys: [SortKey]
    public let schema: PlanSchema
    
    private var context: ExecutionContext?
    private var sortedRows: [PlanRow] = []
    private var currentIndex: Int = 0
    
    public init(child: PlanOperator, keys: [SortKey]) {
        self.child = child
        self.keys = keys
        self.schema = child.schema
    }
    
    public func open(context: ExecutionContext) throws {
        self.context = context
        try child.open(context: context)
        
        // Materialize all rows and sort them
        var allRows: [PlanRow] = []
        while let row = try child.next() {
            allRows.append(row)
        }
        try child.close()
        
        self.sortedRows = allRows.sorted { row1, row2 in
            for key in keys {
                let value1 = row1[key.column]
                let value2 = row2[key.column]
                
                let comparison = compareValues(value1, value2)
                if comparison != 0 {
                    return key.ascending ? comparison < 0 : comparison > 0
                }
            }
            return false
        }
        self.currentIndex = 0
    }
    
    public func next() throws -> PlanRow? {
        guard currentIndex < sortedRows.count else { return nil }
        let row = sortedRows[currentIndex]
        currentIndex += 1
        return row
    }
    
    public func close() throws {
        self.context = nil
        self.sortedRows = []
        self.currentIndex = 0
    }
    
    private func compareValues(_ v1: Value?, _ v2: Value?) -> Int {
        guard let val1 = v1, let val2 = v2 else {
            if v1 == nil && v2 == nil { return 0 }
            return v1 == nil ? -1 : 1
        }
        
        switch (val1, val2) {
        case (.int(let i1), .int(let i2)):
            return i1 == i2 ? 0 : (i1 < i2 ? -1 : 1)
        case (.double(let d1), .double(let d2)):
            return d1 == d2 ? 0 : (d1 < d2 ? -1 : 1)
        case (.string(let t1), .string(let t2)):
            return t1.compare(t2).rawValue
        case (.bool(let b1), .bool(let b2)):
            return b1 == b2 ? 0 : (b1 ? 1 : -1)
        default:
            return 0
        }
    }
}

// MARK: - Sort Key

/// Represents a sort key with column name and direction
public struct SortKey {
    public let column: String
    public let ascending: Bool
    
    public init(column: String, ascending: Bool = true) {
        self.column = column
        self.ascending = ascending
    }
}

// MARK: - Hash Join Operator

/// Performs hash-based join
public final class HashJoinOperator: PlanOperator {
    public let joinType: JoinType
    public let left: PlanOperator
    public let right: PlanOperator
    public let leftKeys: [String]
    public let rightKeys: [String]
    public let schema: PlanSchema
    
    private var context: ExecutionContext?
    private var hashTable: [String: [PlanRow]] = [:]
    private var currentLeftRow: PlanRow?
    private var currentRightRows: [PlanRow] = []
    private var currentRightIndex: Int = 0
    
    public init(joinType: JoinType, left: PlanOperator, right: PlanOperator, leftKeys: [String], rightKeys: [String]) {
        self.joinType = joinType
        self.left = left
        self.right = right
        self.leftKeys = leftKeys
        self.rightKeys = rightKeys
        // Schema would be combination of left and right schemas
        self.schema = left.schema
    }
    
    public func open(context: ExecutionContext) throws {
        self.context = context
        try right.open(context: context)
        
        // Build hash table from right side
        while let rightRow = try right.next() {
            let key = buildJoinKey(row: rightRow, keys: rightKeys)
            hashTable[key, default: []].append(rightRow)
        }
        try right.close()
        
        try left.open(context: context)
        self.currentLeftRow = nil
        self.currentRightRows = []
        self.currentRightIndex = 0
    }
    
    public func next() throws -> PlanRow? {
        // If we have remaining right rows for current left row, process them
        if currentRightIndex < currentRightRows.count {
            let rightRow = currentRightRows[currentRightIndex]
            currentRightIndex += 1
            
            // Combine left and right rows
            guard let leftRow = currentLeftRow else { return nil }
            var combinedValues = leftRow.values
            for (key, value) in rightRow.values {
                combinedValues[key] = value
            }
            
            return PlanRow(values: combinedValues)
        }
        
        // Get next left row
        guard let leftRow = try left.next() else {
            return nil
        }
        
        currentLeftRow = leftRow
        
        // Get matching right rows for current left row
        let leftKey = buildJoinKey(row: leftRow, keys: leftKeys)
        currentRightRows = hashTable[leftKey] ?? []
        currentRightIndex = 0
        
        // If no matching right rows, get next left row
        if currentRightRows.isEmpty {
            return try next()
        }
        
        // Process first matching right row
        guard currentRightIndex < currentRightRows.count else {
            return try next()
        }
        let rightRow = currentRightRows[currentRightIndex]
        currentRightIndex += 1
        
        // Combine left and right rows
        var combinedValues = leftRow.values
        for (key, value) in rightRow.values {
            combinedValues[key] = value
        }
        
        return PlanRow(values: combinedValues)
    }
    
    public func close() throws {
        self.context = nil
        self.hashTable = [:]
        self.currentLeftRow = nil
        self.currentRightRows = []
        self.currentRightIndex = 0
    }
    
    private func buildJoinKey(row: PlanRow, keys: [String]) -> String {
        func encode(_ v: Value) -> String {
            switch v {
            case .int(let i): return "i:\(i)"
            case .double(let d): return "d:\(d)"
            case .bool(let b): return b ? "b:1" : "b:0"
            case .string(let s): return "s:\(s)"
            case .null: return "n:"
            case .decimal(let d): return "dec:\(d)"
            case .date(let d): return "date:\(d.timeIntervalSince1970)"
            }
        }
        var parts: [String] = []
        parts.reserveCapacity(keys.count)
        for key in keys {
            if let value = row[key] { parts.append(encode(value)) }
            else { parts.append("n:") }
        }
        return parts.joined(separator: "|")
    }
}

// MARK: - Merge Join Operator

/// Performs merge-based join (requires sorted inputs)
public final class MergeJoinOperator: PlanOperator {
    public let joinType: JoinType
    public let left: PlanOperator
    public let right: PlanOperator
    public let leftKeys: [String]
    public let rightKeys: [String]
    public let schema: PlanSchema
    
    private var context: ExecutionContext?
    
    public init(joinType: JoinType, left: PlanOperator, right: PlanOperator, leftKeys: [String], rightKeys: [String]) {
        self.joinType = joinType
        self.left = left
        self.right = right
        self.leftKeys = leftKeys
        self.rightKeys = rightKeys
        self.schema = left.schema
    }
    
    public func open(context: ExecutionContext) throws {
        self.context = context
        try left.open(context: context)
        try right.open(context: context)
    }
    
    public func next() throws -> PlanRow? {
        // Implementation would handle merge join logic
        // For now, return nil as placeholder
        return nil
    }
    
    public func close() throws {
        try left.close()
        try right.close()
        self.context = nil
    }
}

// MARK: - Join Type

/// Types of joins supported
public enum JoinType {
    case inner
    case leftOuter
    case rightOuter
    case fullOuter
}

// MARK: - Limit Operator

/// Limits the number of rows returned
public final class LimitOperator: PlanOperator {
    public let child: PlanOperator
    public let limit: Int
    public let schema: PlanSchema
    
    private var context: ExecutionContext?
    private var childOpen: Bool = false
    private var rowsReturned: Int = 0
    
    public init(child: PlanOperator, limit: Int) {
        self.child = child
        self.limit = limit
        self.schema = child.schema
    }
    
    public func open(context: ExecutionContext) throws {
        self.context = context
        try child.open(context: context)
        self.childOpen = true
        self.rowsReturned = 0
    }
    
    public func next() throws -> PlanRow? {
        guard childOpen && rowsReturned < limit else { return nil }
        
        if let row = try child.next() {
            rowsReturned += 1
            return row
        }
        return nil
    }
    
    public func close() throws {
        if childOpen {
            try child.close()
            childOpen = false
        }
        self.context = nil
        self.rowsReturned = 0
    }
}

// MARK: - Parallel Map Operator

/// Applies a transformation function in parallel
public final class ParallelMapOperator: PlanOperator {
    public let child: PlanOperator
    public let concurrency: Int
    public let transform: (PlanRow) -> PlanRow
    public let schema: PlanSchema
    
    private var context: ExecutionContext?
    private var childOpen: Bool = false
    
    public init(child: PlanOperator, concurrency: Int, transform: @escaping (PlanRow) -> PlanRow) {
        self.child = child
        self.concurrency = concurrency
        self.transform = transform
        self.schema = child.schema
    }
    
    public func open(context: ExecutionContext) throws {
        self.context = context
        try child.open(context: context)
        self.childOpen = true
    }
    
    public func next() throws -> PlanRow? {
        guard childOpen else { return nil }
        
        guard let childRow = try child.next() else { return nil }
        return transform(childRow)
    }
    
    public func close() throws {
        if childOpen {
            try child.close()
            childOpen = false
        }
        self.context = nil
    }
}