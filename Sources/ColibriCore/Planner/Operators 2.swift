//
//  Operators.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// Theme: Operator suite powering Volcano pipelines with scans, filters, joins, and sorts.

import Foundation

// MARK: - Utility predicates

/// Boolean predicate used by filter and join operators.
public struct PlanPredicate {
    public typealias Evaluator = (PlanRow) -> Bool
    public let referencedColumns: Set<String>
    public let selectivityHint: Double?
    private let evaluator: Evaluator

    public init(columns: Set<String>, selectivityHint: Double? = nil, evaluator: @escaping Evaluator) {
        self.referencedColumns = columns
        self.selectivityHint = selectivityHint
        self.evaluator = evaluator
    }

    public func evaluate(_ row: PlanRow) -> Bool { evaluator(row) }
}

// MARK: - Table Scan

public final class TableScanOperator: PlanOperator {
    public let table: String
    public let alias: String
    public let projectedColumns: [String]?
    public private(set) var schema: PlanSchema

    private var iterator: IndexingIterator<[PlanRow]>?
    private var materialized: [PlanRow] = []

    public init(table: String, alias: String? = nil, projectedColumns: [String]? = nil) {
        self.table = table
        let resolvedAlias = alias ?? table
        self.alias = resolvedAlias
        self.projectedColumns = projectedColumns
        if let projectedColumns {
            let cols = projectedColumns.map { "\(resolvedAlias).\($0)" }
            schema = PlanSchema(columns: cols)
        } else {
            schema = PlanSchema(columns: [])
        }
    }

    public func open(context: ExecutionContext) throws {
        let pairs = try context.database.scan(table, tid: context.transactionId)
        materialized.removeAll(keepingCapacity: true)
        materialized.reserveCapacity(pairs.count)
        for (_, row) in pairs {
            var qualified: [String: Value] = [:]
            for (col, val) in row {
                let qualifiedName = "\(alias).\(col)"
                qualified[qualifiedName] = val
            }
            if let projectedColumns {
                var subset: [String: Value] = [:]
                for col in projectedColumns {
                    let key = "\(alias).\(col)"
                    if let val = qualified[key] {
                        subset[key] = val
                    }
                }
                materialized.append(PlanRow(values: subset))
            } else {
                materialized.append(PlanRow(values: qualified))
            }
        }
        if schema.columns.isEmpty, let first = materialized.first {
            schema = PlanSchema(columns: Array(first.values.keys).sorted())
        }
        iterator = materialized.makeIterator()
    }

    public func next() throws -> PlanRow? {
        iterator?.next()
    }

    public func close() throws {
        iterator = nil
        materialized.removeAll(keepingCapacity: false)
    }
}

// MARK: - Index Scan (accelerated ORDER BY/predicate pushdown)

public final class IndexScanOperator: PlanOperator {
    public let table: String
    public let index: String
    public let indexColumns: [String]
    public let alias: String
    public let equality: [String: Value]
    public let lowerBound: [Value]?
    public let upperBound: [Value]?
    public let projectedColumns: [String]?

    public private(set) var schema: PlanSchema

    private var iterator: IndexingIterator<[PlanRow]>?
    private var buffer: [PlanRow] = []
    private var tableLock: LockHandle?
    private weak var databaseRef: Database?

    public init(table: String,
                index: String,
                indexColumns: [String],
                alias: String? = nil,
                equality: [String: Value] = [:],
                lowerBound: [Value]? = nil,
                upperBound: [Value]? = nil,
                projectedColumns: [String]? = nil) {
        self.table = table
        self.index = index
        self.indexColumns = indexColumns
        let resolvedAlias = alias ?? table
        self.alias = resolvedAlias
        self.equality = equality
        self.lowerBound = lowerBound
        self.upperBound = upperBound
        self.projectedColumns = projectedColumns
        if let projectedColumns {
            schema = PlanSchema(columns: projectedColumns.map { "\(resolvedAlias).\($0)" })
        } else {
            schema = PlanSchema(columns: [])
        }
    }

    public func open(context: ExecutionContext) throws {
        databaseRef = context.database
        let tid = context.transactionId ?? 0
        tableLock = try context.database.lockManager.lock(.table(table), mode: .shared, tid: tid, timeout: context.database.config.lockTimeoutSeconds)

        do {
            let ridList = try fetchRIDs(database: context.database)
            let snapshotCutoff = context.transactionId.flatMap { context.database.txContexts[$0]?.snapshotCutoff }
            let snapshot = context.database.mvcc.snapshot(for: context.transactionId, isolationCutoff: snapshotCutoff)
            var visible = context.database.mvcc.visibleRows(table: table, snapshot: snapshot, readerTID: context.transactionId)
            let knownVersions = context.database.mvcc.allVersions(for: table)

            buffer.removeAll(keepingCapacity: true)
            buffer.reserveCapacity(ridList.count)
            let projected = projectedColumns?.map { "\(alias).\($0)" }

            for rid in ridList {
                var row: Row
                if let tracked = visible[rid] {
                    row = tracked
                } else {
                    row = try context.database.readRow(table: table, rid: rid)
                    if knownVersions[rid] == nil {
                        context.database.mvcc.registerInsert(table: table, rid: rid, row: row, tid: nil)
                        visible[rid] = row
                    }
                }
                var qualified: [String: Value] = [:]
                for (col, val) in row {
                    let key = "\(alias).\(col)"
                    qualified[key] = val
                }
                if let projected {
                    var subset: [String: Value] = [:]
                    for col in projected {
                        if let v = qualified[col] { subset[col] = v }
                    }
                    buffer.append(PlanRow(values: subset))
                } else {
                    buffer.append(PlanRow(values: qualified))
                }
            }

            if schema.columns.isEmpty, let first = buffer.first {
                schema = PlanSchema(columns: Array(first.values.keys).sorted())
            }
            iterator = buffer.makeIterator()
        } catch {
            if let handle = tableLock, let db = databaseRef {
                db.lockManager.unlock(handle)
            }
            tableLock = nil
            databaseRef = nil
            throw error
        }
    }

    private func fetchRIDs(database: Database) throws -> [RID] {
        let leadingColumns = indexColumns
        let orderedEquality = leadingColumns.compactMap { equality[$0] }
        if !orderedEquality.isEmpty && orderedEquality.count == leadingColumns.count {
            if orderedEquality.count == 1 {
                return try database.indexSearchEqualsTyped(table: table, index: index, value: orderedEquality[0])
            }
            return try database.indexSearchEqualsValues(table: table, index: index, values: orderedEquality)
        }
        if let lowerBound {
            if indexColumns.count == 1 {
                let lo = lowerBound.first
                let hi = upperBound?.first
                return try database.indexRangeTyped(table: table, index: index, lo: lo, hi: hi)
            }
            return try database.indexRangeValues(table: table, index: index, lo: lowerBound, hi: upperBound)
        }
        return try database.indexRangeTyped(table: table, index: index, lo: nil, hi: nil)
    }

    public func next() throws -> PlanRow? { iterator?.next() }

    public func close() throws {
        iterator = nil
        buffer.removeAll(keepingCapacity: false)
        if let handle = tableLock, let db = databaseRef {
            db.lockManager.unlock(handle)
        }
        tableLock = nil
        databaseRef = nil
    }
}

// MARK: - Filter

public final class FilterOperator: PlanOperator {
    public let child: PlanOperator
    public let predicate: PlanPredicate
    public var schema: PlanSchema { child.schema }

    public init(child: PlanOperator, predicate: PlanPredicate) {
        self.child = child
        self.predicate = predicate
    }

    public func open(context: ExecutionContext) throws {
        try child.open(context: context)
    }

    public func next() throws -> PlanRow? {
        while let row = try child.next() {
            if predicate.evaluate(row) { return row }
        }
        return nil
    }

    public func close() throws { try child.close() }
}

// MARK: - Projection

public final class ProjectOperator: PlanOperator {
    public let child: PlanOperator
    public let projection: [String]
    public var schema: PlanSchema

    public init(child: PlanOperator, projection: [String]) {
        self.child = child
        self.projection = projection
        self.schema = PlanSchema(columns: projection)
    }

    public func open(context: ExecutionContext) throws {
        try child.open(context: context)
    }

    public func next() throws -> PlanRow? {
        guard let row = try child.next() else { return nil }
        var projected: [String: Value] = [:]
        for col in projection {
            if let val = row.values[col] {
                projected[col] = val
            }
        }
        return PlanRow(values: projected)
    }

    public func close() throws { try child.close() }
}

// MARK: - Sort (ORDER BY)

public final class SortOperator: PlanOperator {
    public struct SortKey {
        public let column: String
        public let ascending: Bool
        public init(column: String, ascending: Bool = true) {
            self.column = column
            self.ascending = ascending
        }
    }

    public let child: PlanOperator
    public let keys: [SortKey]
    public private(set) var schema: PlanSchema

    private var iterator: IndexingIterator<[PlanRow]>?
    private var buffer: [PlanRow] = []

    public init(child: PlanOperator, keys: [SortKey]) {
        self.child = child
        self.keys = keys
        self.schema = child.schema
    }

    public func open(context: ExecutionContext) throws {
        try child.open(context: context)
        buffer.removeAll(keepingCapacity: true)
        while let row = try child.next() {
            buffer.append(row)
        }
        buffer.sort(by: comparator)
        iterator = buffer.makeIterator()
    }

    private func comparator(_ lhs: PlanRow, _ rhs: PlanRow) -> Bool {
        for key in keys {
            guard let lv = lhs.values[key.column], let rv = rhs.values[key.column] else { continue }
            if lv == rv { continue }
            let result = compare(lv, rv)
            if result == .orderedSame { continue }
            return key.ascending ? (result == .orderedAscending) : (result == .orderedDescending)
        }
        return false
    }

    private func compare(_ lhs: Value, _ rhs: Value) -> ComparisonResult {
        switch (lhs, rhs) {
        case (.int(let l), .int(let r)): return l == r ? .orderedSame : (l < r ? .orderedAscending : .orderedDescending)
        case (.double(let l), .double(let r)): return l == r ? .orderedSame : (l < r ? .orderedAscending : .orderedDescending)
        case (.bool(let l), .bool(let r)): return l == r ? .orderedSame : ((l == false && r == true) ? .orderedAscending : .orderedDescending)
        case (.string(let l), .string(let r)): return l == r ? .orderedSame : (l < r ? .orderedAscending : .orderedDescending)
        case (.null, .null): return .orderedSame
        case (.null, _): return .orderedAscending
        case (_, .null): return .orderedDescending
        default:
            // Fallback to string comparison for heterogeneous types
            return lhs.description.compare(rhs.description)
        }
    }

    public func next() throws -> PlanRow? { iterator?.next() }

    public func close() throws {
        iterator = nil
        buffer.removeAll(keepingCapacity: false)
        try child.close()
    }
}

// MARK: - Hash Join

public final class HashJoinOperator: PlanOperator {
    public enum JoinType { case inner }

    public let joinType: JoinType
    public let left: PlanOperator
    public let right: PlanOperator
    public let leftKeys: [String]
    public let rightKeys: [String]
    public private(set) var schema: PlanSchema

    private var hashTable: [JoinKey: [PlanRow]] = [:]
    private var leftRow: PlanRow?
    private var matches: [PlanRow] = []
    private var matchIndex = 0

    public init(joinType: JoinType = .inner,
                left: PlanOperator,
                right: PlanOperator,
                leftKeys: [String],
                rightKeys: [String]) {
        precondition(leftKeys.count == rightKeys.count, "join key count mismatch")
        self.joinType = joinType
        self.left = left
        self.right = right
        self.leftKeys = leftKeys
        self.rightKeys = rightKeys
        self.schema = PlanSchema(columns: [])
    }

    public func open(context: ExecutionContext) throws {
        try left.open(context: context)
        try right.open(context: context)
        let mergedCols = Array(Set(left.schema.columns + right.schema.columns))
        if !mergedCols.isEmpty { schema = PlanSchema(columns: mergedCols) }
        try buildHashTable()
        leftRow = nil
        matches = []
        matchIndex = 0
    }

    private func buildHashTable() throws {
        hashTable.removeAll(keepingCapacity: true)
        while let row = try right.next() {
            guard let key = joinKey(for: row, keys: rightKeys) else { continue }
            hashTable[key, default: []].append(row)
        }
        try right.close()
    }

    public func next() throws -> PlanRow? {
        while true {
            if matchIndex < matches.count {
                let matched = matches[matchIndex]
                matchIndex += 1
                return merge(leftRow!, matched)
            }
            guard let row = try left.next() else { return nil }
            leftRow = row
            guard let key = joinKey(for: row, keys: leftKeys) else { continue }
            if let bucket = hashTable[key] {
                matches = bucket
                matchIndex = 0
                continue
            }
        }
    }

    private func joinKey(for row: PlanRow, keys: [String]) -> JoinKey? {
        var values: [Value] = []
        values.reserveCapacity(keys.count)
        for key in keys {
            guard let value = row.values[key] else { return nil }
            values.append(value)
        }
        return JoinKey(values: values)
    }

    private func merge(_ lhs: PlanRow, _ rhs: PlanRow) -> PlanRow {
        var merged = lhs.values
        for (k, v) in rhs.values {
            merged[k] = v
        }
        return PlanRow(values: merged)
    }

    public func close() throws {
        hashTable.removeAll(keepingCapacity: false)
        matches.removeAll(keepingCapacity: false)
        matchIndex = 0
        try left.close()
        try right.close()
    }

    private struct JoinKey: Hashable {
        let values: [Value]
    }
}

// MARK: - Merge Join (requires sorted inputs)

public final class MergeJoinOperator: PlanOperator {
    public let left: PlanOperator
    public let right: PlanOperator
    public let leftKeys: [String]
    public let rightKeys: [String]
    public private(set) var schema: PlanSchema

    private var leftBuffer: [PlanRow] = []
    private var rightBuffer: [PlanRow] = []
    private var leftRow: PlanRow?
    private var rightRow: PlanRow?

    public init(left: PlanOperator, right: PlanOperator, leftKeys: [String], rightKeys: [String]) {
        precondition(leftKeys.count == rightKeys.count, "join key count mismatch")
        self.left = left
        self.right = right
        self.leftKeys = leftKeys
        self.rightKeys = rightKeys
        self.schema = PlanSchema(columns: [])
    }

    public func open(context: ExecutionContext) throws {
        try left.open(context: context)
        try right.open(context: context)
        let combined = Array(Set(left.schema.columns + right.schema.columns))
        if !combined.isEmpty { schema = PlanSchema(columns: combined) }
        leftRow = try left.next()
        rightRow = try right.next()
        leftBuffer.removeAll(keepingCapacity: true)
        rightBuffer.removeAll(keepingCapacity: true)
    }

    public func next() throws -> PlanRow? {
        while let l = leftRow, let r = rightRow {
            let cmp = compare(lhs: l, rhs: r)
            if cmp == .orderedSame {
                try collectEquals(startingLeft: l, startingRight: r)
                if !leftBuffer.isEmpty && !rightBuffer.isEmpty {
                    let leftOut = leftBuffer.removeFirst()
                    let rightOut = rightBuffer.removeFirst()
                    return merge(leftOut, rightOut)
                }
            } else if cmp == .orderedAscending {
                leftRow = try left.next()
            } else {
                rightRow = try right.next()
            }
        }
        return nil
    }

    private func collectEquals(startingLeft: PlanRow, startingRight: PlanRow) throws {
        leftBuffer = [startingLeft]
        rightBuffer = [startingRight]

        var nextLeft = try left.next()
        while let candidate = nextLeft, compareKeys(candidate, startingRight) == .orderedSame {
            leftBuffer.append(candidate)
            nextLeft = try left.next()
        }
        leftRow = nextLeft

        var nextRight = try right.next()
        while let candidate = nextRight, compareKeys(startingLeft, candidate) == .orderedSame {
            rightBuffer.append(candidate)
            nextRight = try right.next()
        }
        rightRow = nextRight
    }

    private func compare(lhs: PlanRow, rhs: PlanRow) -> ComparisonResult {
        compareKeys(lhs, rhs)
    }

    private func compareKeys(_ lhs: PlanRow, _ rhs: PlanRow) -> ComparisonResult {
        for (lk, rk) in zip(leftKeys, rightKeys) {
            guard let lv = lhs.values[lk], let rv = rhs.values[rk] else { continue }
            let cmp = compareValues(lv, rv)
            if cmp != .orderedSame { return cmp }
        }
        return .orderedSame
    }

    private func compareValues(_ lhs: Value, _ rhs: Value) -> ComparisonResult {
        switch (lhs, rhs) {
        case (.int(let l), .int(let r)): return l == r ? .orderedSame : (l < r ? .orderedAscending : .orderedDescending)
        case (.double(let l), .double(let r)): return l == r ? .orderedSame : (l < r ? .orderedAscending : .orderedDescending)
        case (.bool(let l), .bool(let r)): return l == r ? .orderedSame : ((l == false && r == true) ? .orderedAscending : .orderedDescending)
        case (.string(let l), .string(let r)): return l == r ? .orderedSame : (l < r ? .orderedAscending : .orderedDescending)
        case (.null, .null): return .orderedSame
        case (.null, _): return .orderedAscending
        case (_, .null): return .orderedDescending
        default:
            return lhs.description.compare(rhs.description)
        }
    }

    private func merge(_ lhs: PlanRow, _ rhs: PlanRow) -> PlanRow {
        var merged = lhs.values
        for (k, v) in rhs.values { merged[k] = v }
        return PlanRow(values: merged)
    }

    public func close() throws {
        leftBuffer.removeAll(keepingCapacity: false)
        rightBuffer.removeAll(keepingCapacity: false)
        try left.close()
        try right.close()
    }
}

// MARK: - Parallel map (simple actor style)

public final class ParallelMapOperator: PlanOperator {
    public typealias Transform = @Sendable (PlanRow) -> PlanRow

    public let child: PlanOperator
    public let concurrency: Int
    public let transform: Transform
    public private(set) var schema: PlanSchema

    private var buffer: [PlanRow] = []
    private var iterator: IndexingIterator<[PlanRow]>?

    public init(child: PlanOperator, concurrency: Int = max(1, ProcessInfo.processInfo.processorCount / 2), transform: @escaping Transform) {
        self.child = child
        self.concurrency = max(1, concurrency)
        self.transform = transform
        self.schema = child.schema
    }

    public func open(context: ExecutionContext) throws {
        let rows = try child.materialize(context: context)
        let transformClosure = transform
        if concurrency <= 1 || rows.count <= 1 {
            buffer = rows.map(transformClosure)
            iterator = buffer.makeIterator()
            return
        }

        let workerCount = min(concurrency, rows.count)
        buffer = rows
        buffer.withUnsafeMutableBufferPointer { ptr in
            DispatchQueue.concurrentPerform(iterations: workerCount) { worker in
                let range = chunkRange(worker: worker, workers: workerCount, count: ptr.count)
                guard !range.isEmpty else { return }
                for index in range {
                    ptr[index] = transformClosure(rows[index])
                }
            }
        }
        iterator = buffer.makeIterator()
    }

    public func next() throws -> PlanRow? { iterator?.next() }

    public func close() throws {
        buffer.removeAll(keepingCapacity: false)
        iterator = nil
    }

    private func chunkRange(worker: Int, workers: Int, count: Int) -> Range<Int> {
        guard count > 0 else { return 0..<0 }
        let base = count / workers
        let remainder = count % workers
        let start = worker * base + min(worker, remainder)
        let extra = worker < remainder ? 1 : 0
        let end = start + base + extra
        return start..<end
    }
}

// MARK: - Limit

public final class LimitOperator: PlanOperator {
    public let child: PlanOperator
    public let limit: Int
    public let offset: Int
    public var schema: PlanSchema { child.schema }

    private var remaining: Int = 0
    private var skipped: Int = 0

    public init(child: PlanOperator, limit: Int, offset: Int = 0) {
        self.child = child
        self.limit = limit
        self.offset = max(0, offset)
    }

    public func open(context: ExecutionContext) throws {
        try child.open(context: context)
        remaining = limit
        skipped = 0
    }

    public func next() throws -> PlanRow? {
        guard remaining > 0 else { return nil }
        while let row = try child.next() {
            if skipped < offset {
                skipped += 1
                continue
            }
            remaining -= 1
            return row
        }
        return nil
    }

    public func close() throws { try child.close() }
}
