//
//  QueryPlanner.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// Theme: Planner brain mapping logical intents to optimized Volcano pipelines.

import Foundation

public enum QueryPredicateOperator {
    case equals
    case greaterOrEqual
    case lessOrEqual
}

public struct QueryPredicate {
    public let column: String
    public let op: QueryPredicateOperator
    public let value: Value
    public let selectivityHint: Double?

    public init(column: String, op: QueryPredicateOperator, value: Value, selectivityHint: Double? = nil) {
        self.column = column
        self.op = op
        self.value = value
        self.selectivityHint = selectivityHint
    }
}

public struct QueryTableRef {
    public let name: String
    public let alias: String?
    public var predicates: [QueryPredicate]
    public var projection: [String]?
    public var indexHint: String?

    public init(name: String,
                alias: String? = nil,
                predicates: [QueryPredicate] = [],
                projection: [String]? = nil,
                indexHint: String? = nil) {
        self.name = name
        self.alias = alias
        self.predicates = predicates
        self.projection = projection
        self.indexHint = indexHint
    }
}

public struct QueryJoinSpec {
    public enum JoinType { case inner }
    public let table: QueryTableRef
    public let type: JoinType
    public let leftColumns: [String]
    public let rightColumns: [String]

    public init(table: QueryTableRef,
                type: JoinType = .inner,
                leftColumns: [String],
                rightColumns: [String]) {
        self.table = table
        self.type = type
        self.leftColumns = leftColumns
        self.rightColumns = rightColumns
    }
}

public struct QueryRequest {
    public var root: QueryTableRef
    public var joins: [QueryJoinSpec]
    public var orderBy: [SortKey]
    public var limit: Int?
    public var parallelism: Int?
    public var cacheKey: String?
    public var useMaterializedCache: Bool

    public init(root: QueryTableRef,
                joins: [QueryJoinSpec] = [],
                orderBy: [SortKey] = [],
                limit: Int? = nil,
                parallelism: Int? = nil,
                cacheKey: String? = nil,
                useMaterializedCache: Bool = false) {
        self.root = root
        self.joins = joins
        self.orderBy = orderBy
        self.limit = limit
        self.parallelism = parallelism
        self.cacheKey = cacheKey
        self.useMaterializedCache = useMaterializedCache
    }
}

public final class QueryPlanner {
    private unowned let database: Database
    private let costModel: CostModel

    public init(database: Database) {
        self.database = database
        self.costModel = CostModel(database: database)
    }

    public func plan(request: QueryRequest, context: ExecutionContext) throws -> PlanOperator {
        let span = Signpost.begin(.planner,
                                  name: "PlannerPlan",
                                  message: request.cacheKey ?? request.root.name)
        defer { Signpost.end(span, message: "joins=\(request.joins.count)") }
        var rootOperator = try buildAccess(for: request.root)

        for joinSpec in request.joins {
            let rightOp = try buildAccess(for: joinSpec.table)
            let hash = HashJoinOperator(joinType: .inner,
                                        left: rootOperator,
                                        right: rightOp,
                                        leftKeys: qualified(joinSpec.leftColumns, alias: request.root.alias ?? request.root.name),
                                        rightKeys: qualified(joinSpec.rightColumns, alias: joinSpec.table.alias ?? joinSpec.table.name))
            let merge = MergeJoinOperator(joinType: .inner, left: rootOperator,
                                          right: rightOp,
                                          leftKeys: qualified(joinSpec.leftColumns, alias: request.root.alias ?? request.root.name),
                                          rightKeys: qualified(joinSpec.rightColumns, alias: joinSpec.table.alias ?? joinSpec.table.name))
            let hashCost = costModel.cost(of: hash)
            let mergeCost = costModel.cost(of: merge)
            if hashCost.cpu + hashCost.io <= mergeCost.cpu + mergeCost.io {
                rootOperator = hash
            } else {
                rootOperator = merge
            }
        }

        if !request.orderBy.isEmpty {
            rootOperator = SortOperator(child: rootOperator, keys: request.orderBy)
        }

        if let limit = request.limit {
            rootOperator = LimitOperator(child: rootOperator, limit: limit)
        }

        if let parallelism = request.parallelism, parallelism > 1 {
            rootOperator = ParallelMapOperator(child: rootOperator, concurrency: parallelism) { $0 }
        }

        return rootOperator
    }

    private func buildAccess(for ref: QueryTableRef) throws -> PlanOperator {
        let alias = ref.alias ?? ref.name
        let predicates = ref.predicates
        let equalityPredicates = predicates.filter { $0.op == .equals }
        let equalityMap = Dictionary(uniqueKeysWithValues: equalityPredicates.map { ($0.column, $0.value) })

        var candidates: [(PlanOperator, Double)] = []

        // Table scan candidate
        let tableScan = TableScanOperator(table: ref.name, alias: alias)
        let tableCost = costModel.cost(of: tableScan)
        candidates.append((tableScan, tableCost.cpu + tableCost.io))

        if let indexInfo = bestIndex(for: ref.name, using: ref.indexHint, equality: equalityMap) {
            let bounds = rangeBounds(for: indexInfo.columns, predicates: predicates)
            let indexOp = IndexScanOperator(table: ref.name,
                                            index: indexInfo.name,
                                            indexColumns: indexInfo.columns,
                                            bounds: bounds,
                                            alias: alias)
            let indexCost = costModel.cost(of: indexOp)
            candidates.append((indexOp, indexCost.cpu + indexCost.io))
        }

        let best = candidates.min(by: { $0.1 < $1.1 })?.0 ?? tableScan
        var current: PlanOperator = best

        if !ref.predicates.isEmpty {
            let nonIndex = predicates.filter { predicate in
                !(predicate.op == .equals && (best is IndexScanOperator) && equalityMap[predicate.column] != nil)
            }
            if !nonIndex.isEmpty {
                let planPredicate = PlanPredicate(columns: Set(nonIndex.map { "\(alias).\($0.column)" }),
                                                  selectivityHint: nonIndex.first?.selectivityHint) { row in
                    evaluate(predicates: nonIndex, row: row, alias: alias)
                }
                current = FilterOperator(child: current, predicate: planPredicate)
            }
        }

        if let projection = ref.projection {
            let qualifiedColumns = projection.map { "\(alias).\($0)" }
            current = ProjectOperator(child: current, projection: qualifiedColumns)
        }

        return current
    }

    private func bestIndex(for table: String, using hint: String?, equality: [String: Value]) -> (name: String, columns: [String])? {
        if let hint, let entry = database.indexes[table]?[hint] {
            return (hint, entry.columns)
        }
        guard let map = database.indexes[table] else { return nil }
        var bestMatch: (String, [String], Int)? = nil
        for (name, entry) in map {
            let prefixMatch = entry.columns.prefix { equality[$0] != nil }
            if prefixMatch.isEmpty { continue }
            let score = prefixMatch.count
            if let current = bestMatch {
                if score > current.2 { bestMatch = (name, Array(entry.columns), score) }
            } else {
                bestMatch = (name, Array(entry.columns), score)
            }
        }
        if let best = bestMatch { return (best.0, best.1) }
        return nil
    }

    private func qualified(_ columns: [String], alias: String) -> [String] {
        columns.map { col in
            if col.contains(".") { return col }
            return "\(alias).\(col)"
        }
    }

    private func rangeBounds(for columns: [String], predicates: [QueryPredicate]) -> IndexBounds {
        guard let first = columns.first else { return IndexBounds(lower: [], upper: []) }
        var lower: Value?
        var upper: Value?
        for predicate in predicates where predicate.column == first {
            switch predicate.op {
            case .greaterOrEqual:
                if let current = lower {
                    if compare(predicate.value, current) == .orderedDescending {
                        lower = predicate.value
                    }
                } else {
                    lower = predicate.value
                }
            case .lessOrEqual:
                if let current = upper {
                    if compare(predicate.value, current) == .orderedAscending {
                        upper = predicate.value
                    }
                } else {
                    upper = predicate.value
                }
            case .equals:
                lower = predicate.value
                upper = predicate.value
            }
        }
        let lowerArr = lower.map { [ $0 ] } ?? []
        let upperArr = upper.map { [ $0 ] } ?? []
        return IndexBounds(lower: lowerArr, upper: upperArr)
    }
}

private func evaluate(predicates: [QueryPredicate], row: PlanRow, alias: String) -> Bool {
    for predicate in predicates {
        let key = "\(alias).\(predicate.column)"
        guard let value = row.values[key] else { return false }
        switch predicate.op {
        case .equals:
            if value != predicate.value { return false }
        case .greaterOrEqual:
            if compare(value, predicate.value) == .orderedAscending { return false }
        case .lessOrEqual:
            if compare(value, predicate.value) == .orderedDescending { return false }
        }
    }
    return true
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
        return lhs.description.compare(rhs.description)
    }
}
