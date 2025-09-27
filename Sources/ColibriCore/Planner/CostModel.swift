//
//  CostModel.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// Theme: Cost oracle estimating cardinalities and resource usage for plans.

import Foundation

public struct PlanCost {
    public var rows: Double
    public var cpu: Double
    public var io: Double
    public var memory: Double

    public static var zero: PlanCost { PlanCost(rows: 0, cpu: 0, io: 0, memory: 0) }

    public mutating func add(_ other: PlanCost) {
        rows = max(rows, other.rows)
        cpu += other.cpu
        io += other.io
        memory = max(memory, other.memory)
    }
}

public struct CardinalityEstimate {
    public var rows: Double
    public var confidence: Double
}

public final class CardinalityEstimator {
    private unowned let database: Database

    public init(database: Database) {
        self.database = database
    }

    public func estimateScan(table: String) -> CardinalityEstimate {
        if let stats = database.tableStatistics[table] {
            return CardinalityEstimate(rows: max(1, Double(stats.rowCount)), confidence: 0.9)
        }
        // Fallback heuristic: assume medium sized table
        return CardinalityEstimate(rows: 1_000, confidence: 0.2)
    }

    public func estimateFilter(base: CardinalityEstimate, predicate: PlanPredicate) -> CardinalityEstimate {
        let selectivity = predicate.selectivityHint ?? 0.1
        return CardinalityEstimate(rows: max(1, base.rows * selectivity), confidence: base.confidence * 0.9)
    }

    public func estimateJoin(left: CardinalityEstimate, right: CardinalityEstimate, keys: Int) -> CardinalityEstimate {
        if keys == 0 { return CardinalityEstimate(rows: left.rows * right.rows, confidence: min(left.confidence, right.confidence) * 0.2) }
        let avgCard = max(1, min(left.rows, right.rows))
        return CardinalityEstimate(rows: avgCard, confidence: min(left.confidence, right.confidence) * 0.6)
    }
}

public final class CostModel {
    private let estimator: CardinalityEstimator
    private let pageSize: Double
    private unowned let database: Database

    public init(database: Database) {
        self.database = database
        self.estimator = CardinalityEstimator(database: database)
        self.pageSize = Double(database.config.pageSizeBytes)
    }

    public func cost(of op: PlanOperator) -> PlanCost {
        switch op {
        case let scan as TableScanOperator:
            return costTableScan(scan)
        case let filter as FilterOperator:
            return costFilter(filter)
        case let vfilter as VectorizedFilterOperator:
            let base = cost(of: vfilter.child)
            // Assume better CPU efficiency per batch
            return PlanCost(rows: base.rows, cpu: base.cpu * 0.8, io: base.io, memory: base.memory)
        case let project as ProjectOperator:
            return costProject(project)
        case let vproj as VectorizedProjectOperator:
            let base = cost(of: vproj.child)
            return PlanCost(rows: base.rows, cpu: base.cpu * 0.9, io: base.io, memory: base.memory)
        case let sort as SortOperator:
            return costSort(sort)
        case let hashJoin as HashJoinOperator:
            return costHashJoin(hashJoin)
        case let mergeJoin as MergeJoinOperator:
            return costMergeJoin(mergeJoin)
        case let parallel as ParallelMapOperator:
            return costParallel(parallel)
        default:
            return PlanCost(rows: 1_000, cpu: 1_000, io: 100, memory: 1)
        }
    }

    private func costTableScan(_ op: TableScanOperator) -> PlanCost {
        let card = estimator.estimateScan(table: op.table)
        let rowSize = averageRowSize(for: op.table)
        let pages = (card.rows * rowSize) / pageSize
        return PlanCost(rows: card.rows,
                        cpu: card.rows,
                        io: max(1, pages),
                        memory: 0)
    }

    private func costFilter(_ op: FilterOperator) -> PlanCost {
        let childCost = cost(of: op.child)
        let childCard = CardinalityEstimate(rows: childCost.rows, confidence: 0.7)
        let filtered = estimator.estimateFilter(base: childCard, predicate: op.predicate)
        return PlanCost(rows: filtered.rows,
                        cpu: childCost.cpu + childCost.rows,
                        io: childCost.io,
                        memory: childCost.memory)
    }

    private func costProject(_ op: ProjectOperator) -> PlanCost {
        let child = cost(of: op.child)
        return PlanCost(rows: child.rows, cpu: child.cpu, io: child.io, memory: child.memory)
    }

    private func costSort(_ op: SortOperator) -> PlanCost {
        let childCost = cost(of: op.child)
        let n = childCost.rows
        // TimSort/merge sort n log n cost by default.
        let cpu = childCost.cpu + n * log2(max(2, n))
        let memory = childCost.memory + n
        return PlanCost(rows: childCost.rows, cpu: cpu, io: childCost.io + n, memory: memory)
    }

    private func costHashJoin(_ op: HashJoinOperator) -> PlanCost {
        let leftCost = cost(of: op.left)
        let rightCost = cost(of: op.right)
        let card = estimator.estimateJoin(left: CardinalityEstimate(rows: leftCost.rows, confidence: 0.8),
                                          right: CardinalityEstimate(rows: rightCost.rows, confidence: 0.8),
                                          keys: op.leftKeys.count)
        let buildCost = rightCost.rows
        let probeCost = leftCost.rows
        let memory = rightCost.rows
        return PlanCost(rows: card.rows,
                        cpu: leftCost.cpu + rightCost.cpu + buildCost + probeCost,
                        io: leftCost.io + rightCost.io,
                        memory: memory)
    }

    private func costMergeJoin(_ op: MergeJoinOperator) -> PlanCost {
        let leftCost = cost(of: op.left)
        let rightCost = cost(of: op.right)
        let card = estimator.estimateJoin(left: CardinalityEstimate(rows: leftCost.rows, confidence: 0.8),
                                          right: CardinalityEstimate(rows: rightCost.rows, confidence: 0.8),
                                          keys: op.leftKeys.count)
        let cpu = leftCost.cpu + rightCost.cpu + leftCost.rows + rightCost.rows
        return PlanCost(rows: card.rows,
                        cpu: cpu,
                        io: leftCost.io + rightCost.io,
                        memory: max(leftCost.memory, rightCost.memory))
    }

    private func costParallel(_ op: ParallelMapOperator) -> PlanCost {
        let child = cost(of: op.child)
        let cpu = child.cpu / Double(op.concurrency)
        return PlanCost(rows: child.rows, cpu: cpu, io: child.io, memory: child.memory)
    }

    private func averageRowSize(for table: String) -> Double {
        database.tableStatistics[table]?.avgRowSizeBytes ?? 128
    }
}
