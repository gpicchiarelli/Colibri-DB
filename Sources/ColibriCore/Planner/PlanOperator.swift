//
//  PlanOperator.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// Theme: Volcano backbone defining iterator interfaces for query plans.

import Foundation
import Dispatch

/// Execution-time row used by the planner/executor pipeline.
public struct PlanRow: Sendable {
    public var values: [String: Value]
    public init(values: [String: Value]) { self.values = values }
    public subscript(column: String) -> Value? { values[column] }
}

/// Schema wrapper that tracks column order and metadata for a row stream.
public struct PlanSchema {
    public let columns: [String]
    public init(columns: [String]) { self.columns = columns }

    public func project(_ row: PlanRow, into subset: [String]) -> PlanRow {
        var projected: [String: Value] = [:]
        for col in subset {
            if let v = row.values[col] {
                projected[col] = v
            }
        }
        return PlanRow(values: projected)
    }
}

/// Volcano style operator definition (open/next/close).
public protocol PlanOperator: AnyObject {
    var schema: PlanSchema { get }
    func open(context: ExecutionContext) throws
    func next() throws -> PlanRow?
    func close() throws
}

/// Convenience to materialize all rows from an operator.
extension PlanOperator {
    public func materialize(context: ExecutionContext) throws -> [PlanRow] {
        try open(context: context)
        defer { try? close() }
        var rows: [PlanRow] = []
        while let row = try next() {
            rows.append(row)
        }
        return rows
    }
}

/// Execution context bridging the planner to database services and metrics.
public final class ExecutionContext {
    public let database: Database
    public let transactionId: UInt64?
    public let queue: DispatchQueue

    public init(database: Database, transactionId: UInt64?, queue: DispatchQueue = DispatchQueue(label: "ColibriDB.Execution", attributes: .concurrent)) {
        self.database = database
        self.transactionId = transactionId
        self.queue = queue
    }
}
