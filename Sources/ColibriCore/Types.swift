//
//  Types.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Value palette representing rows, scalars, and encoders.

import Foundation

/// Record Identifier (pageId, slotId)
public struct RID: Hashable, Codable, CustomStringConvertible, Sendable {
    public let pageId: UInt64
    public let slotId: UInt16
    public init(pageId: UInt64, slotId: UInt16) {
        self.pageId = pageId
        self.slotId = slotId
    }
    public var description: String { "RID(\(pageId),\(slotId))" }
}

/// Logical Page Identifier
public typealias PageID = UInt64

/// Simple value types for rows (MVP)
public enum Value: Codable, Hashable, CustomStringConvertible, Sendable {
    case int(Int64)
    case double(Double)
    case bool(Bool)
    case string(String)
    case null
    case decimal(Decimal)
    case date(Date)

    public var description: String {
        switch self {
        case .int(let v): return String(v)
        case .double(let v): return String(v)
        case .bool(let v): return String(v)
        case .string(let v): return v
        case .null: return "NULL"
        case .decimal(let v): return String(describing: v)
        case .date(let v): return ISO8601DateFormatter().string(from: v)
        }
    }
}

/// Row represented as ordered dictionary (stable key order not guaranteed)
public typealias Row = [String: Value]

/// Cached statistics about a table used by the optimizer.
public struct TableStatistics: Codable {
    public let table: String
    public let rowCount: Int
    public let deadRowCount: Int
    public let avgRowSizeBytes: Double
    public let fragmentation: HeapFragmentationStats?
    public let columnCardinality: [String: Int]
    public let sampledRowCount: Int
    public let updatedAt: Date
}

/// Basic index statistics surfaced to the optimizer.
public struct IndexStatistics: Codable {
    public let table: String
    public let name: String
    public let entryCount: Int
    public let height: Int
    public let leafOccupancy: Double
    public let updatedAt: Date
}
