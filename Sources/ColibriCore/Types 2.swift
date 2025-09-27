//
//  Types.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Value palette representing rows, scalars, and encoders.

import Foundation

/// Record Identifier (pageId, slotId)
public struct RID: Hashable, Codable, CustomStringConvertible {
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

/// Extended value types for rows with additional data types
public enum Value: Codable, Hashable, CustomStringConvertible, Sendable {
    case int(Int64)
    case double(Double)
    case bool(Bool)
    case string(String)
    case null
    // Extended types
    case date(Date)
    case decimal(Decimal)
    case blob(Data)
    case json(Data) // JSON stored as Data for efficiency
    case enumValue(String, String) // (enumName, value)

    public var description: String {
        switch self {
        case .int(let v): return String(v)
        case .double(let v): return String(v)
        case .bool(let v): return String(v)
        case .string(let v): return v
        case .null: return "NULL"
        case .date(let v): return ISO8601DateFormatter().string(from: v)
        case .decimal(let v): return v.description
        case .blob(let v): return "<BLOB:\(v.count) bytes>"
        case .json(let v): return String(data: v, encoding: .utf8) ?? "<INVALID JSON>"
        case .enumValue(let enumName, let value): return "\(enumName).\(value)"
        }
    }
    
    /// Returns the data type name for this value
    public var typeName: String {
        switch self {
        case .int: return "INT"
        case .double: return "DOUBLE"
        case .bool: return "BOOL"
        case .string: return "TEXT"
        case .null: return "NULL"
        case .date: return "DATE"
        case .decimal: return "DECIMAL"
        case .blob: return "BLOB"
        case .json: return "JSON"
        case .enumValue(let enumName, _): return "ENUM(\(enumName))"
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
