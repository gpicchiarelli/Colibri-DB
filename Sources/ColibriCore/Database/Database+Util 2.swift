//
//  Database+Util.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Utility toolbox offering helpers shared across subsystems.

import Foundation

extension Database {
    func rowDescription(_ row: Row) -> [String:String] {
        var m: [String:String] = [:]
        for (k,v) in row { m[k] = stringFromValue(v) }
        return m
    }

    func stringFromValue(_ v: Value) -> String {
        switch v {
        case .string(let s): return s
        case .int(let i): return String(i)
        case .double(let d): return String(d)
        case .bool(let b): return String(b)
        case .null: return ""
        case .date(let d): return ISO8601DateFormatter().string(from: d)
        case .decimal(let d): return d.description
        case .blob(let d): return "<BLOB:\(d.count) bytes>"
        case .json(let d): return String(data: d, encoding: .utf8) ?? "<INVALID JSON>"
        case .enumValue(let enumName, let value): return "\(enumName).\(value)"
        }
    }
}


