//
//  DevCLI+Data.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Data manipulation commands for development CLI.

import Foundation
import ColibriCore

extension DevCLI {
    
    /// Handles data manipulation commands (insert, scan, delete)
    mutating func handleDataCommands(_ trimmed: String) {
        if trimmed.hasPrefix("\\insert ") {
            handleInsert(String(trimmed.dropFirst("\\insert ".count)))
            return
        }
        
        if trimmed.hasPrefix("\\scan ") {
            handleScan(String(trimmed.dropFirst("\\scan ".count)))
            return
        }
        
        if trimmed.hasPrefix("\\delete ") {
            handleDelete(String(trimmed.dropFirst("\\delete ".count)))
            return
        }
    }
    
    /// Parses key-value pairs and inserts a row into the target table.
    private func handleInsert(_ rest: String) {
        let parts = rest.split(separator: " ")
        guard parts.count >= 2 else { 
            print("usage: \\insert <table> col=val,...")
            return 
        }
        let table = String(parts[0])
        let kvStr = parts.dropFirst().joined(separator: " ")
        var row: Row = [:]
        for item in kvStr.split(separator: ",") {
            let p = item.split(separator: "=", maxSplits: 1)
            guard p.count == 2 else { continue }
            let key = String(p[0]).trimmingCharacters(in: .whitespaces)
            let valRaw = String(p[1]).trimmingCharacters(in: .whitespaces)
            row[key] = parseValue(valRaw)
        }
        do {
            let rid: RID
            if let tid = currentTID { 
                rid = try db.insert(into: table, row: row, tid: tid) 
            } else { 
                rid = try db.insert(into: table, row: row) 
            }
            print("inserted \(rid)")
        } catch { 
            print("error: \(error)") 
        }
    }

    /// Converts a textual literal into a typed Value for storage.
    public func parseValue(_ s: String) -> Value {
        // Handle NULL
        if s.uppercased() == "NULL" { return .null }
        
        // Handle boolean values
        if s.lowercased() == "true" { return .bool(true) }
        if s.lowercased() == "false" { return .bool(false) }
        
        // Handle numeric values
        if let i = Int64(s) { return .int(i) }
        if let d = Double(s) { return .double(d) }
        
        // Handle decimal values (with 'd' suffix)
        if s.hasSuffix("d") || s.hasSuffix("D") {
            let decimalStr = String(s.dropLast())
            if let decimal = Decimal(string: decimalStr) { return .decimal(decimal) }
        }
        
        // Handle date values (ISO8601 format)
        if s.hasPrefix("'") && s.hasSuffix("'") {
            let dateStr = String(s.dropFirst().dropLast())
            if let date = ISO8601DateFormatter().date(from: dateStr) { return .date(date) }
        }
        
        // Handle JSON values (with 'j' prefix)
        if s.hasPrefix("j:") {
            let jsonStr = String(s.dropFirst(2))
            if let jsonData = jsonStr.data(using: .utf8) { return .json(jsonData) }
        }
        
        // Handle BLOB values (with 'b:' prefix)
        if s.hasPrefix("b:") {
            let blobStr = String(s.dropFirst(2))
            if let blobData = Data(base64Encoded: blobStr) { return .blob(blobData) }
        }
        
        // Handle ENUM values (with 'e:' prefix)
        if s.hasPrefix("e:") {
            let enumStr = String(s.dropFirst(2))
            let parts = enumStr.split(separator: ".", maxSplits: 1)
            if parts.count == 2 {
                return .enumValue(String(parts[0]), String(parts[1]))
            }
        }
        
        // Default to string
        return .string(s)
    }

    /// Reads and prints every row stored in the given table.
    private func handleScan(_ rest: String) {
        let table = rest.trimmingCharacters(in: .whitespaces)
        do {
            let items = try db.scan(table)
            for (rid, row) in items { 
                print("\(rid) -> \(row)") 
            }
            if items.isEmpty { 
                print("(empty)") 
            }
        } catch { 
            print("error: \(error)") 
        }
    }

    /// Deletes rows matching one or more equality predicates.
    private mutating func handleDelete(_ rest: String) {
        // format: <table> col=val[,col2=val2]
        let parts = rest.split(separator: " ", maxSplits: 1)
        guard parts.count == 2 else { 
            print("usage: \\delete <table> col=val[,col2=val2]")
            return 
        }
        let table = String(parts[0])
        let kvRaw = String(parts[1])
        var kvs: [(String, Value)] = []
        for item in kvRaw.split(separator: ",") {
            let p = item.split(separator: "=", maxSplits: 1)
            guard p.count == 2 else { continue }
            let key = String(p[0]).trimmingCharacters(in: .whitespaces)
            let val = parseValue(String(p[1]).trimmingCharacters(in: .whitespaces))
            kvs.append((key, val))
        }
        guard !kvs.isEmpty else { 
            print("usage: \\delete <table> col=val[,col2=val2]")
            return 
        }
        do {
            if kvs.count == 1 {
                let n: Int
                if let tid = currentTID { 
                    n = try db.deleteEquals(table: table, column: kvs[0].0, value: kvs[0].1, tid: tid) 
                } else { 
                    n = try db.deleteEquals(table: table, column: kvs[0].0, value: kvs[0].1) 
                }
                print("deleted \(n)")
            } else {
                let n: Int
                if let tid = currentTID { 
                    n = try db.deleteEqualsMulti(table: table, predicates: kvs, tid: tid) 
                } else { 
                    n = try db.deleteEqualsMulti(table: table, predicates: kvs) 
                }
                print("deleted \(n)")
            }
        } catch { 
            print("error: \(error)") 
        }
    }
}
