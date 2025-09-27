//
//  CLI+DataManipulation.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-27.
//
// Theme: Data manipulation commands (insert, delete, scan).

import Foundation
import ColibriCore

// MARK: - Data Manipulation Commands
extension CLI {
    /// Parses a raw input line and dispatches the associated command handler.
    mutating func parseAndRun(_ line: String) {
        let trimmed = line.trimmingCharacters(in: .whitespacesAndNewlines)
        guard !trimmed.isEmpty else { return }
        
        if trimmed == "\\help" { help(); return }
        if trimmed == "\\conf" { showConfig(); return }
        if trimmed == "\\dt" { listTables(); return }
        if trimmed == "\\exit" { exit(0) }

        if trimmed.hasPrefix("\\create table ") {
            let parts = trimmed.split(separator: " ")
            if parts.count >= 3 {
                let n = String(trimmed.dropFirst("\\create table ".count))
                do { try db.createTable(n) ; print("created \(n)") } catch { print("error: \(error)") }
            }
            return
        }

        if trimmed.hasPrefix("\\begin") {
            handleBegin()
            return
        }
        if trimmed.hasPrefix("\\commit") {
            let parts = trimmed.split(separator: " ")
            handleCommit(parts)
            return
        }
        if trimmed.hasPrefix("\\rollback") {
            let parts = trimmed.split(separator: " ")
            handleRollback(parts)
            return
        }

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
        
        // SQL commands
        if trimmed.hasPrefix("\\sql ") {
            let query = String(trimmed.dropFirst("\\sql ".count))
            executeSQL(query)
            return
        }

        print("Unrecognized command. Type \\help.")
    }

    /// Parses key-value pairs and inserts a row into the target table.
    private func handleInsert(_ rest: String) {
        let parts = rest.split(separator: " ")
        guard parts.count >= 2 else { print("usage: \\insert <table> col=val,..."); return }
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
            if let tid = currentTID { rid = try db.insert(into: table, row: row, tid: tid) }
            else { rid = try db.insert(into: table, row: row) }
            print("inserted \(rid)")
        } catch { print("error: \(error)") }
    }

    /// Converts a textual literal into a typed Value for storage.
    private func parseValue(_ s: String) -> Value {
        if let i = Int64(s) { return .int(i) }
        if s.lowercased() == "true" { return .bool(true) }
        if s.lowercased() == "false" { return .bool(false) }
        if let d = Double(s) { return .double(d) }
        if s.uppercased() == "NULL" { return .null }
        return .string(s)
    }

    /// Reads and prints every row stored in the given table.
    private func handleScan(_ rest: String) {
        let table = rest.trimmingCharacters(in: .whitespaces)
        do {
            let items = try db.scan(table)
            for (rid, row) in items { print("\(rid) -> \(row)") }
            if items.isEmpty { print("(empty)") }
        } catch { print("error: \(error)") }
    }

    /// Deletes rows matching one or more equality predicates.
    private mutating func handleDelete(_ rest: String) {
        // format: <table> col=val[,col2=val2]
        let parts = rest.split(separator: " ", maxSplits: 1)
        guard parts.count == 2 else { print("usage: \\delete <table> col=val[,col2=val2]"); return }
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
        guard !kvs.isEmpty else { print("usage: \\delete <table> col=val[,col2=val2]"); return }
        do {
            if kvs.count == 1 {
                let n: Int
                if let tid = currentTID { n = try db.deleteEquals(table: table, column: kvs[0].0, value: kvs[0].1, tid: tid) }
                else { n = try db.deleteEquals(table: table, column: kvs[0].0, value: kvs[0].1) }
                print("deleted \(n)")
            } else {
                let n: Int
                if let tid = currentTID { n = try db.deleteEqualsMulti(table: table, predicates: kvs, tid: tid) }
                else { n = try db.deleteEqualsMulti(table: table, predicates: kvs) }
                print("deleted \(n)")
            }
        } catch { print("error: \(error)") }
    }
}
