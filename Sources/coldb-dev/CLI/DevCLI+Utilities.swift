//
//  DevCLI+Utilities.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Utility commands for development CLI (import/export, fault injection, etc.).

import Foundation
import ColibriCore

extension DevCLI {
    
    /// Handles utility commands (import/export, fault injection, etc.)
    mutating func handleUtilityCommands(_ trimmed: String) {
        if trimmed.hasPrefix("\\import ") {
            handleImport(String(trimmed.dropFirst("\\import ".count)))
            return
        }
        
        if trimmed.hasPrefix("\\export ") {
            handleExport(String(trimmed.dropFirst("\\export ".count)))
            return
        }
        
        if trimmed == "\\stats prometheus" {
            printPrometheus()
            return
        }
        
        if trimmed.hasPrefix("\\fault set ") {
            handleFaultSet(String(trimmed.dropFirst("\\fault set ".count)))
            return
        }
        
        if trimmed == "\\fault clear" {
            FaultInjector.shared.clear()
            print("faults cleared")
            return
        }
    }
    
    /// Handles import/export commands
    mutating func handleImportExportCommands(_ trimmed: String) {
        if trimmed.hasPrefix("\\import ") {
            handleImport(String(trimmed.dropFirst("\\import ".count)))
            return
        }
        
        if trimmed.hasPrefix("\\export ") {
            handleExport(String(trimmed.dropFirst("\\export ".count)))
            return
        }
    }
    
    /// Handles fault injection commands
    mutating func handleFaultCommands(_ trimmed: String) {
        if trimmed.hasPrefix("\\fault set ") {
            handleFaultSet(String(trimmed.dropFirst("\\fault set ".count)))
            return
        }
        
        if trimmed == "\\fault clear" {
            FaultInjector.shared.clear()
            print("faults cleared")
            return
        }
    }

    /// Loads CSV rows into a table using the first row as the header.
    private func handleImport(_ rest: String) {
        // format: <file.csv> INTO <table>
        let parts = rest.split(separator: " ")
        guard let intoIdx = parts.firstIndex(where: { $0.uppercased() == "INTO" }) else { 
            print("usage: \\import <file.csv> INTO <table>")
            return 
        }
        let file = parts.prefix(upTo: intoIdx).joined(separator: " ")
        let table = parts.suffix(from: parts.index(after: intoIdx)).joined(separator: " ")
        guard !file.isEmpty, !table.isEmpty else { 
            print("usage: \\import <file.csv> INTO <table>")
            return 
        }
        let path = String(file)
        let tname = String(table)
        do {
            let data = try String(contentsOfFile: path, encoding: .utf8)
            let lines = data.components(separatedBy: .newlines)
            guard let headerLine = lines.first(where: { !$0.trimmingCharacters(in: .whitespaces).isEmpty }) else { 
                print("empty file")
                return 
            }
            let headers = headerLine.split(separator: ",").map { String($0).trimmingCharacters(in: .whitespaces) }
            guard !headers.isEmpty else { 
                print("missing CSV header")
                return 
            }
            var imported = 0
            var started = false
            for line in lines {
                // skip lines until (and including) header
                if !started { 
                    if line == headerLine { started = true }
                    continue 
                }
                if line.trimmingCharacters(in: .whitespaces).isEmpty { 
                    continue 
                }
                let fields = line.split(separator: ",", omittingEmptySubsequences: false).map { String($0) }
                var row: Row = [:]
                for (i, h) in headers.enumerated() {
                    let v = i < fields.count ? parseValue(fields[i]) : .null
                    row[h] = v
                }
                _ = try db.insert(into: tname, row: row)
                imported += 1
            }
            print("imported \(imported) rows")
        } catch {
            print("error: \(error)")
        }
    }

    /// Exports table contents to CSV, materializing a synthesized header.
    private func handleExport(_ rest: String) {
        // format: <table> TO <file.csv>
        let parts = rest.split(separator: " ")
        guard let toIdx = parts.firstIndex(where: { $0.uppercased() == "TO" }) else { 
            print("usage: \\export <table> TO <file.csv>")
            return 
        }
        let table = parts.prefix(upTo: toIdx).joined(separator: " ")
        let file = parts.suffix(from: parts.index(after: toIdx)).joined(separator: " ")
        guard !file.isEmpty, !table.isEmpty else { 
            print("usage: \\export <table> TO <file.csv>")
            return 
        }
        do {
            let tname = String(table)
            let items = try db.scan(tname)
            // Collect column set
            var colsSet = Set<String>()
            for (_, row) in items { 
                for (k, _) in row { 
                    colsSet.insert(k) 
                } 
            }
            let cols = colsSet.sorted()
            func csvEscape(_ s: String) -> String {
                if s.contains(",") || s.contains("\"") || s.contains("\n") {
                    let escaped = s.replacingOccurrences(of: "\"", with: "\"\"")
                    return "\"\(escaped)\""
                }
                return s
            }
            var out = cols.joined(separator: ",") + "\n"
            for (_, row) in items {
                var fields: [String] = []
                for c in cols {
                    let val = row[c]
                    let s: String
                    switch val {
                    case .some(.string(let v)): s = v
                    case .some(.int(let i)): s = String(i)
                    case .some(.double(let d)): s = String(d)
                    case .some(.bool(let b)): s = b ? "true" : "false"
                    case .some(.null): s = ""
                    case .some(.date(let d)): s = ISO8601DateFormatter().string(from: d)
                    case .some(.decimal(let d)): s = d.description
                    case .some(.blob(let d)): s = "<BLOB:\(d.count) bytes>"
                    case .some(.json(let d)): s = String(data: d, encoding: .utf8) ?? "<INVALID JSON>"
                    case .some(.enumValue(let enumName, let value)): s = "\(enumName).\(value)"
                    case .none: s = ""
                    }
                    fields.append(csvEscape(s))
                }
                out.append(fields.joined(separator: ","))
                out.append("\n")
            }
            try out.write(toFile: String(file), atomically: true, encoding: .utf8)
            print("exported \(items.count) rows")
        } catch {
            print("error: \(error)")
        }
    }

    /// Emits current metrics formatted for Prometheus scraping.
    private func printPrometheus() {
        let agg = db.bufferPoolAggregateNumbers()
        print("colibridb_buffer_hits_total \(agg.hits)")
        print("colibridb_buffer_misses_total \(agg.misses)")
        print("colibridb_buffer_evictions_total \(agg.evictions)")
        print("colibridb_buffer_pages \(agg.pages)")
        print("colibridb_buffer_capacity \(agg.capacity)")
        print("colibridb_buffer_pinned \(agg.pinned)")
        print("colibridb_buffer_dirty \(agg.dirty)")
        print("colibridb_vacuum_runs_total \(db.vacuumRuns)")
        print("colibridb_vacuum_pages_compacted_total \(db.vacuumTotalPagesCompacted)")
        print("colibridb_vacuum_bytes_reclaimed_total \(db.vacuumTotalBytesReclaimed)")
        let ts = db.vacuumLastRun?.timeIntervalSince1970 ?? 0
        print("colibridb_vacuum_last_run_timestamp_seconds \(Int(ts))")
    }

    /// Arms the fault injector to trigger after a configurable countdown.
    private func handleFaultSet(_ rest: String) {
        // format: <key> <n>
        let parts = rest.split(separator: " ")
        guard parts.count >= 2, let n = Int(parts[1]) else { 
            print("usage: \\fault set <key> <n>")
            return 
        }
        FaultInjector.shared.set(key: String(parts[0]), remaining: n)
        print("fault set for \(parts[0]) = \(n)")
    }
}
