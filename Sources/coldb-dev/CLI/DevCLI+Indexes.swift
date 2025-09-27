//
//  DevCLI+Indexes.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Index management commands for development CLI.

import Foundation
import ColibriCore

extension DevCLI {
    
    /// Handles index-related commands
    mutating func handleIndexCommands(_ trimmed: String) {
        if trimmed.hasPrefix("\\create index ") {
            handleCreateIndex(String(trimmed.dropFirst("\\create index ".count)))
            return
        }
        
        if trimmed.hasPrefix("\\indexes ") {
            handleListIndexes(String(trimmed.dropFirst("\\indexes ".count)))
            return
        }
        
        if trimmed.hasPrefix("\\index search ") {
            handleIndexSearch(String(trimmed.dropFirst("\\index search ".count)))
            return
        }
        
        if trimmed.hasPrefix("\\index range ") {
            handleIndexRange(String(trimmed.dropFirst("\\index range ".count)))
            return
        }
        
        if trimmed.hasPrefix("\\index validate ") {
            handleIndexValidate(String(trimmed.dropFirst("\\index validate ".count)))
            return
        }
        
        if trimmed.hasPrefix("\\index rebuild ") {
            handleIndexRebuild(String(trimmed.dropFirst("\\index rebuild ".count)))
            return
        }
        
        if trimmed.hasPrefix("\\index validate-deep ") {
            handleIndexValidateDeep(String(trimmed.dropFirst("\\index validate-deep ".count)))
            return
        }
        
        if trimmed.hasPrefix("\\index rebuild-bulk ") {
            handleIndexRebuildBulk(String(trimmed.dropFirst("\\index rebuild-bulk ".count)))
            return
        }
        
        if trimmed.hasPrefix("\\index dump-header ") {
            handleIndexDumpHeader(String(trimmed.dropFirst("\\index dump-header ".count)))
            return
        }
        
        if trimmed.hasPrefix("\\index dump-leaves ") {
            handleIndexDumpLeaves(String(trimmed.dropFirst("\\index dump-leaves ".count)))
            return
        }
        
        if trimmed.hasPrefix("\\index compact ") {
            handleIndexCompact(String(trimmed.dropFirst("\\index compact ".count)))
            return
        }
    }

    /// Parses arguments and creates an index using the chosen backend.
    private func handleCreateIndex(_ rest: String) {
        // format: <name> ON <table>(<col>) USING <kind>
        // Simple parse
        let parts = rest.split(separator: " ")
        guard parts.count >= 4 else { 
            print("usage: \\create index <name> ON <table>(<col>) USING <Hash|ART>")
            return 
        }
        let name = String(parts[0])
        guard let onIdx = parts.firstIndex(where: { $0.uppercased() == "ON" }) else { 
            print("missing ON")
            return 
        }
        let tableAndCol = parts[parts.index(after: onIdx)]
        guard let l = tableAndCol.firstIndex(of: "("), let r = tableAndCol.firstIndex(of: ")") else { 
            print("table(col) malformed")
            return 
        }
        let table = String(tableAndCol[..<l])
        let colsRaw = String(tableAndCol[tableAndCol.index(after: l)..<r])
        let cols = colsRaw.split(separator: ",").map { $0.trimmingCharacters(in: .whitespaces) }
        guard let usingIdx = parts.firstIndex(where: { $0.uppercased() == "USING" }), 
              parts.index(after: usingIdx) < parts.endIndex else { 
            print("missing USING kind")
            return 
        }
        let kind = String(parts[parts.index(after: usingIdx)])
        do { 
            try db.createIndex(name: name, on: table, columns: cols, using: kind)
            print("index created") 
        } catch { 
            print("error: \(error)") 
        }
    }

    /// Lists index names associated with a table.
    private func handleListIndexes(_ rest: String) {
        let table = rest.trimmingCharacters(in: .whitespaces)
        let names = db.listIndexes(table: table)
        if names.isEmpty { 
            print("(no indexes)") 
        } else { 
            names.forEach { print($0) } 
        }
    }

    /// Runs an equality probe against a specific index.
    private func handleIndexSearch(_ rest: String) {
        let parts = rest.split(separator: " ")
        guard parts.count >= 3 else { 
            print("usage: \\index search <table> <index> <value>")
            return 
        }
        let table = String(parts[0])
        let index = String(parts[1])
        let raw = String(parts[2])
        if raw.contains(",") {
            let vs = raw.split(separator: ",").map { parseValue(String($0)) }
            do { 
                let r = try db.indexSearchEqualsValues(table: table, index: index, values: vs)
                r.forEach { print($0) }
                if r.isEmpty { print("(none)") } 
            } catch { 
                print("error: \(error)") 
            }
        } else {
            let v = parseValue(raw)
            do { 
                let r = try db.indexSearchEqualsTyped(table: table, index: index, value: v)
                r.forEach { print($0) }
                if r.isEmpty { print("(none)") } 
            } catch { 
                print("error: \(error)") 
            }
        }
    }

    /// Executes a range lookup on the selected index.
    private func handleIndexRange(_ rest: String) {
        let parts = rest.split(separator: " ")
        guard parts.count >= 4 else { 
            print("usage: \\index range <table> <index> <lo> <hi>")
            return 
        }
        let table = String(parts[0])
        let index = String(parts[1])
        let loRaw = String(parts[2])
        let hiRaw = String(parts[3])
        if loRaw.contains(",") || hiRaw.contains(",") {
            let loVals = loRaw.isEmpty ? nil : loRaw.split(separator: ",").map { parseValue(String($0)) }
            let hiVals = hiRaw.isEmpty ? nil : hiRaw.split(separator: ",").map { parseValue(String($0)) }
            do { 
                let r = try db.indexRangeValues(table: table, index: index, lo: loVals, hi: hiVals)
                r.forEach { print($0) }
                if r.isEmpty { print("(none)") } 
            } catch { 
                print("error: \(error)") 
            }
        } else {
            let loV = parseValue(loRaw)
            let hiV = parseValue(hiRaw)
            do { 
                let r = try db.indexRangeTyped(table: table, index: index, lo: loV, hi: hiV)
                r.forEach { print($0) }
                if r.isEmpty { print("(none)") } 
            } catch { 
                print("error: \(error)") 
            }
        }
    }

    /// Runs lightweight validation and reports coverage stats.
    private func handleIndexValidate(_ rest: String) {
        let parts = rest.split(separator: " ")
        guard parts.count >= 2 else { 
            print("usage: \\index validate <table> <index>")
            return 
        }
        let table = String(parts[0])
        let index = String(parts[1])
        do { 
            let r = try db.validateIndex(table: table, index: index)
            print("total=\(r.total) indexed=\(r.indexed) missing=\(r.missing)") 
        } catch { 
            print("error: \(error)") 
        }
    }

    /// Triggers a full logical rebuild of an index.
    private func handleIndexRebuild(_ rest: String) {
        let parts = rest.split(separator: " ")
        guard parts.count >= 2 else { 
            print("usage: \\index rebuild <table> <index>")
            return 
        }
        let table = String(parts[0])
        let index = String(parts[1])
        do { 
            try db.rebuildIndex(table: table, index: index)
            print("rebuild done") 
        } catch { 
            print("error: \(error)") 
        }
    }

    /// Performs deep validation and prints structural diagnostics.
    private func handleIndexValidateDeep(_ rest: String) {
        let parts = rest.split(separator: " ")
        guard parts.count >= 2 else { 
            print("usage: \\index validate-deep <table> <index>")
            return 
        }
        let table = String(parts[0])
        let index = String(parts[1])
        do { 
            let report = try db.validateIndexDeep(table: table, index: index)
            print(report) 
        } catch { 
            print("error: \(error)") 
        }
    }

    /// Rebuilds an index using the bulk-loading routine.
    private func handleIndexRebuildBulk(_ rest: String) {
        let parts = rest.split(separator: " ")
        guard parts.count >= 2 else { 
            print("usage: \\index rebuild-bulk <table> <index>")
            return 
        }
        let table = String(parts[0])
        let index = String(parts[1])
        do { 
            try db.rebuildIndexBulk(table: table, index: index)
            print("bulk rebuild done") 
        } catch { 
            print("error: \(error)") 
        }
    }

    /// Prints internal header information for the specified index page.
    private func handleIndexDumpHeader(_ rest: String) {
        // format: <table> <index> [pageId]
        let parts = rest.split(separator: " ")
        guard parts.count >= 2 else { 
            print("usage: \\index dump-header <table> <index> [pageId]")
            return 
        }
        let table = String(parts[0])
        let index = String(parts[1])
        let pid: UInt64? = parts.count >= 3 ? UInt64(parts[2]) : nil
        do { 
            let s = try db.indexDumpHeader(table: table, index: index, pageId: pid)
            print(s) 
        } catch { 
            print("error: \(error)") 
        }
    }

    /// Prints a sample of leaf pages to aid diagnostics.
    private func handleIndexDumpLeaves(_ rest: String) {
        // format: <table> <index> [count]
        let parts = rest.split(separator: " ")
        guard parts.count >= 2 else { 
            print("usage: \\index dump-leaves <table> <index> [count]")
            return 
        }
        let table = String(parts[0])
        let index = String(parts[1])
        let count = parts.count >= 3 ? (Int(parts[2]) ?? 3) : 3
        do { 
            let s = try db.indexDumpFirstLeaves(table: table, index: index, count: count)
            print(s) 
        } catch { 
            print("error: \(error)") 
        }
    }

    /// Asks the index to physically compact fragmented space.
    private func handleIndexCompact(_ rest: String) {
        let parts = rest.split(separator: " ")
        guard parts.count >= 2 else { 
            print("usage: \\index compact <table> <index>")
            return 
        }
        let table = String(parts[0])
        let index = String(parts[1])
        do { 
            try db.compactIndex(table: table, index: index)
            print("compaction done") 
        } catch { 
            print("error: \(error)") 
        }
    }
}
