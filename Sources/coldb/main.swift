//
//  main.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Command-line maestro wiring CLI options to engine flows.

import Foundation
import ColibriCore

// Simple CLI parser for ColibrìDB (MVP)

/// Interactive command interpreter connecting CLI commands to the database core.
struct CLI {
    let db: Database
    let cfgPath: String?
    var currentTID: UInt64? = nil

    /// Displays the CLI banner and brief usage hint.
    func printBanner() {
        print("ColibrìDB CLI (coldb) — MVP")
        print("Type \\help for help, \\exit to quit.\n")
    }

    /// Lists every CLI command along with a short description.
    func help() {
        print("Commands:")
        print("  \\help                              Show this help")
        print("  \\conf                              Show active configuration")
        print("  \\dt                                List tables")
        print("  \\create table <name>               Create table (heap)")
        print("  \\begin                            Begin transaction")
        print("  \\commit [tid]                     Commit (current or given tid)")
        print("  \\rollback [tid]                   Rollback (current or given tid)")
        print("  \\insert <table> col=val,...        Insert a row")
        print("  \\delete <table> col=val[,col2=val2] Delete rows by equality (uses indexes)")
        print("  \\scan <table>                      Scan and print rows")
        print("  \\create index <name> ON <table>(<col>) USING <Hash|ART|BTree>")
        print("  \\indexes <table>                   List indexes on table")
        print("  \\index search <table> <index> <value>")
        print("  \\index range <table> <index> <lo> <hi>")
        print("  \\index validate <table> <index>")
        print("  \\index rebuild <table> <index>")
        print("  \\index validate-deep <table> <index>")
        print("  \\index rebuild-bulk <table> <index>")
        print("  \\index dump-header <table> <index> [pageId]")
        print("  \\index dump-leaves <table> <index> [count]")
        print("  \\index compact <table> <index>     Compact persistent index file")
        print("  \\flush all                         Flush all buffers")
        print("  \\flush table <table>               Flush table buffers")
        print("  \\flush index <table> <index>       Flush index buffers")
        print("  \\bp                                 Buffer pool stats (tables + indexes)")
        print("  \\stats                              Aggregate metrics (buffers, vacuum)")
        print("  \\table compact <table> [pageId]     Compact heap page(s)")
        print("  \\vacuum start [sec] [pages]        Start periodic vacuum")
        print("  \\vacuum stop                       Stop periodic vacuum")
        print("  \\vacuum stats                      Show vacuum stats")
        print("  \\checkpoint                        Checkpoint DB (truncate WAL)")
        print("  \\policy add time-window <table> [BY col1,col2] WINDOW hh:mm-hh:mm")
        print("  \\policy add load-threshold <table> THRESHOLD qps=100,cpu=20%")
        print("  \\policy add fragmentation <table> THRESHOLD 30%")
        print("  \\policy list                        List policies")
        print("  \\policy remove <uuid>               Remove policy by id")
        print("  \\optimize simulate <table> [BY col1,col2]")
        print("  \\import <file.csv> INTO <table>     Import CSV (header row, simple CSV)")
        print("  \\export <table> TO <file.csv>       Export table to CSV")
        print("  \\stats prometheus                   Print Prometheus metrics")
        print("  \\exit                              Quit")
    }

    /// Prints the active configuration values and source file.
    func showConfig() {
        let cfg = db.config
        print("Configuration: dataDir=\(cfg.dataDir) logical=\(cfg.maxConnectionsLogical) physical=\(cfg.maxConnectionsPhysical) page=\(cfg.pageSizeBytes) index=\(cfg.indexImplementation) wal=\(cfg.walEnabled) checksum=\(cfg.checksumEnabled)")
        if let path = cfgPath { print("Loaded from: \(path)") }
    }

    /// Outputs all registered tables in the catalog.
    func listTables() {
        let ts = db.listTables()
        if ts.isEmpty { print("(no tables)") } else { ts.forEach { print($0) } }
    }

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
            do { let tid = try db.begin(); currentTID = tid; print("TID=\(tid)"); } catch { print("error: \(error)") }
            return
        }
        if trimmed.hasPrefix("\\commit") {
            let parts = trimmed.split(separator: " ")
            var tid: UInt64? = nil
            if parts.count >= 2 { tid = UInt64(parts[1]) }
            if tid == nil { tid = currentTID }
            guard let t = tid else { print("no active TID"); return }
            do { try db.commit(t); print("committed \(t)") } catch { print("error: \(error)") }
            if currentTID == t { currentTID = nil }
            return
        }
        if trimmed.hasPrefix("\\rollback") {
            let parts = trimmed.split(separator: " ")
            var tid: UInt64? = nil
            if parts.count >= 2 { tid = UInt64(parts[1]) }
            if tid == nil { tid = currentTID }
            guard let t = tid else { print("no active TID"); return }
            do { try db.rollback(t); print("aborted \(t)") } catch { print("error: \(error)") }
            if currentTID == t { currentTID = nil }
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
        if trimmed == "\\checkpoint" {
            do { try db.checkpoint(); print("checkpoint done") } catch { print("error: \(error)") }
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
        if trimmed.hasPrefix("\\fault set ") {
            handleFaultSet(String(trimmed.dropFirst("\\fault set ".count)))
            return
        }
        if trimmed == "\\fault clear" {
            FaultInjector.shared.clear(); print("faults cleared"); return
        }
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
        if trimmed.hasPrefix("\\flush all") {
            let tokens = trimmed.split(whereSeparator: { $0.isWhitespace })
            let fullSync = tokens.contains { $0.lowercased() == "fullsync" }
            db.flushAll(fullSync: fullSync)
            print(fullSync ? "flushed (fullsync)" : "flushed")
            return
        }
        if trimmed.hasPrefix("\\flush table ") {
            let tokens = trimmed.split(whereSeparator: { $0.isWhitespace })
            guard tokens.count >= 3 else { print("usage: \\flush table <table> [fullsync]"); return }
            let table = String(tokens[2])
            let fullSync = tokens.dropFirst(3).contains { $0.lowercased() == "fullsync" }
            do {
                try db.flushTable(table, fullSync: fullSync)
                print(fullSync ? "flushed table (fullsync)" : "flushed table")
            } catch { print("error: \(error)") }
            return
        }
        if trimmed.hasPrefix("\\flush index ") {
            let tokens = trimmed.split(whereSeparator: { $0.isWhitespace })
            guard tokens.count >= 4 else { print("usage: \\flush index <table> <index> [fullsync]"); return }
            let table = String(tokens[2])
            let index = String(tokens[3])
            let fullSync = tokens.dropFirst(4).contains { $0.lowercased() == "fullsync" }
            do {
                try db.flushIndex(table, index, fullSync: fullSync)
                print(fullSync ? "flushed index (fullsync)" : "flushed index")
            } catch { print("error: \(error)") }
            return
        }
        if trimmed == "\\bp" {
            for line in db.bufferPoolStats() { print(line) }
            return
        }
        if trimmed == "\\stats" {
            print(db.bufferPoolAggregateStats())
            print(db.vacuumStats())
            return
        }
        if trimmed.hasPrefix("\\table compact ") {
            handleTableCompact(String(trimmed.dropFirst("\\table compact ".count)))
            return
        }
        if trimmed.hasPrefix("\\vacuum start") {
            let parts = trimmed.split(separator: " ")
            let sec = parts.count >= 3 ? (Double(parts[2]) ?? 5.0) : 5.0
            let pages = parts.count >= 4 ? (Int(parts[3]) ?? 32) : 32
            db.startVacuum(intervalSeconds: sec, pagesPerRun: pages)
            print("vacuum started")
            return
        }
        if trimmed == "\\vacuum stop" { db.stopVacuum(); print("vacuum stopped"); return }
        if trimmed == "\\vacuum stats" { print(db.vacuumStats()); return }

        if trimmed.hasPrefix("\\policy add ") {
            handlePolicyAdd(String(trimmed.dropFirst("\\policy add ".count)))
            return
        }
        if trimmed == "\\policy list" { handlePolicyList(); return }
        if trimmed.hasPrefix("\\policy remove ") { handlePolicyRemove(String(trimmed.dropFirst("\\policy remove ".count))); return }

        if trimmed.hasPrefix("\\optimize simulate ") {
            handleOptimizeSimulate(String(trimmed.dropFirst("\\optimize simulate ".count)))
            return
        }

        if trimmed.hasPrefix("\\import ") || trimmed.hasPrefix("\\export ") {
            print("Not implemented in MVP (import/export)")
            return
        }

        print("Unrecognized command. Type \\help.")
    }

    /// Creates a policy object based on command arguments and registers it.
    private func handlePolicyAdd(_ rest: String) {
        // Supported: time-window, load-threshold, fragmentation
        if rest.hasPrefix("time-window ") {
            let r = String(rest.dropFirst("time-window ".count))
            let parts = r.split(separator: " ")
            guard let table = parts.first.map(String.init) else { print("usage: \\policy add time-window <table> [BY col1,col2] WINDOW hh:mm-hh:mm"); return }
            let cols = extractList(after: "BY", in: r)
            let window = extractToken(after: "WINDOW", in: r) ?? ""
            let p = Policy(kind: .timeWindow, table: table, columns: cols, params: ["window": window])
            db.addPolicy(p)
            print("policy added: \(p.id.uuidString)")
            return
        }
        if rest.hasPrefix("load-threshold ") {
            let r = String(rest.dropFirst("load-threshold ".count))
            let parts = r.split(separator: " ")
            guard let table = parts.first.map(String.init) else { print("usage: \\policy add load-threshold <table> THRESHOLD qps=..,cpu=..") ; return }
            let th = extractToken(after: "THRESHOLD", in: r) ?? ""
            let p = Policy(kind: .loadThreshold, table: table, columns: [], params: ["threshold": th])
            db.addPolicy(p)
            print("policy added: \(p.id.uuidString)")
            return
        }
        if rest.hasPrefix("fragmentation ") {
            let r = String(rest.dropFirst("fragmentation ".count))
            let parts = r.split(separator: " ")
            guard let table = parts.first.map(String.init) else { print("usage: \\policy add fragmentation <table> THRESHOLD <percent>"); return }
            let th = extractToken(after: "THRESHOLD", in: r) ?? ""
            let p = Policy(kind: .fragmentation, table: table, columns: [], params: ["threshold": th])
            db.addPolicy(p)
            print("policy added: \(p.id.uuidString)")
            return
        }
        print("Unsupported policy kind (supported: time-window, load-threshold, fragmentation)")
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

    /// Parses arguments and creates an index using the chosen backend.
    private func handleCreateIndex(_ rest: String) {
        // format: <name> ON <table>(<col>) USING <kind>
        // Simple parse
        let parts = rest.split(separator: " ")
        guard parts.count >= 4 else { print("usage: \\create index <name> ON <table>(<col>) USING <Hash|ART>"); return }
        let name = String(parts[0])
        guard let onIdx = parts.firstIndex(where: { $0.uppercased() == "ON" }) else { print("missing ON"); return }
        let tableAndCol = parts[parts.index(after: onIdx)]
        guard let l = tableAndCol.firstIndex(of: "("), let r = tableAndCol.firstIndex(of: ")") else { print("table(col) malformed"); return }
        let table = String(tableAndCol[..<l])
        let colsRaw = String(tableAndCol[tableAndCol.index(after: l)..<r])
        let cols = colsRaw.split(separator: ",").map { $0.trimmingCharacters(in: .whitespaces) }
        guard let usingIdx = parts.firstIndex(where: { $0.uppercased() == "USING" }), parts.index(after: usingIdx) < parts.endIndex else { print("missing USING kind"); return }
        let kind = String(parts[parts.index(after: usingIdx)])
        do { try db.createIndex(name: name, on: table, columns: cols, using: kind); print("index created") } catch { print("error: \(error)") }
    }

    /// Lists index names associated with a table.
    private func handleListIndexes(_ rest: String) {
        let table = rest.trimmingCharacters(in: .whitespaces)
        let names = db.listIndexes(table: table)
        if names.isEmpty { print("(no indexes)") } else { names.forEach { print($0) } }
    }

    /// Runs an equality probe against a specific index.
    private func handleIndexSearch(_ rest: String) {
        let parts = rest.split(separator: " ")
        guard parts.count >= 3 else { print("usage: \\index search <table> <index> <value>"); return }
        let table = String(parts[0])
        let index = String(parts[1])
        let raw = String(parts[2])
        if raw.contains(",") {
            let vs = raw.split(separator: ",").map { parseValue(String($0)) }
            do { let r = try db.indexSearchEqualsValues(table: table, index: index, values: vs); r.forEach { print($0) }; if r.isEmpty { print("(none)") } } catch { print("error: \(error)") }
        } else {
            let v = parseValue(raw)
            do { let r = try db.indexSearchEqualsTyped(table: table, index: index, value: v); r.forEach { print($0) }; if r.isEmpty { print("(none)") } } catch { print("error: \(error)") }
        }
    }

    /// Executes a range lookup on the selected index.
    private func handleIndexRange(_ rest: String) {
        let parts = rest.split(separator: " ")
        guard parts.count >= 4 else { print("usage: \\index range <table> <index> <lo> <hi>"); return }
        let table = String(parts[0])
        let index = String(parts[1])
        let loRaw = String(parts[2])
        let hiRaw = String(parts[3])
        if loRaw.contains(",") || hiRaw.contains(",") {
            let loVals = loRaw.isEmpty ? nil : loRaw.split(separator: ",").map { parseValue(String($0)) }
            let hiVals = hiRaw.isEmpty ? nil : hiRaw.split(separator: ",").map { parseValue(String($0)) }
            do { let r = try db.indexRangeValues(table: table, index: index, lo: loVals, hi: hiVals); r.forEach { print($0) }; if r.isEmpty { print("(none)") } } catch { print("error: \(error)") }
        } else {
            let loV = parseValue(loRaw)
            let hiV = parseValue(hiRaw)
            do { let r = try db.indexRangeTyped(table: table, index: index, lo: loV, hi: hiV); r.forEach { print($0) }; if r.isEmpty { print("(none)") } } catch { print("error: \(error)") }
        }
    }

    /// Runs lightweight validation and reports coverage stats.
    private func handleIndexValidate(_ rest: String) {
        let parts = rest.split(separator: " ")
        guard parts.count >= 2 else { print("usage: \\index validate <table> <index>"); return }
        let table = String(parts[0])
        let index = String(parts[1])
        do { let r = try db.validateIndex(table: table, index: index); print("total=\(r.total) indexed=\(r.indexed) missing=\(r.missing)") } catch { print("error: \(error)") }
    }

    /// Triggers a full logical rebuild of an index.
    private func handleIndexRebuild(_ rest: String) {
        let parts = rest.split(separator: " ")
        guard parts.count >= 2 else { print("usage: \\index rebuild <table> <index>"); return }
        let table = String(parts[0])
        let index = String(parts[1])
        do { try db.rebuildIndex(table: table, index: index); print("rebuild done") } catch { print("error: \(error)") }
    }

    /// Performs deep validation and prints structural diagnostics.
    private func handleIndexValidateDeep(_ rest: String) {
        let parts = rest.split(separator: " ")
        guard parts.count >= 2 else { print("usage: \\index validate-deep <table> <index>"); return }
        let table = String(parts[0])
        let index = String(parts[1])
        do { let report = try db.validateIndexDeep(table: table, index: index); print(report) } catch { print("error: \(error)") }
    }

    /// Rebuilds an index using the bulk-loading routine.
    private func handleIndexRebuildBulk(_ rest: String) {
        let parts = rest.split(separator: " ")
        guard parts.count >= 2 else { print("usage: \\index rebuild-bulk <table> <index>"); return }
        let table = String(parts[0])
        let index = String(parts[1])
        do { try db.rebuildIndexBulk(table: table, index: index); print("bulk rebuild done") } catch { print("error: \(error)") }
    }

    /// Prints internal header information for the specified index page.
    private func handleIndexDumpHeader(_ rest: String) {
        // format: <table> <index> [pageId]
        let parts = rest.split(separator: " ")
        guard parts.count >= 2 else { print("usage: \\index dump-header <table> <index> [pageId]"); return }
        let table = String(parts[0])
        let index = String(parts[1])
        let pid: UInt64? = parts.count >= 3 ? UInt64(parts[2]) : nil
        do { let s = try db.indexDumpHeader(table: table, index: index, pageId: pid); print(s) } catch { print("error: \(error)") }
    }

    /// Prints a sample of leaf pages to aid diagnostics.
    private func handleIndexDumpLeaves(_ rest: String) {
        // format: <table> <index> [count]
        let parts = rest.split(separator: " ")
        guard parts.count >= 2 else { print("usage: \\index dump-leaves <table> <index> [count]"); return }
        let table = String(parts[0])
        let index = String(parts[1])
        let count = parts.count >= 3 ? (Int(parts[2]) ?? 3) : 3
        do { let s = try db.indexDumpFirstLeaves(table: table, index: index, count: count); print(s) } catch { print("error: \(error)") }
    }

    /// Invokes heap compaction optionally targeting a single page.
    private func handleTableCompact(_ rest: String) {
        let parts = rest.split(separator: " ")
        guard parts.count >= 1 else { print("usage: \\table compact <table> [pageId]"); return }
        let table = String(parts[0])
        let pid = parts.count >= 2 ? UInt64(parts[1]) : nil
        do { let s = try db.compactTable(table: table, pageId: pid); print(s) } catch { print("error: \(error)") }
    }

    /// Asks the index to physically compact fragmented space.
    private func handleIndexCompact(_ rest: String) {
        let parts = rest.split(separator: " ")
        guard parts.count >= 2 else { print("usage: \\index compact <table> <index>"); return }
        let table = String(parts[0])
        let index = String(parts[1])
        do { try db.compactIndex(table: table, index: index); print("compaction done") } catch { print("error: \(error)") }
    }

    /// Arms the fault injector to trigger after a configurable countdown.
    private func handleFaultSet(_ rest: String) {
        // format: <key> <n>
        let parts = rest.split(separator: " ")
        guard parts.count >= 2, let n = Int(parts[1]) else { print("usage: \\fault set <key> <n>"); return }
        FaultInjector.shared.set(key: String(parts[0]), remaining: n)
        print("fault set for \(parts[0]) = \(n)")
    }

    /// Loads CSV rows into a table using the first row as the header.
    private func handleImport(_ rest: String) {
        // format: <file.csv> INTO <table>
        let parts = rest.split(separator: " ")
        guard let intoIdx = parts.firstIndex(where: { $0.uppercased() == "INTO" }) else { print("usage: \\import <file.csv> INTO <table>"); return }
        let file = parts.prefix(upTo: intoIdx).joined(separator: " ")
        let table = parts.suffix(from: parts.index(after: intoIdx)).joined(separator: " ")
        guard !file.isEmpty, !table.isEmpty else { print("usage: \\import <file.csv> INTO <table>"); return }
        let path = String(file)
        let tname = String(table)
        do {
            let data = try String(contentsOfFile: path, encoding: .utf8)
            let lines = data.components(separatedBy: .newlines)
            guard let headerLine = lines.first(where: { !$0.trimmingCharacters(in: .whitespaces).isEmpty }) else { print("empty file"); return }
            let headers = headerLine.split(separator: ",").map { String($0).trimmingCharacters(in: .whitespaces) }
            guard !headers.isEmpty else { print("missing CSV header"); return }
            var imported = 0
            var started = false
            for line in lines {
                // skip lines until (and including) header
                if !started { if line == headerLine { started = true }; continue }
                if line.trimmingCharacters(in: .whitespaces).isEmpty { continue }
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
        guard let toIdx = parts.firstIndex(where: { $0.uppercased() == "TO" }) else { print("usage: \\export <table> TO <file.csv>"); return }
        let table = parts.prefix(upTo: toIdx).joined(separator: " ")
        let file = parts.suffix(from: parts.index(after: toIdx)).joined(separator: " ")
        guard !file.isEmpty, !table.isEmpty else { print("usage: \\export <table> TO <file.csv>"); return }
        do {
            let tname = String(table)
            let items = try db.scan(tname)
            // Collect column set
            var colsSet = Set<String>()
            for (_, row) in items { for (k, _) in row { colsSet.insert(k) } }
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

    /// Shows every registered maintenance policy with metadata.
    private func handlePolicyList() {
        let items = db.listPolicies()
        if items.isEmpty { print("(no policies)"); return }
        for p in items {
            print("\(p.id.uuidString) \(p.kind.rawValue) table=\(p.table) cols=\(p.columns.joined(separator: ",")) params=\(p.params)")
        }
    }

    /// Removes a policy by UUID, reporting whether it existed.
    private func handlePolicyRemove(_ idStr: String) {
        guard let id = UUID(uuidString: idStr.trimmingCharacters(in: .whitespaces)) else { print("invalid UUID"); return }
        print(db.removePolicy(id: id) ? "removed" : "not found")
    }

    /// Runs the optimization simulator for the given table and columns.
    private func handleOptimizeSimulate(_ rest: String) {
        let parts = rest.split(separator: " ")
        guard let table = parts.first.map(String.init) else { print("usage: \\optimize simulate <table> [BY col1,col2]"); return }
        let cols = extractList(after: "BY", in: rest)
        let est = db.simulateOptimize(table: table, columns: cols)
        print(est.description)
    }

    /// Extracts a comma-separated token list following a keyword.
    private func extractList(after keyword: String, in text: String) -> [String] {
        guard let token = extractToken(after: keyword, in: text) else { return [] }
        return token.split(separator: ",").map { String($0) }
    }

    /// Returns the raw token immediately following the given keyword.
    private func extractToken(after keyword: String, in text: String) -> String? {
        let tokens = text.split(separator: " ")
        guard let idx = tokens.firstIndex(where: { $0.uppercased() == keyword.uppercased() }) else { return nil }
        let nextIdx = tokens.index(after: idx)
        guard nextIdx < tokens.endIndex else { return nil }
        return String(tokens[nextIdx])
    }
}

// Entry point
var configPath: String? = nil
var i = 1
let args = CommandLine.arguments
while i < args.count {
    switch args[i] {
    case "--config", "-c":
        if i + 1 < args.count { configPath = args[i+1]; i += 1 }
    default:
        break
    }
    i += 1
}

do {
    let cfg = try ConfigIO.load(from: configPath)
    let db = Database(config: cfg)
    try db.ensureDataDir()
    var cli = CLI(db: db, cfgPath: configPath)
    cli.printBanner()
    while let line = readLine(strippingNewline: true) {
        cli.parseAndRun(line)
    }
} catch {
    fputs("fatal: \(error)\n", stderr)
    exit(1)
}

