//
//  DevCLI.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Development CLI core structure and command routing.

import Foundation
import ColibriCore
import os.log

/// Development CLI interpreter connecting CLI commands to the database core.
/// This is the development version with additional debugging and testing capabilities.
struct DevCLI {
    let db: Database
    let cfgPath: String?
    var currentTID: UInt64? = nil

    /// Displays the CLI banner and brief usage hint.
    func printBanner() {
        print("ColibrìDB Dev CLI (coldb-dev) — Development Version")
        print("Type \\help for help, \\exit to quit.\n")
    }

    /// Lists every CLI command along with a short description.
    func help() {
        print("Commands:")
        print("  \\help                              Show this help")
        print("  \\conf                              Show active configuration")
        print("  \\dt                                List tables")
        print("  \\create table <name>               Create table (heap)")
        print("  \\drop table <name>                 Drop table")
        print("  \\alter table <name> <op> <args>    Alter table structure")
        print("  \\begin                            Begin transaction")
        print("  \\commit [tid]                     Commit (current or given tid)")
        print("  \\rollback [tid]                   Rollback (current or given tid)")
        print("  \\insert <table> col=val,...        Insert a row")
        print("  \\delete <table> col=val[,col2=val2] Delete rows by equality (uses indexes)")
        print("  \\scan <table>                      Scan and print rows")
        print("  \\sql <statement>                   Execute SQL statement")
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
        print("  \\add constraint <table> <type> <name> [options]")
        print("  \\drop constraint <table> <name>")
        print("  \\constraints <table>")
        print("  \\fault set <key> <n>               Set fault injection")
        print("  \\fault clear                       Clear fault injection")
        print("  \\debug memory [monitor]            Debug memory usage")
        print("  \\debug performance                 Debug performance metrics")
        print("  \\debug constraints                 Debug constraint validation")
        print("  \\debug sql <query>                 Debug SQL parsing/execution")
        print("  \\debug types                       Debug type system")
        print("  \\debug profile <operation> <cmd>   Debug profiling")
        print("  \\monitor stats [interval=1.0]      Monitor real-time statistics")
        print("  \\monitor memory [continuous]       Monitor memory usage")
        print("  \\monitor performance               Monitor performance metrics")
        print("  \\monitor constraints               Monitor constraint validation")
        print("  \\profile start                     Start CPU profiling")
        print("  \\profile stop                      Stop CPU profiling")
        print("  \\profile memory <operation>        Profile memory operations")
        print("  \\profile sql <query>               Profile SQL operations")
        print("  \\profile constraints               Profile constraint operations")
        print("  \\test run                          Run all tests")
        print("  \\test unit                         Run unit tests")
        print("  \\test integration                  Run integration tests")
        print("  \\test performance                  Run performance tests")
        print("  \\test stress                       Run stress tests")
        print("  \\test auto [interval=300]          Run automated tests")
        print("  \\test regression                   Run regression tests")
        print("  \\test memory                       Run memory leak tests")
        print("  \\benchmark sql [iterations=1000]   Benchmark SQL operations")
        print("  \\benchmark constraints [iterations=1000] Benchmark constraints")
        print("  \\benchmark types [iterations=10000] Benchmark data types")
        print("  \\benchmark memory [iterations=100] Benchmark memory allocation")
        print("  \\benchmark suite                   Run comprehensive benchmark suite")
        print("  \\benchmark custom <name> <iterations> <operation> Run custom benchmark")
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
        
        // Basic commands
        if trimmed == "\\help" { help(); return }
        if trimmed == "\\conf" { showConfig(); return }
        if trimmed == "\\dt" { listTables(); return }
        if trimmed == "\\exit" { exit(0) }

        // Route to specialized command handlers
        if trimmed.hasPrefix("\\create table ") || trimmed.hasPrefix("\\drop table ") || trimmed.hasPrefix("\\alter table ") {
            handleTableCommands(trimmed)
            return
        }
        
        if trimmed.hasPrefix("\\add constraint ") || trimmed.hasPrefix("\\drop constraint ") || trimmed.hasPrefix("\\constraints ") {
            handleConstraintCommands(trimmed)
            return
        }
        
        if trimmed.hasPrefix("\\begin") || trimmed.hasPrefix("\\commit") || trimmed.hasPrefix("\\rollback") {
            handleTransactionCommands(trimmed)
            return
        }
        
        if trimmed.hasPrefix("\\insert ") || trimmed.hasPrefix("\\scan ") || trimmed.hasPrefix("\\delete ") {
            handleDataCommands(trimmed)
            return
        }
        
        if trimmed.hasPrefix("\\create index ") || trimmed.hasPrefix("\\indexes ") || trimmed.hasPrefix("\\index ") {
            handleIndexCommands(trimmed)
            return
        }
        
        if trimmed.hasPrefix("\\flush ") || trimmed.hasPrefix("\\bp") || trimmed.hasPrefix("\\stats") || 
           trimmed.hasPrefix("\\table compact ") || trimmed.hasPrefix("\\vacuum ") || trimmed == "\\checkpoint" {
            handleMaintenanceCommands(trimmed)
            return
        }
        
        if trimmed.hasPrefix("\\policy ") || trimmed.hasPrefix("\\optimize ") {
            handlePolicyCommands(trimmed)
            return
        }
        
        if trimmed.hasPrefix("\\import ") || trimmed.hasPrefix("\\export ") {
            handleImportExportCommands(trimmed)
            return
        }
        
        if trimmed.hasPrefix("\\fault ") {
            handleFaultCommands(trimmed)
            return
        }
        
        if trimmed.hasPrefix("\\sql ") {
            handleSQLCommands(trimmed)
            return
        }
        
        if trimmed == "\\stats prometheus" {
            printPrometheus()
            return
        }
        
        if trimmed.hasPrefix("\\debug ") {
            handleDebugCommands(trimmed)
            return
        }
        
        if trimmed.hasPrefix("\\monitor ") || trimmed.hasPrefix("\\profile ") {
            handleMonitoringCommands(trimmed)
            return
        }
        
        if trimmed.hasPrefix("\\test ") {
            handleTestingCommands(trimmed)
            return
        }
        
        if trimmed.hasPrefix("\\benchmark ") {
            handleBenchmarkCommands(trimmed)
            return
        }

        // SQL query execution
        if !trimmed.hasPrefix("\\") {
            handleSQLQuery(trimmed)
            return
        }

        print("Unrecognized command. Type \\help.")
    }
    
    /// Handles SQL query execution
    private func handleSQLQuery(_ sql: String) {
        do {
            let parser = SimpleSQLParser(sql: sql)
            let statement = try parser.parse()
            
            let executor = SimpleSQLExecutor(database: db)
            let result = try executor.execute(statement)
            print(result)
        } catch {
            print("SQL Error: \(error.localizedDescription)")
        }
    }
    
    /// Formats a value for display
    private func formatValue(_ value: Value) -> String {
        switch value {
        case .string(let s): return s
        case .int(let i): return String(i)
        case .double(let d): return String(d)
        case .bool(let b): return b ? "true" : "false"
        case .null: return "NULL"
        case .date(let d): return ISO8601DateFormatter().string(from: d)
        case .decimal(let d): return d.description
        case .blob(let d): return "<BLOB:\(d.count) bytes>"
        case .json(let d): return String(data: d, encoding: .utf8) ?? "<INVALID JSON>"
        case .enumValue(let enumName, let value): return "\(enumName).\(value)"
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
}
