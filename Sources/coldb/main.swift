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
    init(db: Database, cfgPath: String?) {
        self.db = db
        self.cfgPath = cfgPath
    }

    /// Displays the CLI banner and brief usage hint.
    func printBanner() {
        print("ColibrìDB CLI (coldb) — MVP")
        print("Type \\help for help, \\exit to quit.\n")
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

        print("Unrecognized command. Type \\help.")
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

