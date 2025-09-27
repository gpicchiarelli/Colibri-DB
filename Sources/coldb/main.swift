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

