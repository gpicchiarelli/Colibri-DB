//
//  CLI+Core.swift
//  ColibriCLI
//
//  Created by Codex on 2025-09-28.
//
//  Core data structures and entry plumbing for the coldb executable.

import Foundation
import ColibriCore

/// Lightweight command interpreter powering the `coldb` executable.
public struct CLI {
    public let db: Database
    public let cfgPath: String?
    public var currentTID: UInt64? = nil

    public init(db: Database, cfgPath: String?) {
        self.db = db
        self.cfgPath = cfgPath
    }

    /// Displays the CLI banner and a short usage hint.
    public func printBanner() {
        print("ColibrDB CLI (coldb) — MVP")
        print("Type \\help for help, \\exit to quit.\n")
    }
}

/// Bootstraps the CLI given process arguments.
public func runColdBCLI(arguments: [String]) throws {
    var configPath: String? = nil
    var i = 1
    while i < arguments.count {
        switch arguments[i] {
        case "--config", "-c":
            if i + 1 < arguments.count {
                configPath = arguments[i + 1]
                i += 1
            }
        default:
            break
        }
        i += 1
    }

    let cfg = try ConfigIO.load(from: configPath)
    let db = Database(config: cfg)
    try db.ensureDataDir()

    var cli = CLI(db: db, cfgPath: configPath)
    cli.printBanner()

    while let line = readLine(strippingNewline: true) {
        cli.parseAndRun(line)
    }
}
