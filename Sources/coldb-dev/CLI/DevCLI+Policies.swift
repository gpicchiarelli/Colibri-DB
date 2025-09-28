//
//  DevCLI+Policies.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Policy management commands for development CLI.

import Foundation
import ColibriCore

extension DevCLI {
    
    /// Handles policy-related commands
    mutating func handlePolicyCommands(_ trimmed: String) {
        if trimmed.hasPrefix("\\policy add ") {
            handlePolicyAdd(String(trimmed.dropFirst("\\policy add ".count)))
            return
        }
        
        if trimmed == "\\policy list" { 
            handlePolicyList()
            return 
        }
        
        if trimmed.hasPrefix("\\policy remove ") { 
            handlePolicyRemove(String(trimmed.dropFirst("\\policy remove ".count)))
            return 
        }
        
        if trimmed.hasPrefix("\\optimize simulate ") {
            handleOptimizeSimulate(String(trimmed.dropFirst("\\optimize simulate ".count)))
            return
        }
    }

    /// Creates a policy object based on command arguments and registers it.
    private func handlePolicyAdd(_ rest: String) {
        // Supported: time-window, load-threshold, fragmentation
        if rest.hasPrefix("time-window ") {
            let r = String(rest.dropFirst("time-window ".count))
            let parts = r.split(separator: " ")
            guard let table = parts.first.map(String.init) else { 
                print("usage: \\policy add time-window <table> [BY col1,col2] WINDOW hh:mm-hh:mm")
                return 
            }
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
            guard let table = parts.first.map(String.init) else { 
                print("usage: \\policy add load-threshold <table> THRESHOLD qps=..,cpu=..")
                return 
            }
            let th = extractToken(after: "THRESHOLD", in: r) ?? ""
            let p = Policy(kind: .loadThreshold, table: table, columns: [], params: ["threshold": th])
            db.addPolicy(p)
            print("policy added: \(p.id.uuidString)")
            return
        }
        
        if rest.hasPrefix("fragmentation ") {
            let r = String(rest.dropFirst("fragmentation ".count))
            let parts = r.split(separator: " ")
            guard let table = parts.first.map(String.init) else { 
                print("usage: \\policy add fragmentation <table> THRESHOLD <percent>")
                return 
            }
            let th = extractToken(after: "THRESHOLD", in: r) ?? ""
            let p = Policy(kind: .fragmentation, table: table, columns: [], params: ["threshold": th])
            db.addPolicy(p)
            print("policy added: \(p.id.uuidString)")
            return
        }
        
        print("Unsupported policy kind (supported: time-window, load-threshold, fragmentation)")
    }

    /// Shows every registered maintenance policy with metadata.
    private func handlePolicyList() {
        let items = db.listPolicies()
        if items.isEmpty { 
            print("(no policies)")
            return 
        }
        for p in items {
            print("\(p.id.uuidString) \(p.kind.rawValue) table=\(p.table) cols=\(p.columns.joined(separator: ",")) params=\(p.params)")
        }
    }

    /// Removes a policy by UUID, reporting whether it existed.
    private func handlePolicyRemove(_ idStr: String) {
        guard let id = UUID(uuidString: idStr.trimmingCharacters(in: .whitespaces)) else { 
            print("invalid UUID")
            return 
        }
        print(db.removePolicy(id: id) ? "removed" : "not found")
    }

    /// Runs the optimization simulator for the given table and columns.
    private func handleOptimizeSimulate(_ rest: String) {
        let parts = rest.split(separator: " ")
        guard let table = parts.first.map(String.init) else { 
            print("usage: \\optimize simulate <table> [BY col1,col2]")
            return 
        }
        let cols = extractList(after: "BY", in: rest)
        let est = db.simulateOptimize(table: table, columns: cols)
        print(est.description)
    }
}
