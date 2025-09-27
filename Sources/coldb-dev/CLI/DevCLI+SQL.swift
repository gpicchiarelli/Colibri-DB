//
//  DevCLI+SQL.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-26.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: SQL command extensions for DevCLI.

import Foundation
import ColibriCore

extension DevCLI {
    
    /// Handles SQL commands
    func handleSQLCommands(_ command: String) -> Bool {
        let parts = command.components(separatedBy: .whitespacesAndNewlines).filter { !$0.isEmpty }
        guard !parts.isEmpty else { return false }
        
        switch parts[0] {
        case "\\sql":
            return handleSQLCommand(Array(parts.dropFirst()))
        default:
            return false
        }
    }
    
    /// Handles SQL command execution
    private func handleSQLCommand(_ args: [String]) -> Bool {
        guard !args.isEmpty else {
            print("Usage: \\sql <SQL statement>")
            return true
        }
        
        let sql = args.joined(separator: " ")
        
        do {
            let parser = SimpleSQLParser(sql: sql)
            let statement = try parser.parse()
            
            let executor = SQLExecutor(database: db)
            try executor.execute(statement)
            
            print("SQL executed successfully")
        } catch {
            print("SQL Error: \(error)")
        }
        
        return true
    }
}
