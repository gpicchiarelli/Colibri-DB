//
//  DevCLI.swift
//  ColibrìDB - Development CLI
//
//  Created by Giacomo Picchiarelli on 2025-01-02.
//

import Foundation
import ColibriCore

/// Development CLI with basic functionality
class DevCLI: @unchecked Sendable {
    let db: Database
    let cfgPath: String?
    var currentTID: UInt64? = nil
    
    init(db: Database, cfgPath: String?) {
        self.db = db
        self.cfgPath = cfgPath
    }

    /// Displays the CLI banner
    func printBanner() {
        print("ColibrìDB Dev CLI (coldb-dev) — Development Version")
        print("Type \\help for help, \\exit to quit.\n")
    }

    /// Main interactive loop
    func runInteractiveLoop() {
        while true {
            print("coldb-dev> ", terminator: "")
            guard let input = readLine() else { break }
            
            let trimmed = input.trimmingCharacters(in: .whitespacesAndNewlines)
            if trimmed.isEmpty { continue }
            
            if trimmed == "\\exit" || trimmed == "\\quit" {
                print("Goodbye!")
                break
            }
            
            if trimmed == "\\help" {
                printHelp()
                continue
            }
            
            // Handle basic commands
            handleCommand(trimmed)
        }
    }
    
    private func printHelp() {
        print("""
        ColibrìDB Development CLI Commands:
        
        Basic Commands:
        \\help                 - Show this help
        \\exit, \\quit          - Exit the CLI
        \\tables               - List all tables
        \\describe <table>     - Describe table structure
        
        SQL Commands:
        SELECT * FROM <table> - Query data
        INSERT INTO ...       - Insert data
        CREATE TABLE ...      - Create table
        DROP TABLE ...        - Drop table
        
        Transaction Commands:
        \\begin               - Begin transaction
        \\commit              - Commit transaction
        \\rollback            - Rollback transaction
        """)
    }
    
    private func handleCommand(_ command: String) {
        do {
            if command.starts(with: "\\") {
                handleMetaCommand(command)
            } else {
                // Handle SQL command
                try handleSQL(command)
            }
        } catch {
            print("Error: \(error)")
        }
    }
    
    private func handleMetaCommand(_ command: String) {
        switch command {
        case "\\tables":
            let tables = db.listTables()
            if tables.isEmpty {
                print("No tables found.")
            } else {
                print("Tables:")
                for table in tables {
                    print("  - \(table)")
                }
            }
            
        case let cmd where cmd.starts(with: "\\describe "):
            let tableName = String(cmd.dropFirst("\\describe ".count))
            print("Table description for '\(tableName)' not yet implemented.")
            
        case "\\begin":
            if currentTID != nil {
                print("Transaction already active.")
            } else {
                do {
                    let tid = try db.begin()
                    currentTID = tid
                    print("Transaction \(tid) started.")
                } catch {
                    print("Error starting transaction: \(error)")
                }
            }
            
        case "\\commit":
            if let tid = currentTID {
                do {
                    try db.commit(tid)
                    currentTID = nil
                    print("Transaction committed.")
                } catch {
                    print("Error committing transaction: \(error)")
                }
            } else {
                print("No active transaction.")
            }
            
        case "\\rollback":
            if let tid = currentTID {
                do {
                    try db.rollback(tid)
                    currentTID = nil
                    print("Transaction rolled back.")
                } catch {
                    print("Error rolling back transaction: \(error)")
                }
            } else {
                print("No active transaction.")
            }
            
        default:
            print("Unknown command: \(command)")
            print("Type \\help for available commands.")
        }
    }
    
    private func handleSQL(_ sql: String) throws {
        // Basic SQL handling - for now just print that it's not implemented
        print("SQL execution: '\(sql)'")
        print("SQL execution not yet implemented in simplified CLI.")
    }
}