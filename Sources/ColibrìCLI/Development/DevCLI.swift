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
        
        🚀 Debug Commands (Issue #28):
        \\debug show-locks         - Show active locks
        \\debug show-transactions  - Show active transactions
        \\debug show-buffers       - Show buffer pool stats
        \\debug stats cache        - Show cache statistics
        \\debug stats memory       - Show memory usage
        \\debug telemetry          - Show telemetry metrics
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
        
        // 🚀 FIX #28: Debug Commands
        case "\\debug show-locks":
            handleDebugShowLocks()
        
        case "\\debug show-transactions":
            handleDebugShowTransactions()
        
        case "\\debug show-buffers":
            handleDebugShowBuffers()
        
        case "\\debug stats cache":
            handleDebugStatsCache()
        
        case "\\debug stats memory":
            handleDebugStatsMemory()
        
        case "\\debug telemetry":
            handleDebugTelemetry()
            
        default:
            print("Unknown command: \(command)")
            print("Type \\help for available commands.")
        }
    }
    
    // MARK: - 🚀 FIX #28: Debug Command Handlers
    
    private func handleDebugShowLocks() {
        print("\n📊 Active Locks:")
        print("Lock manager integration not yet available")
        print("(LockManager is internal - would need public API)\n")
    }
    
    private func handleDebugShowTransactions() {
        print("\n📊 Active Transactions:")
        if let tid = currentTID {
            print("  TID \(tid) - Active")
        } else {
            print("  No active transactions in this CLI session")
        }
        print()
    }
    
    private func handleDebugShowBuffers() {
        print("\n📊 Buffer Pool Statistics:")
        print("Buffer pool stats integration not yet available")
        print("(BufferPool is internal - would need public stats API)\n")
    }
    
    private func handleDebugStatsCache() {
        print("\n📊 Cache Statistics:")
        
        // SQL Parser cache stats
        let stats = SQLParser.getCacheStats()
        print("SQL Parser Cache:")
        print("  Hits: \(stats.hits)")
        print("  Misses: \(stats.misses)")
        print("  Hit Rate: \(String(format: "%.2f%%", stats.hitRate * 100))")
        print("  Size: \(stats.size) entries")
        print()
    }
    
    private func handleDebugStatsMemory() {
        print("\n📊 Memory Usage:")
        let memory = ProcessInfo.processInfo.physicalMemory / (1024 * 1024)
        print("  System Memory: \(memory) MB")
        print("  Process Info: available via Activity Monitor")
        print()
    }
    
    private func handleDebugTelemetry() {
        print("\n📊 Telemetry Metrics:")
        print("Telemetry system available but not integrated in DevCLI yet")
        print("(Would need TelemetryManager instance)\n")
    }
    
    private func handleSQL(_ sql: String) throws {
        // Basic SQL handling - for now just print that it's not implemented
        print("SQL execution: '\(sql)'")
        print("SQL execution not yet implemented in simplified CLI.")
    }
}