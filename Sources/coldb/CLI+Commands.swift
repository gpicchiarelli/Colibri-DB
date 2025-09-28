//
//  CLI+Commands.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-09-27.
//
// Theme: General CLI commands (help, config, tables).

import Foundation
import ColibriCore

// MARK: - General Commands
extension CLI {
    /// Displays help information for available commands.
    func help() {
        print("""
        ColibrDB CLI Commands:
        
        General:
          \\help          - Show this help
          \\conf          - Show configuration
          \\dt            - List tables
          \\exit          - Exit CLI
        
        Tables:
          \\create table <name>  - Create a table
        
        Transactions:
          \\begin         - Start transaction
          \\commit        - Commit transaction
          \\rollback      - Rollback transaction
        
        Data:
          \\insert <table> col=val,...  - Insert row
          \\scan <table>               - Scan table
          \\delete <table> col=val     - Delete rows
        
        SQL:
          \\sql <query>   - Execute SQL query
        """)
    }
    
    /// Displays current database configuration.
    func showConfig() {
        print("Configuration:")
        print("  Page size: \(db.config.pageSizeBytes) bytes")
        print("  Buffer pool: \(db.config.bufferPoolSizeBytes) bytes")
        print("  Lock timeout: \(db.config.lockTimeoutSeconds) seconds")
        print("  WAL enabled: \(db.config.walEnabled)")
        print("  Data directory: \(db.config.dataDir)")
    }
    
    /// Lists all tables in the database.
    func listTables() {
        let tables = db.listTables()
        if tables.isEmpty {
            print("No tables found.")
        } else {
            print("Tables:")
            for table in tables {
                print("  \(table)")
            }
        }
    }
}