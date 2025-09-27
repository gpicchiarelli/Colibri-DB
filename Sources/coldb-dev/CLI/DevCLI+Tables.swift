//
//  DevCLI+Tables.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Table management commands for development CLI.

import Foundation
import ColibriCore

extension DevCLI {
    
    /// Handles table-related commands (create, drop, alter)
    mutating func handleTableCommands(_ trimmed: String) {
        if trimmed.hasPrefix("\\create table ") {
            handleCreateTable(trimmed)
            return
        }
        
        if trimmed.hasPrefix("\\drop table ") {
            handleDropTable(trimmed)
            return
        }
        
        if trimmed.hasPrefix("\\alter table ") {
            handleAlterTable(trimmed)
            return
        }
    }
    
    /// Creates a new table
    private func handleCreateTable(_ trimmed: String) {
        let parts = trimmed.split(separator: " ")
        if parts.count >= 3 {
            let n = String(trimmed.dropFirst("\\create table ".count))
            do { 
                try db.createTable(n) 
                print("created \(n)") 
            } catch { 
                print("error: \(error)") 
            }
        }
    }
    
    /// Drops an existing table
    private func handleDropTable(_ trimmed: String) {
        let parts = trimmed.split(separator: " ")
        if parts.count >= 3 {
            let n = String(trimmed.dropFirst("\\drop table ".count))
            do { 
                try db.dropTable(n) 
                print("dropped \(n)") 
            } catch { 
                print("error: \(error)") 
            }
        }
    }
    
    /// Alters an existing table structure
    private func handleAlterTable(_ trimmed: String) {
        let parts = trimmed.split(separator: " ")
        if parts.count >= 4 {
            let tableName = String(parts[2])
            let operation = String(parts[3])
            
            if operation == "rename" && parts.count >= 5 {
                let newName = String(parts[4])
                do { 
                    try db.alterTable(tableName, operation: .renameTo(newName))
                    print("renamed \(tableName) to \(newName)")
                } catch { 
                    print("error: \(error)") 
                }
            } else if operation == "add" && parts.count >= 6 {
                let columnName = String(parts[4])
                let columnType = String(parts[5])
                do { 
                    try db.alterTable(tableName, operation: .addColumn(columnName, columnType))
                    print("added column \(columnName) \(columnType) to \(tableName)")
                } catch { 
                    print("error: \(error)") 
                }
            } else if operation == "drop" && parts.count >= 5 {
                let columnName = String(parts[4])
                do { 
                    try db.alterTable(tableName, operation: .dropColumn(columnName))
                    print("dropped column \(columnName) from \(tableName)")
                } catch { 
                    print("error: \(error)") 
                }
            } else {
                print("usage: \\alter table <name> rename <new_name>")
                print("       \\alter table <name> add <column> <type>")
                print("       \\alter table <name> drop <column>")
            }
        }
    }
}
