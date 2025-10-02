//
//  DevCLI+Tables.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrDB — BSD 3-Clause License
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
            let _ = String(trimmed.dropFirst("\\drop table ".count))
            // TODO: Implement dropTable method in Database class
            print("error: dropTable not yet implemented")
        }
    }
    
    /// Alters an existing table structure
    private func handleAlterTable(_ trimmed: String) {
        let parts = trimmed.split(separator: " ")
        if parts.count >= 4 {
            let _ = String(parts[2])
            let _ = String(parts[3])
            
            // TODO: Implement alterTable method in Database class
            print("error: alterTable not yet implemented")
            print("usage: \\alter table <name> rename <new_name>")
            print("       \\alter table <name> add <column> <type>")
            print("       \\alter table <name> drop <column>")
        }
    }
}
