//
//  CLIFormatter+Display.swift
//  ColibrDB - CLI Display Extension
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//

import Foundation
import ColibriCore

// MARK: - CLIFormatter Display Extension

extension CLIFormatter {
    
    func printTableList(_ tables: [String]) {
        if tables.isEmpty {
            print(colors.info("No tables found"))
            return
        }
        
        print(colors.header("📋 Tables:"))
        print(colors.border("┌─────────────────────────────────────┐"))
        print(colors.border("│ ") + colors.tableHeader("Table Name") + String(repeating: " ", count: 25) + colors.border(" │"))
        print(colors.border("├─────────────────────────────────────┤"))
        
        for table in tables {
            let padding = max(0, 35 - table.count)
            print(colors.border("│ ") + colors.tableName(table) + String(repeating: " ", count: padding) + colors.border(" │"))
        }
        
        print(colors.border("└─────────────────────────────────────┘"))
        print(colors.info("(\(tables.count) table\(tables.count == 1 ? "" : "s"))"))
        print()
    }
    
    func printIndexList(table: String, indexes: [String]) {
        print(colors.header("🔍 Indexes on '\(table)':"))
        for index in indexes {
            print("  • \(index)")
        }
        print()
    }
    
    // TODO: Implement table schema display when ConstraintManager is ready
}
