//
//  CLI+Commands.swift
//  ColibrìDB - CLI Commands Extension
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//

import Foundation
import ColibriCore

// MARK: - CLI Commands Extension

extension ProductionCLI {
    
    func handleMetaCommand(_ command: String) throws {
        let parts = command.components(separatedBy: .whitespaces).filter { !$0.isEmpty }
        guard let cmd = parts.first else { return }
        
        switch cmd.lowercased() {
        case "\\help", "\\h", "\\?":
            formatter.printHelp()
            
        case "\\quit", "\\q", "\\exit":
            isRunning = false
            
        case "\\version", "\\v":
            formatter.printVersion()
            
        case "\\status", "\\s":
            formatter.printStatus(database: database)
            
        case "\\dt":
            try handleListTables()
            
        case "\\di":
            try handleListIndexes()
            
        case "\\d":
            if parts.count > 1 {
                try handleDescribeTable(parts[1])
            } else {
                formatter.printError("Usage: \\d <table_name>")
            }
            
        case "\\timing":
            formatter.toggleTiming()
            
        case "\\echo":
            if parts.count > 1 {
                formatter.printInfo(parts.dropFirst().joined(separator: " "))
            }
            
        default:
            formatter.printError("Unknown command: \(cmd)")
            formatter.printInfo("Type \\help for available commands")
        }
    }
    
    func handleSQLQuery(_ sql: String) throws {
        let startTime = Date()
        
        do {
            let parser = SimpleSQLParser(sql: sql)
            let statement = try parser.parse()
            
            let executor = SimpleSQLExecutor(database: database)
            let result = try executor.execute(statement)
            
            let executionTime = Date().timeIntervalSince(startTime)
            formatter.printQueryResult(result, executionTime: executionTime)
            
        } catch {
            let executionTime = Date().timeIntervalSince(startTime)
            formatter.printError("SQL Error: \(error.localizedDescription)")
            formatter.printTiming(executionTime)
        }
    }
    
    private func handleListTables() throws {
        let tables = database.listTables()
        formatter.printTableList(tables)
    }
    
    private func handleListIndexes() throws {
        let tables = database.listTables()
        for table in tables {
            let indexes = database.listIndexes(table: table)
            if !indexes.isEmpty {
                formatter.printIndexList(table: table, indexes: indexes)
            }
        }
    }
    
    private func handleDescribeTable(_ tableName: String) throws {
        // For now, just list table existence
        let tables = database.listTables()
        if tables.contains(tableName) {
            formatter.printInfo("Table '\(tableName)' exists")
            // TODO: Implement table schema display
        } else {
            formatter.printError("Table '\(tableName)' not found")
        }
    }
}
