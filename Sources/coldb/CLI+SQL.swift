//
//  CLI+SQL.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-27.
//
// Theme: SQL query execution commands.

import Foundation
import ColibriCore

// MARK: - SQL Commands
extension CLI {
    /// Executes a SQL query and displays the results.
    func executeSQL(_ query: String) {
        do {
            let interface = SQLQueryInterface(database: db)
            let result = try interface.execute(query)
            printSQLResult(result)
        } catch {
            print("SQL Error: \(error)")
        }
    }
    
    /// Prints SQL query results in a formatted way.
    private func printSQLResult(_ result: SQLQueryResult) {
        if !result.message.isEmpty {
            print(result.message)
        }
        
        if !result.columns.isEmpty {
            print("Columns: \(result.columns.joined(separator: ", "))")
        }
        
        if !result.rows.isEmpty {
            print("Rows (\(result.rows.count)):")
            for (index, row) in result.rows.enumerated() {
                let values = row.map { "\($0)" }.joined(separator: ", ")
                print("  \(index + 1): \(values)")
            }
        } else if result.affectedRows > 0 {
            print("Affected rows: \(result.affectedRows)")
        }
    }
}