//
//  CLI+SQL.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-27.
//
// Theme: SQL command integration for the CLI.

import Foundation
import ColibriCore

// MARK: - SQL Commands
extension CLI {
    /// Execute SQL query
    func executeSQL(_ query: String) {
        do {
            let sqlInterface = SQLQueryInterface(database: db)
            let result = try sqlInterface.execute(query)
            printSQLResult(result)
        } catch {
            print("SQL Error: \(error.localizedDescription)")
        }
    }
    
    /// Print SQL query result
    func printSQLResult(_ result: SQLQueryResult) {
        print("Query executed successfully")
        print("Statement: \(result.statementType.rawValue)")
        print("Affected rows: \(result.affectedRows)")
        print("Message: \(result.message)")
        
        if !result.columns.isEmpty {
            print("\nResult:")
            print("Columns: \(result.columns.joined(separator: " | "))")
            print(String(repeating: "-", count: result.columns.joined(separator: " | ").count))
            
            for row in result.rows {
                let values = row.map { value in
                    switch value {
                    case .null: return "NULL"
                    case .int(let v): return String(v)
                    case .double(let v): return String(v)
                    case .string(let v): return "'\(v)'"
                    case .bool(let v): return v ? "TRUE" : "FALSE"
                    case .data(let v): return "<\(v.count) bytes>"
                    case .array(let v): return "[\(v.count) items]"
                    }
                }
                print(values.joined(separator: " | "))
            }
        }
        print()
    }
}
