//
//  DevCLI+Constraints.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Constraint management commands for development CLI.

import Foundation
import ColibriCore

extension DevCLI {
    
    /// Handles constraint-related commands (add, drop, list)
    mutating func handleConstraintCommands(_ trimmed: String) {
        if trimmed.hasPrefix("\\add constraint ") {
            handleAddConstraint(String(trimmed.dropFirst("\\add constraint ".count)))
            return
        }
        
        if trimmed.hasPrefix("\\drop constraint ") {
            handleDropConstraint(String(trimmed.dropFirst("\\drop constraint ".count)))
            return
        }
        
        if trimmed.hasPrefix("\\constraints ") {
            handleListConstraints(String(trimmed.dropFirst("\\constraints ".count)))
            return
        }
    }
    
    /// Handles adding constraints to tables
    private func handleAddConstraint(_ rest: String) {
        let parts = rest.split(separator: " ")
        guard parts.count >= 4 else {
            print("usage: \\add constraint <table> <type> <name> [options]")
            print("types: primary_key, unique, not_null, check, foreign_key")
            return
        }
        
        let tableName = String(parts[0])
        let constraintType = String(parts[1])
        let constraintName = String(parts[2])
        
        do {
            switch constraintType.lowercased() {
            case "primary_key":
                let columns = Array(parts.dropFirst(3)).map(String.init)
                let constraint = PrimaryKeyConstraint(name: constraintName, columns: columns)
                try db.constraintManager.addConstraint(constraint, to: tableName)
                print("added primary key constraint '\(constraintName)' to \(tableName)")
                
            case "unique":
                let columns = Array(parts.dropFirst(3)).map(String.init)
                let constraint = UniqueConstraint(name: constraintName, columns: columns)
                try db.constraintManager.addConstraint(constraint, to: tableName)
                print("added unique constraint '\(constraintName)' to \(tableName)")
                
            case "not_null":
                guard parts.count >= 4 else {
                    print("usage: \\add constraint <table> not_null <name> <column>")
                    return
                }
                let column = String(parts[3])
                let constraint = NotNullConstraint(name: constraintName, column: column)
                try db.constraintManager.addConstraint(constraint, to: tableName)
                print("added not null constraint '\(constraintName)' to \(tableName).\(column)")
                
            case "check":
                guard parts.count >= 4 else {
                    print("usage: \\add constraint <table> check <name> <expression>")
                    return
                }
                let expression = parts.dropFirst(3).joined(separator: " ")
                let constraint = CheckConstraint(name: constraintName, expression: expression)
                try db.constraintManager.addConstraint(constraint, to: tableName)
                print("added check constraint '\(constraintName)' to \(tableName)")
                
            case "foreign_key":
                guard parts.count >= 6 else {
                    print("usage: \\add constraint <table> foreign_key <name> <columns> <ref_table> <ref_columns>")
                    return
                }
                let columns = [String(parts[3])] // Simplified for MVP
                let refTable = String(parts[4])
                let refColumns = [String(parts[5])] // Simplified for MVP
                let constraint = ForeignKeyConstraint(name: constraintName, columns: columns, referencedTable: refTable, referencedColumns: refColumns)
                try db.constraintManager.addConstraint(constraint, to: tableName)
                print("added foreign key constraint '\(constraintName)' to \(tableName)")
                
            default:
                print("unknown constraint type: \(constraintType)")
                print("supported types: primary_key, unique, not_null, check, foreign_key")
            }
        } catch {
            print("error: \(error)")
        }
    }
    
    /// Handles dropping constraints from tables
    private func handleDropConstraint(_ rest: String) {
        let parts = rest.split(separator: " ")
        guard parts.count >= 2 else {
            print("usage: \\drop constraint <table> <constraint_name>")
            return
        }
        
        let tableName = String(parts[0])
        let constraintName = String(parts[1])
        
        do {
            try db.constraintManager.removeConstraint(constraintName, from: tableName)
            print("dropped constraint '\(constraintName)' from \(tableName)")
        } catch {
            print("error: \(error)")
        }
    }
    
    /// Handles listing constraints for a table
    private func handleListConstraints(_ rest: String) {
        let tableName = rest.trimmingCharacters(in: .whitespaces)
        guard !tableName.isEmpty else {
            print("usage: \\constraints <table>")
            return
        }
        
        let constraints = db.constraintManager.getConstraints(for: tableName)
        if constraints.isEmpty {
            print("no constraints found for table \(tableName)")
        } else {
            print("constraints for table \(tableName):")
            for constraint in constraints {
                print("  \(constraint.name): \(constraint.description)")
            }
        }
    }
}
