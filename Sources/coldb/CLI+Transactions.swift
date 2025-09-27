//
//  CLI+Transactions.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-27.
//
// Theme: Transaction management commands.

import Foundation
import ColibriCore

// MARK: - Transaction Commands
extension CLI {
    /// Starts a new transaction.
    mutating func handleBegin() {
        do {
            let tid = try db.begin()
            currentTID = tid
            print("Transaction started: \(tid)")
        } catch {
            print("Error starting transaction: \(error)")
        }
    }
    
    /// Commits the current transaction.
    mutating func handleCommit(_ parts: [Substring]) {
        guard let tid = currentTID else {
            print("No active transaction")
            return
        }
        
        do {
            try db.commit(tid)
            currentTID = nil
            print("Transaction committed: \(tid)")
        } catch {
            print("Error committing transaction: \(error)")
        }
    }
    
    /// Rolls back the current transaction.
    mutating func handleRollback(_ parts: [Substring]) {
        guard let tid = currentTID else {
            print("No active transaction")
            return
        }
        
        do {
            try db.rollback(toSavepoint: "", tid: tid)
            currentTID = nil
            print("Transaction rolled back: \(tid)")
        } catch {
            print("Error rolling back transaction: \(error)")
        }
    }
}