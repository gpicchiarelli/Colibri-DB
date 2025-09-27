//
//  DevCLI+Transactions.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Transaction management commands for development CLI.

import Foundation
import ColibriCore

extension DevCLI {
    
    /// Handles transaction-related commands (begin, commit, rollback)
    mutating func handleTransactionCommands(_ trimmed: String) {
        if trimmed.hasPrefix("\\begin") {
            handleBeginTransaction()
            return
        }
        
        if trimmed.hasPrefix("\\commit") {
            handleCommitTransaction(trimmed)
            return
        }
        
        if trimmed.hasPrefix("\\rollback") {
            handleRollbackTransaction(trimmed)
            return
        }
    }
    
    /// Begins a new transaction
    private mutating func handleBeginTransaction() {
        do { 
            let tid = try db.begin()
            currentTID = tid
            print("TID=\(tid)")
        } catch { 
            print("error: \(error)") 
        }
    }
    
    /// Commits a transaction (current or specified)
    private mutating func handleCommitTransaction(_ trimmed: String) {
        let parts = trimmed.split(separator: " ")
        var tid: UInt64? = nil
        if parts.count >= 2 { 
            tid = UInt64(parts[1]) 
        }
        if tid == nil { 
            tid = currentTID 
        }
        guard let t = tid else { 
            print("no active TID")
            return 
        }
        do { 
            try db.commit(t)
            print("committed \(t)") 
        } catch { 
            print("error: \(error)") 
        }
        if currentTID == t { 
            currentTID = nil 
        }
    }
    
    /// Rolls back a transaction (current or specified)
    private mutating func handleRollbackTransaction(_ trimmed: String) {
        let parts = trimmed.split(separator: " ")
        var tid: UInt64? = nil
        if parts.count >= 2 { 
            tid = UInt64(parts[1]) 
        }
        if tid == nil { 
            tid = currentTID 
        }
        guard let t = tid else { 
            print("no active TID")
            return 
        }
        do { 
            try db.rollback(t)
            print("aborted \(t)") 
        } catch { 
            print("error: \(error)") 
        }
        if currentTID == t { 
            currentTID = nil 
        }
    }
}
