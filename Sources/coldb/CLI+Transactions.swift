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
    /// Handles transaction begin command
    mutating func handleBegin() {
        do { 
            let tid = try db.begin()
            currentTID = tid
            print("TID=\(tid)")
        } catch { 
            print("error: \(error)") 
        }
    }
    
    /// Handles transaction commit command
    mutating func handleCommit(_ parts: [Substring]) {
        var tid: UInt64? = nil
        if parts.count >= 2 { tid = UInt64(parts[1]) }
        if tid == nil { tid = currentTID }
        guard let t = tid else { print("no active TID"); return }
        do { 
            try db.commit(t)
            print("committed \(t)") 
        } catch { 
            print("error: \(error)") 
        }
        if currentTID == t { currentTID = nil }
    }
    
    /// Handles transaction rollback command
    mutating func handleRollback(_ parts: [Substring]) {
        var tid: UInt64? = nil
        if parts.count >= 2 { tid = UInt64(parts[1]) }
        if tid == nil { tid = currentTID }
        guard let t = tid else { print("no active TID"); return }
        do { 
            try db.rollback(t)
            print("aborted \(t)") 
        } catch { 
            print("error: \(error)") 
        }
        if currentTID == t { currentTID = nil }
    }
}
