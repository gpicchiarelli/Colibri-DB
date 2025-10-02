//
//  DevCLI+Maintenance.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Database maintenance commands for development CLI.

import Foundation
import ColibriCore

extension DevCLI {
    
    /// Handles maintenance-related commands (flush, stats, vacuum, checkpoint, etc.)
    mutating func handleMaintenanceCommands(_ trimmed: String) {
        if trimmed.hasPrefix("\\flush all") {
            handleFlushAll(trimmed)
            return
        }
        
        if trimmed.hasPrefix("\\flush table ") {
            handleFlushTable(trimmed)
            return
        }
        
        if trimmed.hasPrefix("\\flush index ") {
            handleFlushIndex(trimmed)
            return
        }
        
        if trimmed == "\\bp" {
            handleBufferPoolStats()
            return
        }
        
        if trimmed == "\\stats" {
            handleStats()
            return
        }
        
        if trimmed.hasPrefix("\\table compact ") {
            handleTableCompact(String(trimmed.dropFirst("\\table compact ".count)))
            return
        }
        
        if trimmed.hasPrefix("\\vacuum start") {
            handleVacuumStart(trimmed)
            return
        }
        
        if trimmed == "\\vacuum stop" { 
            handleVacuumStop()
            return 
        }
        
        if trimmed == "\\vacuum stats" { 
            handleVacuumStats()
            return 
        }
        
        if trimmed == "\\checkpoint" {
            handleCheckpoint()
            return
        }
    }
    
    /// Flushes all buffers
    private func handleFlushAll(_ trimmed: String) {
        let tokens = trimmed.split(whereSeparator: { $0.isWhitespace })
        let fullSync = tokens.contains { $0.lowercased() == "fullsync" }
        db.flushAll(fullSync: fullSync)
        print(fullSync ? "flushed (fullsync)" : "flushed")
    }
    
    /// Flushes table buffers
    private func handleFlushTable(_ trimmed: String) {
        let tokens = trimmed.split(whereSeparator: { $0.isWhitespace })
        guard tokens.count >= 3 else { 
            print("usage: \\flush table <table> [fullsync]")
            return 
        }
        let table = String(tokens[2])
        let fullSync = tokens.dropFirst(3).contains { $0.lowercased() == "fullsync" }
        do {
            try db.flushTable(table, fullSync: fullSync)
            print(fullSync ? "flushed table (fullsync)" : "flushed table")
        } catch { 
            print("error: \(error)") 
        }
    }
    
    /// Flushes index buffers
    private func handleFlushIndex(_ trimmed: String) {
        let tokens = trimmed.split(whereSeparator: { $0.isWhitespace })
        guard tokens.count >= 4 else { 
            print("usage: \\flush index <table> <index> [fullsync]")
            return 
        }
        let table = String(tokens[2])
        let index = String(tokens[3])
        let fullSync = tokens.dropFirst(4).contains { $0.lowercased() == "fullsync" }
        do {
            try db.flushIndex(table, index, fullSync: fullSync)
            print(fullSync ? "flushed index (fullsync)" : "flushed index")
        } catch { 
            print("error: \(error)") 
        }
    }
    
    /// Shows buffer pool statistics
    private func handleBufferPoolStats() {
        do {
            for line in try db.bufferPoolStats() { 
                print(line) 
            }
        } catch {
            print("Error getting buffer pool stats: \(error)")
        }
    }
    
    /// Shows aggregate statistics
    private func handleStats() {
        print(db.bufferPoolAggregateStats())
        print(db.vacuumStats())
    }
    
    /// Invokes heap compaction optionally targeting a single page.
    private func handleTableCompact(_ rest: String) {
        let parts = rest.split(separator: " ")
        guard parts.count >= 1 else { 
            print("usage: \\table compact <table> [pageId]")
            return 
        }
        let table = String(parts[0])
        let pid = parts.count >= 2 ? UInt64(parts[1]) : nil
        do { 
            let s = try db.compactTable(table: table, pageId: pid)
            print(s) 
        } catch { 
            print("error: \(error)") 
        }
    }
    
    /// Starts periodic vacuum
    private func handleVacuumStart(_ trimmed: String) {
        let parts = trimmed.split(separator: " ")
        let sec = parts.count >= 3 ? (Double(parts[2]) ?? 5.0) : 5.0
        let pages = parts.count >= 4 ? (Int(parts[3]) ?? 32) : 32
        db.startVacuum(intervalSeconds: sec, pagesPerRun: pages)
        print("vacuum started")
    }
    
    /// Stops periodic vacuum
    private func handleVacuumStop() {
        db.stopVacuum()
        print("vacuum stopped")
    }
    
    /// Shows vacuum statistics
    private func handleVacuumStats() {
        print(db.vacuumStats())
    }
    
    /// Creates a checkpoint
    private func handleCheckpoint() {
        do { 
            try db.checkpoint()
            print("checkpoint done") 
        } catch { 
            print("error: \(error)") 
        }
    }
}
