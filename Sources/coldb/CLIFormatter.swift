//
//  CLIFormatter.swift
//  ColibrìDB - CLI Formatting and Display
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//

import Foundation
import ColibriCore

/// Beautiful formatting and display utilities for the CLI
public class CLIFormatter {
    internal let colors = CLIColors()
    internal var timingEnabled = true
    
    func printWelcome() {
        print(colors.header("""
        ╔═══════════════════════════════════════════════════════════╗
        ║                     🐦 ColibrìDB                          ║
        ║              Professional SQL Database                     ║
        ║                                                           ║
        ║  Type \\help for commands, \\quit to exit                   ║
        ╚═══════════════════════════════════════════════════════════╝
        """))
        print()
    }
    
    func printGoodbye() {
        print(colors.info("\n👋 Thank you for using ColibrìDB!\n"))
    }
    
    func printHelp() {
        print(colors.header("📚 ColibrìDB Commands:"))
        print()
        
        print(colors.section("Meta Commands:"))
        print("  \\help, \\h, \\?         Show this help")
        print("  \\quit, \\q, \\exit      Exit ColibrìDB")
        print("  \\version, \\v          Show version information")
        print("  \\status, \\s           Show database status")
        print("  \\timing               Toggle timing display")
        print()
        
        print(colors.section("Database Exploration:"))
        print("  \\dt                   List all tables")
        print("  \\di                   List all indexes")
        print("  \\d <table>            Describe table structure")
        print()
        
        print(colors.section("SQL Commands:"))
        print("  CREATE TABLE ...      Create a new table")
        print("  DROP TABLE ...        Drop an existing table")
        print("  INSERT INTO ...       Insert data into table")
        print("  SELECT ...            Query data from tables")
        print("  UPDATE ...            Update existing data")
        print("  DELETE FROM ...       Delete data from tables")
        print()
        
        print(colors.section("Transaction Commands:"))
        print("  BEGIN                 Start a transaction")
        print("  COMMIT                Commit current transaction")
        print("  ROLLBACK              Rollback current transaction")
        print()
    }
    
    func printVersion() {
        print(colors.header("ColibrìDB Version Information:"))
        print("  Version: 1.0.0")
        print("  Platform: \(ProcessInfo.processInfo.operatingSystemVersionString)")
        print("  Swift: \(version())")
        print("  Build: Production")
        print()
    }
    
    func printStatus(database: Database) {
        print(colors.header("📊 Database Status:"))
        print("  Configuration: Production")
        print("  Page Size: \(database.config.pageSizeBytes) bytes")
        print("  Buffer Pool: \(database.config.dataBufferPoolPages) data pages, \(database.config.indexBufferPoolPages) index pages")
        print("  WAL: \(database.config.walFullFSyncEnabled ? "Enabled (fsync)" : "Disabled")")
        print("  Lock Timeout: \(database.config.lockTimeoutSeconds)s")
        print()
    }
    
    func readInput() -> String {
        print(colors.prompt("coldb=# "), terminator: "")
        return readLine() ?? ""
    }
    
    func printQueryResult(_ result: String, executionTime: TimeInterval) {
        print(result)
        if timingEnabled {
            printTiming(executionTime)
        }
    }
    
    func printTiming(_ time: TimeInterval) {
        let timeString = String(format: "%.3f", time * 1000)
        print(colors.timing("Time: \(timeString) ms"))
    }
    
    func toggleTiming() {
        timingEnabled.toggle()
        printInfo("Timing display \(timingEnabled ? "enabled" : "disabled")")
    }
    
    private func version() -> String {
        #if swift(>=6.0)
        return "6.0+"
        #elseif swift(>=5.9)
        return "5.9"
        #else
        return "5.8 or earlier"
        #endif
    }
}
