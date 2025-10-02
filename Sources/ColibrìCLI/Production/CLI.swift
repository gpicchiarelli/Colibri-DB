//
//  CLI.swift
//  ColibrDB - Production CLI Core
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//

import Foundation
import ColibriCore

/// Professional command-line interface for ColibrDB production use
public class ProductionCLI {
    internal let database: Database
    internal let formatter = CLIFormatter()
    internal var isRunning = true
    
    public init() throws {
        // Initialize with production-ready configuration
        var config = DBConfig()
        config.pageSizeBytes = 8192
        config.dataBufferPoolPages = 512
        config.indexBufferPoolPages = 256
        config.walFullFSyncEnabled = true
        config.lockTimeoutSeconds = 30.0
        
        self.database = Database(config: config)
        
        // Apply Apple Silicon optimizations if available
        #if os(macOS) && arch(arm64)
        if #available(macOS 13.0, *) {
            AppleSiliconIntegration.applyOptimizations(to: &config)
        }
        #endif
    }
    
    public func run() throws {
        formatter.printWelcome()
        
        while isRunning {
            do {
                let input = formatter.readInput()
                try processCommand(input)
            } catch {
                formatter.printError("Command failed: \(error.localizedDescription)")
            }
        }
        
        formatter.printGoodbye()
    }
    
    private func processCommand(_ input: String) throws {
        let trimmed = input.trimmingCharacters(in: .whitespacesAndNewlines)
        
        // Handle empty input
        guard !trimmed.isEmpty else { return }
        
        // Meta commands
        if trimmed.hasPrefix("\\") {
            try handleMetaCommand(String(trimmed))
            return
        }
        
        // SQL queries
        try handleSQLQuery(String(trimmed))
    }
    
    // MARK: - Command Handlers
    
    internal func handleMetaCommand(_ command: String) throws {
        let cmd = command.lowercased()
        
        switch cmd {
        case "\\help", "\\h", "\\?":
            formatter.printHelp()
        case "\\quit", "\\q", "\\exit":
            isRunning = false
        case "\\status":
            formatter.printInfo("Database status: Running")
        case "\\tables":
            formatter.printInfo("Tables: (not implemented)")
        default:
            formatter.printError("Unknown meta command: \(command)")
            formatter.printInfo("Type \\help for available commands")
        }
    }
    
    internal func handleSQLQuery(_ query: String) throws {
        // Basic SQL execution using Database methods
        let trimmed = query.trimmingCharacters(in: .whitespacesAndNewlines)
        
        if trimmed.uppercased().hasPrefix("CREATE TABLE") {
            // Extract table name - very basic parsing
            let parts = trimmed.split(separator: " ")
            if parts.count >= 3 {
                let tableName = String(parts[2]).trimmingCharacters(in: CharacterSet(charactersIn: ";()"))
                try database.createTable(tableName)
                formatter.printSuccess("Table '\(tableName)' created successfully")
            } else {
                throw CLIError.invalidSyntax("Usage: CREATE TABLE <name>")
            }
        } else if trimmed.uppercased().hasPrefix("INSERT INTO") {
            formatter.printInfo("INSERT not implemented in basic CLI")
        } else if trimmed.uppercased().hasPrefix("SELECT") {
            formatter.printInfo("SELECT not implemented in basic CLI")
        } else if trimmed.uppercased() == "\\TEST WAL" {
            try runWALTests()
        } else {
            throw CLIError.unknownCommand("Unknown SQL command: \(trimmed)")
        }
    }
    
    private func runWALTests() throws {
        formatter.printInfo("Running WAL Acceptance Tests...")
        
        let testRunner = WALTestRunner(verbose: true)
        testRunner.runTests()
    }
}

// MARK: - CLI Errors

enum CLIError: Error, LocalizedError {
    case invalidSyntax(String)
    case unknownCommand(String)
    case databaseError(String)
    
    var errorDescription: String? {
        switch self {
        case .invalidSyntax(let msg): return "Syntax error: \(msg)"
        case .unknownCommand(let msg): return "Unknown command: \(msg)"
        case .databaseError(let msg): return "Database error: \(msg)"
        }
    }
}
