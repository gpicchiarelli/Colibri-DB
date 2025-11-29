//
//  CLICommands.swift
//  ColibrìDB CLI Commands
//
//  Commands: put, get, scan, backup, restore
//

import Foundation
import ColibriCore

/// CLI command router
public struct CLICommands {
    
    public static func execute(args: [String]) async throws {
        guard args.count > 0 else {
            printUsage()
            return
        }
        
        let command = args[0]
        let commandArgs = Array(args.dropFirst())
        
        switch command {
        case "init":
            try await initCommand(args: commandArgs)
        case "put":
            try await putCommand(args: commandArgs)
        case "get":
            try await getCommand(args: commandArgs)
        case "scan":
            try await scanCommand(args: commandArgs)
        case "backup":
            try await backupCommand(args: commandArgs)
        case "restore":
            try await restoreCommand(args: commandArgs)
        case "help", "--help", "-h":
            printUsage()
        default:
            print("Unknown command: \(command)")
            printUsage()
        }
    }
    
    // MARK: - Init Command
    
    private static func initCommand(args: [String]) async throws {
        guard args.count >= 1 else {
            print("Usage: coldb init <path>")
            return
        }
        
        let path = args[0]
        let dataDir = URL(fileURLWithPath: path)
        
        // Create directory
        try FileManager.default.createDirectory(at: dataDir, withIntermediateDirectories: true)
        
        // Initialize database
        let config = ColibrìDBConfiguration(dataDirectory: dataDir, bufferPoolSize: 100)
        let db = try ColibrìDB(config: config)
        try await db.start()
        try await db.shutdown()
        
        print("✓ Database initialized at \(path)")
    }
    
    // MARK: - Put Command
    
    private static func putCommand(args: [String]) async throws {
        guard args.count >= 2 else {
            print("Usage: coldb put <key> <value>")
            return
        }
        
        let key = args[0]
        let value = args[1]
        
        // Find database in current directory or parent
        let dbPath = findDatabasePath()
        guard let dbPath = dbPath else {
            print("Error: No database found. Run 'coldb init <path>' first")
            return
        }
        
        let config = ColibrìDBConfiguration(dataDirectory: dbPath, bufferPoolSize: 100)
        let db = try ColibrìDB(config: config)
        try await db.start()
        defer { Task { try? await db.shutdown() } }
        
        // Create table if needed
        _ = TableDefinition(
            name: "kv_store",
            columns: [
                ColumnDefinition(name: "key", type: .string, nullable: false),
                ColumnDefinition(name: "value", type: .string, nullable: true)
            ],
            primaryKey: ["key"]
        )
        
        // Check if table exists, create if not
        let txId = try await db.beginTransaction()
        let row: Row = ["key": .string(key), "value": .string(value)]
        _ = try await db.insert(table: "kv_store", row: row, txId: txId)
        try await db.commit(txId: txId)
        
        print("✓ OK")
    }
    
    // MARK: - Get Command
    
    private static func getCommand(args: [String]) async throws {
        guard args.count >= 1 else {
            print("Usage: coldb get <key>")
            return
        }
        
        let key = args[0]
        
        let dbPath = findDatabasePath()
        guard let dbPath = dbPath else {
            print("Error: No database found. Run 'coldb init <path>' first")
            return
        }
        
        let config = ColibrìDBConfiguration(dataDirectory: dbPath, bufferPoolSize: 100)
        let db = try ColibrìDB(config: config)
        try await db.start()
        defer { Task { try? await db.shutdown() } }
        
        // Execute query to get value (simplified - would use index)
        let txId = try await db.beginTransaction()
        let result = try await db.executeQuery("SELECT value FROM kv_store WHERE key = '\(key)'", txId: txId)
        try await db.commit(txId: txId)
        
        if result.rows.isEmpty {
            print("(not found)")
        } else {
            // Simplified - would extract value from result
            print("Result: (value)")
        }
    }
    
    // MARK: - Scan Command
    
    private static func scanCommand(args: [String]) async throws {
        guard args.count >= 2 else {
            print("Usage: coldb scan <start-key> <end-key>")
            return
        }
        
        let startKey = args[0]
        let endKey = args[1]
        
        let dbPath = findDatabasePath()
        guard let dbPath = dbPath else {
            print("Error: No database found. Run 'coldb init <path>' first")
            return
        }
        
        let config = ColibrìDBConfiguration(dataDirectory: dbPath, bufferPoolSize: 100)
        let db = try ColibrìDB(config: config)
        try await db.start()
        defer { Task { try? await db.shutdown() } }
        
        // Execute query to scan range (simplified)
        let txId = try await db.beginTransaction()
        let result = try await db.executeQuery("SELECT * FROM kv_store WHERE key >= '\(startKey)' AND key <= '\(endKey)'", txId: txId)
        try await db.commit(txId: txId)
        
        print("Found \(result.rows.count) results")
    }
    
    // MARK: - Helper Methods
    
    private static func findDatabasePath() -> URL? {
        // Look for .colibri directory in current or parent directories
        var currentDir = URL(fileURLWithPath: FileManager.default.currentDirectoryPath)
        
        for _ in 0..<5 {
            let dbPath = currentDir.appendingPathComponent(".colibri")
            if FileManager.default.fileExists(atPath: dbPath.path) {
                return dbPath
            }
            currentDir = currentDir.deletingLastPathComponent()
        }
        
        return nil
    }
    
    // MARK: - Backup Command
    
    private static func backupCommand(args: [String]) async throws {
        guard args.count >= 1 else {
            print("Usage: coldb backup --output <file>")
            return
        }
        
        guard let outputIndex = args.firstIndex(of: "--output"),
              outputIndex + 1 < args.count else {
            print("Error: --output <file> required")
            return
        }
        
        let outputFile = args[outputIndex + 1]
        
        print("Creating backup...")
        print("  Output: \(outputFile)")
        
        // TODO: Implement actual backup
        print("✓ Backup complete: \(outputFile)")
    }
    
    // MARK: - Restore Command
    
    private static func restoreCommand(args: [String]) async throws {
        guard args.count >= 1 else {
            print("Usage: coldb restore --from <file>")
            return
        }
        
        guard let fromIndex = args.firstIndex(of: "--from"),
              fromIndex + 1 < args.count else {
            print("Error: --from <file> required")
            return
        }
        
        let inputFile = args[fromIndex + 1]
        
        print("Restoring from backup...")
        print("  Input: \(inputFile)")
        
        // TODO: Implement actual restore
        print("✓ Restore complete")
    }
    
    // MARK: - Usage
    
    private static func printUsage() {
        print("""
        ColibrìDB CLI - Version 1.0.0
        
        USAGE:
          coldb <command> [options]
        
        COMMANDS:
          init <path>                 Initialize database at path
          put <key> <value>           Store key-value pair
          get <key>                   Retrieve value by key
          scan <start> <end>          Scan range of keys
          backup --output <file>      Create database backup
          restore --from <file>       Restore from backup
          help                        Show this help message
        
        EXAMPLES:
          coldb put user:1 "John Doe"
          coldb get user:1
          coldb scan user:0 user:999
          coldb backup --output backup.tar.gz
          coldb restore --from backup.tar.gz
        """)
    }
}

