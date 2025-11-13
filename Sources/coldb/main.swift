//
//  main.swift
//  coldb - ColibrìDB CLI
//
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//

import Foundation
import ColibriCore

let args = Array(CommandLine.arguments.dropFirst())

if args.isEmpty || args.contains("--help") || args.contains("-h") {
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
    """)
    exit(0)
}

Task {
    do {
        try await CLICommands.execute(args: args)
    } catch {
        print("Error: \(error)")
        exit(1)
    }
}

RunLoop.main.run()
