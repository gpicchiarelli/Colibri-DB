//
//  CLI.swift
//  ColibrìDB - Production CLI Core
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//

import Foundation
import ColibriCore

/// Professional command-line interface for ColibrìDB production use
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
            try handleMetaCommand(trimmed)
            return
        }
        
        // SQL queries
        try handleSQLQuery(trimmed)
    }
}
