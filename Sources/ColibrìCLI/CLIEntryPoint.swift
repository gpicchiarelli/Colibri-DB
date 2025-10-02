//
//  CLIEntryPoint.swift
//  ColibrìDB - Unified CLI Entry Point
//
//  Created by Giacomo Picchiarelli on 2025-01-02.
//

import Foundation
import ColibriCore

/// Unified CLI entry point that routes to production or development CLI
public struct CLIEntryPoint {
    
    /// CLI Mode selection
    public enum CLIMode {
        case production
        case development
    }
    
    /// Launch the appropriate CLI based on mode
    public static func launch(mode: CLIMode, configPath: String? = nil) throws {
        switch mode {
        case .production:
            let cli = try ProductionCLI()
            try cli.run()
            
        case .development:
            let config = loadConfig(from: configPath)
            let database = Database(config: config)
            try database.ensureDataDir()
            
            let devCLI = DevCLI(db: database, cfgPath: configPath)
            devCLI.printBanner()
            devCLI.runInteractiveLoop()
        }
    }
    
    /// Load configuration from file or use defaults
    private static func loadConfig(from path: String?) -> DBConfig {
        guard let path = path else {
            return DBConfig() // Default config
        }
        
        do {
            let data = try Data(contentsOf: URL(fileURLWithPath: path))
            let decoder = JSONDecoder()
            return try decoder.decode(DBConfig.self, from: data)
        } catch {
            print("⚠️ Warning: Could not load config from \(path), using defaults")
            return DBConfig()
        }
    }
}
