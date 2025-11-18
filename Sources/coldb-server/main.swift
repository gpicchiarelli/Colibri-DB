//
//  main.swift
//  coldb-server - ColibrìDB Server
//
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//

import Foundation
#if canImport(Darwin)
import Darwin
#elseif canImport(Glibc)
import Glibc
#endif
import ColibriServer
import ColibriCore

enum Main {
    // MARK: - Command Line Arguments
    
    struct ServerArguments {
        let host: String
        let port: Int
        let dataDir: URL
        let bufferPoolSize: Int
        let maxConnections: Int
        let help: Bool
        
        static func parse(_ args: [String]) -> ServerArguments? {
            var host = "127.0.0.1"
            var port = 5432
            var dataDir: URL?
            var bufferPoolSize = 1000
            var maxConnections = 100
            var help = false
            
            var i = 0
            while i < args.count {
                switch args[i] {
                case "--host", "-h":
                    if i + 1 < args.count {
                        host = args[i + 1]
                        i += 2
                    } else {
                        print("Error: --host requires a value")
                        return nil
                    }
                case "--port", "-p":
                    if i + 1 < args.count {
                        guard let p = Int(args[i + 1]) else {
                            print("Error: --port must be a number")
                            return nil
                        }
                        port = p
                        i += 2
                    } else {
                        print("Error: --port requires a value")
                        return nil
                    }
                case "--data-dir", "-d":
                    if i + 1 < args.count {
                        dataDir = URL(fileURLWithPath: args[i + 1])
                        i += 2
                    } else {
                        print("Error: --data-dir requires a path")
                        return nil
                    }
                case "--buffer-pool-size", "-b":
                    if i + 1 < args.count {
                        guard let size = Int(args[i + 1]) else {
                            print("Error: --buffer-pool-size must be a number")
                            return nil
                        }
                        bufferPoolSize = size
                        i += 2
                    } else {
                        print("Error: --buffer-pool-size requires a value")
                        return nil
                    }
                case "--max-connections", "-c":
                    if i + 1 < args.count {
                        guard let max = Int(args[i + 1]) else {
                            print("Error: --max-connections must be a number")
                            return nil
                        }
                        maxConnections = max
                        i += 2
                    } else {
                        print("Error: --max-connections requires a value")
                        return nil
                    }
                case "--help":
                    help = true
                    i += 1
                default:
                    print("Error: Unknown argument: \(args[i])")
                    print("Use --help for usage information")
                    return nil
                }
            }
            
            // Default data directory if not specified
            if dataDir == nil {
                let homeDir = FileManager.default.homeDirectoryForCurrentUser
                dataDir = homeDir.appendingPathComponent(".colibridb")
            }
            
            return ServerArguments(
                host: host,
                port: port,
                dataDir: dataDir!,
                bufferPoolSize: bufferPoolSize,
                maxConnections: maxConnections,
                help: help
            )
        }
    }
    
    // MARK: - Signal Handling
    
    nonisolated(unsafe) static var globalShutdownManager: ShutdownManager?
    
    actor ShutdownManager {
        private var shouldShutdown = false
        private var database: ColibrìDB?
        
        func setDatabase(_ db: ColibrìDB) {
            self.database = db
        }
        
        func shouldShutdownNow() -> Bool {
            return shouldShutdown
        }
        
        func requestShutdown() async {
            shouldShutdown = true
            if let db = database {
                try? await db.shutdown()
            }
        }
    }
    
    static func printUsage() {
        print("""
        ColibrìDB Server - Version 1.0.0
        
        Usage: coldb-server [OPTIONS]
        
        Options:
          --host, -h HOST          Server host (default: 127.0.0.1)
          --port, -p PORT          Server port (default: 5432)
          --data-dir, -d PATH      Data directory (default: ~/.colibridb)
          --buffer-pool-size, -b SIZE  Buffer pool size in pages (default: 1000)
          --max-connections, -c MAX    Maximum connections (default: 100)
          --help                    Show this help message
        
        Examples:
          coldb-server --host 0.0.0.0 --port 5432
          coldb-server --data-dir /var/lib/colibridb --port 5433
        """)
    }
    
    static func setupSignalHandlers(shutdownManager: ShutdownManager) {
        // Store in global variable for signal handler access
        Main.globalShutdownManager = shutdownManager
        
        signal(SIGINT) { _ in
            print("\nReceived SIGINT, shutting down gracefully...")
            if let manager = Main.globalShutdownManager {
                Task {
                    await manager.requestShutdown()
                    exit(0)
                }
            } else {
                exit(0)
            }
        }
        
        signal(SIGTERM) { _ in
            print("\nReceived SIGTERM, shutting down gracefully...")
            if let manager = Main.globalShutdownManager {
                Task {
                    await manager.requestShutdown()
                    exit(0)
                }
            } else {
                exit(0)
            }
        }
    }
    
    // MARK: - Main Entry Point
    
    static func main() async {
        let args = Array(CommandLine.arguments.dropFirst())
        
        guard let config = ServerArguments.parse(args) else {
            exit(1)
        }
        
        if config.help {
            printUsage()
            exit(0)
        }
        
        let shutdownManager = ShutdownManager()
        
        // Setup signal handlers
        setupSignalHandlers(shutdownManager: shutdownManager)
        
        // Create data directory if it doesn't exist
        do {
            try FileManager.default.createDirectory(
                at: config.dataDir,
                withIntermediateDirectories: true
            )
        } catch {
            print("Error: Failed to create data directory: \(error)")
            exit(1)
        }
        
        // Create database configuration
        let dbConfig = ColibrìDBConfiguration(
            dataDirectory: config.dataDir,
            bufferPoolSize: config.bufferPoolSize,
            maxConnections: config.maxConnections,
            walBufferSize: 1024 * 1024,
            checkpointInterval: 300,
            logLevel: .info,
            enableStatistics: true,
            enableAutoAnalyze: true
        )
        
        // Initialize database
        do {
            print("Initializing ColibrìDB...")
            print("  Data directory: \(config.dataDir.path)")
            print("  Buffer pool size: \(config.bufferPoolSize) pages")
            print("  Max connections: \(config.maxConnections)")
            
            let db = try ColibrìDB(config: dbConfig)
            await shutdownManager.setDatabase(db)
            
            print("Starting database...")
            try await db.start()
            
            // Create HTTP server with ColibriServer
            let serverConfig = ServerConfig(
                host: config.host,
                port: config.port,
                maxConnections: config.maxConnections,
                timeoutSeconds: 30,
                enableSSL: false
            )
            let server = ColibriServer(config: serverConfig, database: db)
            
            print("Starting HTTP server...")
            try await server.start()
            
            print("✓ ColibrìDB started successfully")
            print("  Database: Running")
            print("  HTTP Server: Listening on \(config.host):\(config.port)")
            print("  Press Ctrl+C to shutdown")
            
            // Keep server running
            while !(await shutdownManager.shouldShutdownNow()) {
                try await Task.sleep(nanoseconds: 1_000_000_000) // 1 second
            }
            
            // Stop server gracefully
            print("Shutting down server...")
            await server.stop()
            
        } catch {
            print("Error: Failed to start database: \(error)")
            exit(1)
        }
    }
}
