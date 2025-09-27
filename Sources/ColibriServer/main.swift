//
//  main.swift
//  ColibrìDB Server
//
//  Created by Giacomo Picchiarelli on 2025-09-26.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Main entry point for ColibrìDB HTTP server.

import Foundation
import os.log

/// Main entry point for ColibrìDB HTTP server
public func main() {
    let logger = Logger(subsystem: "com.colibridb.server", category: "main")
    
    logger.info("Starting ColibrìDB HTTP Server")
    
    // Parse command line arguments
    let arguments = CommandLine.arguments
    let host = arguments.contains("--host") ? 
        arguments[arguments.firstIndex(of: "--host")! + 1] : "localhost"
    let port = arguments.contains("--port") ? 
        UInt16(arguments[arguments.firstIndex(of: "--port")! + 1]) ?? 8080 : 8080
    let dataDir = arguments.contains("--data-dir") ? 
        arguments[arguments.firstIndex(of: "--data-dir")! + 1] : "./data"
    
    // Create database configuration
    let config = DBConfig(
        dataDir: dataDir,
        pageSize: 8192,
        dataBufferPoolPages: 1000,
        indexBufferPoolPages: 500,
        walEnabled: true,
        walFullFSyncEnabled: false,
        walCompression: .none,
        ioSequentialReadHint: true,
        autoCompactionEnabled: true,
        autoCompactionIntervalSeconds: 300,
        autoCompactionPagesPerRun: 32,
        lockTimeoutSeconds: 30.0
    )
    
    // Initialize ColibrìDB
    let colibriDB = ColibriDB(config: config)
    
    do {
        // Initialize the database
        try colibriDB.initialize()
        logger.info("Database initialized successfully")
        
        // Start the database
        try colibriDB.start()
        logger.info("Database started successfully")
        
        // Create and start HTTP server
        let server = ColibriServer(colibriDB: colibriDB, host: host, port: port)
        try server.start()
        logger.info("HTTP server started on \(host):\(port)")
        
        // Print server information
        print("🚀 ColibrìDB HTTP Server")
        print("========================")
        print("Host: \(host)")
        print("Port: \(port)")
        print("Data Directory: \(dataDir)")
        print("")
        print("Available endpoints:")
        print("  GET  /health                    - Health check")
        print("  GET  /status                    - System status")
        print("  GET  /info                      - System information")
        print("  GET  /api/v1/databases          - List databases")
        print("  POST /api/v1/databases          - Create database")
        print("  GET  /api/v1/tables/{db}        - List tables")
        print("  POST /api/v1/tables             - Create table")
        print("  POST /api/v1/query              - Execute SQL query")
        print("  POST /api/v1/transactions/begin - Begin transaction")
        print("  POST /api/v1/transactions/commit - Commit transaction")
        print("  POST /api/v1/transactions/rollback - Rollback transaction")
        print("  GET  /api/v1/indexes/{table}    - List indexes")
        print("  POST /api/v1/indexes            - Create index")
        print("  GET  /api/v1/monitoring/metrics - Get metrics")
        print("  GET  /api/v1/monitoring/health  - Get health status")
        print("  GET  /api/v1/monitoring/errors  - Get error statistics")
        print("  POST /api/v1/testing/run        - Run all tests")
        print("  POST /api/v1/testing/unit       - Run unit tests")
        print("  POST /api/v1/testing/integration - Run integration tests")
        print("  POST /api/v1/testing/performance - Run performance tests")
        print("  GET  /api/v1/performance/metrics - Get performance metrics")
        print("  POST /api/v1/performance/benchmarks - Run benchmarks")
        print("")
        print("Press Ctrl+C to stop the server")
        
        // Set up signal handlers for graceful shutdown
        setupSignalHandlers(server: server, colibriDB: colibriDB)
        
        // Keep the server running
        RunLoop.main.run()
        
    } catch {
        logger.error("Failed to start server: \(error.localizedDescription)")
        print("❌ Error: \(error.localizedDescription)")
        exit(1)
    }
}

/// Sets up signal handlers for graceful shutdown
private func setupSignalHandlers(server: ColibriServer, colibriDB: ColibriDB) {
    let logger = Logger(subsystem: "com.colibridb.server", category: "signals")
    
    // Handle SIGINT (Ctrl+C)
    signal(SIGINT) { _ in
        logger.info("Received SIGINT, shutting down gracefully")
        print("\n🛑 Shutting down server...")
        
        server.stop()
        
        do {
            try colibriDB.stop()
            try colibriDB.shutdown()
            logger.info("Server shutdown completed")
            print("✅ Server shutdown completed")
        } catch {
            logger.error("Error during shutdown: \(error.localizedDescription)")
            print("❌ Error during shutdown: \(error.localizedDescription)")
        }
        
        exit(0)
    }
    
    // Handle SIGTERM
    signal(SIGTERM) { _ in
        logger.info("Received SIGTERM, shutting down gracefully")
        print("\n🛑 Shutting down server...")
        
        server.stop()
        
        do {
            try colibriDB.stop()
            try colibriDB.shutdown()
            logger.info("Server shutdown completed")
            print("✅ Server shutdown completed")
        } catch {
            logger.error("Error during shutdown: \(error.localizedDescription)")
            print("❌ Error during shutdown: \(error.localizedDescription)")
        }
        
        exit(0)
    }
}

/// Prints usage information
private func printUsage() {
    print("""
    ColibrìDB HTTP Server
    
    Usage: colibri-server [options]
    
    Options:
      --host <host>        Server host (default: localhost)
      --port <port>        Server port (default: 8080)
      --data-dir <dir>     Data directory (default: ./data)
      --help               Show this help message
    
    Examples:
      colibri-server
      colibri-server --host 0.0.0.0 --port 9090
      colibri-server --data-dir /var/lib/colibridb
    """)
}

// Check for help flag
if CommandLine.arguments.contains("--help") {
    printUsage()
    exit(0)
}

// Run the main function
main()
