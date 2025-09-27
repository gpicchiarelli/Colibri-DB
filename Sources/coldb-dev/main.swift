//
//  main.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Development CLI entry point using modular structure.

import Foundation
import ColibriCore
import os.log

// Entry point
var configPath: String? = nil
var i = 1
let args = CommandLine.arguments
while i < args.count {
    switch args[i] {
    case "--config", "-c":
        if i + 1 < args.count { configPath = args[i+1]; i += 1 }
    default:
        break
    }
    i += 1
}

// Initialize Apple Silicon optimizations
let logger = Logger(subsystem: "com.colibridb", category: "coldb-dev")
logger.info("Initializing ColibrìDB Development CLI with Apple Silicon optimizations")

// Initialize Apple Silicon integration
AppleSiliconIntegration.initialize()

do {
    let cfg = try ConfigIO.load(from: configPath)
    
    // Apply Apple Silicon optimizations to configuration
    var optimizedConfig = cfg
    AppleSiliconIntegration.applyOptimizations(to: &optimizedConfig)
    
    // Log system information
    let systemInfo = AppleSiliconIntegration.getSystemInfo()
    logger.info("System info: \(systemInfo)")
    
    // Create optimized database
    let db = try AppleSiliconIntegration.createOptimizedDatabase(config: optimizedConfig)
    try db.ensureDataDir()
    
    var cli = DevCLI(db: db, cfgPath: configPath)
    cli.printBanner()
    
    // Log performance metrics
    let metrics = AppleSiliconIntegration.getPerformanceMetrics()
    logger.info("Performance metrics: \(metrics)")
    
    while let line = readLine(strippingNewline: true) {
        cli.parseAndRun(line)
    }
} catch {
    logger.error("Fatal error: \(error)")
    fputs("fatal: \(error)\n", stderr)
    exit(1)
}