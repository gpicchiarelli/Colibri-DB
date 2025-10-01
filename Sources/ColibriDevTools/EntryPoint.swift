//
//  EntryPoint.swift
//  ColibriDevTools
//
//  Created by Codex on 2025-09-28.
//

import Foundation
import ColibriCore
import os.log

/// Bootstraps the developer CLI (`coldb-dev`) with Apple Silicon optimisations.
public func runColdBDevCLI(arguments: [String]) throws {
    var configPath: String?
    var index = 1
    while index < arguments.count {
        switch arguments[index] {
        case "--config", "-c":
            if index + 1 < arguments.count {
                configPath = arguments[index + 1]
                index += 1
            }
        default:
            break
        }
        index += 1
    }

    let logger = Logger(subsystem: "com.colibridb", category: "coldb-dev")
    logger.info("Initializing ColibrDB Development CLI with Apple Silicon optimizations")

    AppleSiliconIntegration.initialize()

    let baseConfig = try ConfigIO.load(from: configPath)
    var optimizedConfig = baseConfig
    AppleSiliconIntegration.applyOptimizations(to: &optimizedConfig)

    let systemInfo = AppleSiliconIntegration.getSystemInfo()
    logger.info("System info: \(systemInfo)")

    let database = try AppleSiliconIntegration.createOptimizedDatabase(config: optimizedConfig)
    try database.ensureDataDir()

    var cli = DevCLI(db: database, cfgPath: configPath)
    cli.printBanner()

    let metrics = AppleSiliconIntegration.getPerformanceMetrics()
    logger.info("Performance metrics: \(metrics)")

    while let line = readLine(strippingNewline: true) {
        cli.parseAndRun(line)
    }
}
