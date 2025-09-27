//
//  ConfigurationManager.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-26.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Configuration management system for ColibrìDB.

import Foundation
import os.log

/// Configuration manager for ColibrìDB
public final class ConfigurationManager {
    private let logger = Logger(subsystem: "com.colibridb.config", category: "manager")
    private var configurations: [String: Any] = [:]
    private let configLock = NSLock()
    
    public init() {
        loadDefaultConfigurations()
    }
    
    /// Loads default configurations
    private func loadDefaultConfigurations() {
        // Database configurations
        set("database.name", value: "ColibrìDB")
        set("database.version", value: "1.0.0")
        set("database.encoding", value: "utf8")
        set("database.collation", value: "utf8_general_ci")
        
        // Storage configurations
        set("storage.pageSize", value: 8192)
        set("storage.maxPages", value: 1000000)
        set("storage.dataDir", value: "./data")
        set("storage.walEnabled", value: true)
        set("storage.walSize", value: 64 * 1024 * 1024) // 64MB
        set("storage.checkpointInterval", value: 300) // 5 minutes
        
        // Buffer pool configurations
        set("buffer.dataPoolPages", value: 1000)
        set("buffer.indexPoolPages", value: 500)
        set("buffer.evictionPolicy", value: "LRU")
        set("buffer.deferredWrite", value: true)
        set("buffer.maxDirty", value: 100)
        
        // Index configurations
        set("index.defaultType", value: "BTREE")
        set("index.btreePageSize", value: 8192)
        set("index.artMaxKeyLength", value: 1024)
        set("index.lsmMaxMemTableSize", value: 64 * 1024 * 1024) // 64MB
        set("index.lsmMaxLevels", value: 7)
        
        // Transaction configurations
        set("transaction.isolationLevel", value: "READ_COMMITTED")
        set("transaction.lockTimeout", value: 30.0)
        set("transaction.maxActive", value: 1000)
        set("transaction.deadlockDetection", value: true)
        
        // Query configurations
        set("query.maxExecutionTime", value: 300.0) // 5 minutes
        set("query.maxMemory", value: 100 * 1024 * 1024) // 100MB
        set("query.parallelism", value: 4)
        set("query.cacheEnabled", value: true)
        set("query.cacheSize", value: 1000)
        
        // Monitoring configurations
        set("monitoring.enabled", value: true)
        set("monitoring.interval", value: 1.0)
        set("monitoring.metricsEnabled", value: true)
        set("monitoring.profilingEnabled", value: false)
        
        // Logging configurations
        set("logging.level", value: "INFO")
        set("logging.file", value: "./colibridb.log")
        set("logging.maxSize", value: 10 * 1024 * 1024) // 10MB
        set("logging.maxFiles", value: 5)
        
        // Performance configurations
        set("performance.simdEnabled", value: true)
        set("performance.accelerateEnabled", value: true)
        set("performance.compressionEnabled", value: true)
        set("performance.optimizationLevel", value: 2)
        
        // Security configurations
        set("security.encryptionEnabled", value: false)
        set("security.encryptionKey", value: "")
        set("security.accessControl", value: true)
        set("security.auditLogging", value: false)
        
        logger.info("Default configurations loaded")
    }
    
    /// Sets a configuration value
    public func set<T>(_ key: String, value: T) {
        configLock.lock()
        defer { configLock.unlock() }
        
        configurations[key] = value
        logger.debug("Configuration set: \(key) = \(String(describing: value))")
    }
    
    /// Gets a configuration value
    public func get<T>(_ key: String, type: T.Type) -> T? {
        configLock.lock()
        defer { configLock.unlock() }
        
        return configurations[key] as? T
    }
    
    /// Gets a configuration value with default
    public func get<T>(_ key: String, type: T.Type, defaultValue: T) -> T {
        return get(key, type: type) ?? defaultValue
    }
    
    /// Gets a string configuration
    public func getString(_ key: String, defaultValue: String = "") -> String {
        return get(key, type: String.self, defaultValue: defaultValue)
    }
    
    /// Gets a string configuration (optional)
    public func getString(_ key: String) -> String? {
        return get(key, type: String.self)
    }
    
    /// Gets an integer configuration
    public func getInt(_ key: String, defaultValue: Int = 0) -> Int {
        return get(key, type: Int.self, defaultValue: defaultValue)
    }
    
    /// Gets an integer configuration (optional)
    public func getInt(_ key: String) -> Int? {
        return get(key, type: Int.self)
    }
    
    /// Gets a double configuration
    public func getDouble(_ key: String, defaultValue: Double = 0.0) -> Double {
        return get(key, type: Double.self, defaultValue: defaultValue)
    }
    
    /// Gets a boolean configuration
    public func getBool(_ key: String, defaultValue: Bool = false) -> Bool {
        return get(key, type: Bool.self, defaultValue: defaultValue)
    }
    
    /// Gets all configurations
    public func getAllConfigurations() -> [String: Any] {
        configLock.lock()
        defer { configLock.unlock() }
        return configurations
    }
    
    /// Loads configurations from file
    public func loadFromFile(_ path: String) throws {
        let data = try Data(contentsOf: URL(fileURLWithPath: path))
        let json = try JSONSerialization.jsonObject(with: data, options: [])
        
        guard let configDict = json as? [String: Any] else {
            throw ConfigurationError.invalidFormat
        }
        
        configLock.lock()
        defer { configLock.unlock() }
        
        for (key, value) in configDict {
            configurations[key] = value
        }
        
        logger.info("Configurations loaded from file: \(path)")
    }
    
    /// Saves configurations to file
    public func saveToFile(_ path: String) throws {
        configLock.lock()
        defer { configLock.unlock() }
        
        let data = try JSONSerialization.data(withJSONObject: configurations, options: .prettyPrinted)
        try data.write(to: URL(fileURLWithPath: path))
        
        logger.info("Configurations saved to file: \(path)")
    }
    
    /// Validates configurations
    public func validateConfigurations() throws {
        var errors: [String] = []
        
        // Validate required configurations
        let requiredConfigs = [
            "database.name",
            "storage.pageSize",
            "buffer.dataPoolPages",
            "transaction.isolationLevel"
        ]
        
        for key in requiredConfigs {
            if configurations[key] == nil {
                errors.append("Required configuration missing: \(key)")
            }
        }
        
        // Validate page size
        if let pageSize = getInt("storage.pageSize"), pageSize < 1024 || pageSize > 65536 {
            errors.append("Invalid page size: \(pageSize). Must be between 1024 and 65536")
        }
        
        // Validate buffer pool size
        if let dataPoolPages = getInt("buffer.dataPoolPages"), dataPoolPages < 10 {
            errors.append("Invalid data pool pages: \(dataPoolPages). Must be at least 10")
        }
        
        // Validate isolation level
        if let isolationLevel = getString("transaction.isolationLevel") {
            let validLevels = ["READ_UNCOMMITTED", "READ_COMMITTED", "REPEATABLE_READ", "SERIALIZABLE"]
            if !validLevels.contains(isolationLevel) {
                errors.append("Invalid isolation level: \(isolationLevel)")
            }
        }
        
        if !errors.isEmpty {
            throw ConfigurationError.validationFailed(errors)
        }
        
        logger.info("Configuration validation passed")
    }
    
    /// Resets configurations to defaults
    public func resetToDefaults() {
        configLock.lock()
        defer { configLock.unlock() }
        
        configurations.removeAll()
        loadDefaultConfigurations()
        
        logger.info("Configurations reset to defaults")
    }
    
    /// Gets configuration statistics
    public func getStatistics() -> ConfigurationStatistics {
        configLock.lock()
        defer { configLock.unlock() }
        
        return ConfigurationStatistics(
            totalConfigurations: configurations.count,
            databaseConfigurations: configurations.filter { $0.key.hasPrefix("database.") }.count,
            storageConfigurations: configurations.filter { $0.key.hasPrefix("storage.") }.count,
            bufferConfigurations: configurations.filter { $0.key.hasPrefix("buffer.") }.count,
            indexConfigurations: configurations.filter { $0.key.hasPrefix("index.") }.count,
            transactionConfigurations: configurations.filter { $0.key.hasPrefix("transaction.") }.count,
            queryConfigurations: configurations.filter { $0.key.hasPrefix("query.") }.count,
            monitoringConfigurations: configurations.filter { $0.key.hasPrefix("monitoring.") }.count,
            loggingConfigurations: configurations.filter { $0.key.hasPrefix("logging.") }.count,
            performanceConfigurations: configurations.filter { $0.key.hasPrefix("performance.") }.count,
            securityConfigurations: configurations.filter { $0.key.hasPrefix("security.") }.count
        )
    }
}

/// Configuration statistics
public struct ConfigurationStatistics {
    public let totalConfigurations: Int
    public let databaseConfigurations: Int
    public let storageConfigurations: Int
    public let bufferConfigurations: Int
    public let indexConfigurations: Int
    public let transactionConfigurations: Int
    public let queryConfigurations: Int
    public let monitoringConfigurations: Int
    public let loggingConfigurations: Int
    public let performanceConfigurations: Int
    public let securityConfigurations: Int
    
    public init(totalConfigurations: Int, databaseConfigurations: Int, storageConfigurations: Int, bufferConfigurations: Int, indexConfigurations: Int, transactionConfigurations: Int, queryConfigurations: Int, monitoringConfigurations: Int, loggingConfigurations: Int, performanceConfigurations: Int, securityConfigurations: Int) {
        self.totalConfigurations = totalConfigurations
        self.databaseConfigurations = databaseConfigurations
        self.storageConfigurations = storageConfigurations
        self.bufferConfigurations = bufferConfigurations
        self.indexConfigurations = indexConfigurations
        self.transactionConfigurations = transactionConfigurations
        self.queryConfigurations = queryConfigurations
        self.monitoringConfigurations = monitoringConfigurations
        self.loggingConfigurations = loggingConfigurations
        self.performanceConfigurations = performanceConfigurations
        self.securityConfigurations = securityConfigurations
    }
}

/// Configuration errors
public enum ConfigurationError: Error, LocalizedError {
    case invalidFormat
    case validationFailed([String])
    case fileNotFound(String)
    case fileReadError(String)
    case fileWriteError(String)
    case invalidValue(String, String) // Changed from Any to String for Sendable compliance
    case missingRequired(String)
    
    public var errorDescription: String? {
        switch self {
        case .invalidFormat:
            return "Invalid configuration format"
        case .validationFailed(let errors):
            return "Configuration validation failed: \(errors.joined(separator: ", "))"
        case .fileNotFound(let path):
            return "Configuration file not found: \(path)"
        case .fileReadError(let path):
            return "Error reading configuration file: \(path)"
        case .fileWriteError(let path):
            return "Error writing configuration file: \(path)"
        case .invalidValue(let key, let value):
            return "Invalid value for \(key): \(value)"
        case .missingRequired(let key):
            return "Required configuration missing: \(key)"
        }
    }
}

/// Configuration validator
public final class ConfigurationValidator {
    private let logger = Logger(subsystem: "com.colibridb.config", category: "validator")
    
    public init() {}
    
    /// Validates a configuration value
    public func validate<T>(_ key: String, value: T) throws {
        switch key {
        case "storage.pageSize":
            guard let intValue = value as? Int else {
                throw ConfigurationError.invalidValue(key, String(describing: value))
            }
            if intValue < 1024 || intValue > 65536 {
                throw ConfigurationError.invalidValue(key, String(describing: value))
            }
            
        case "buffer.dataPoolPages":
            guard let intValue = value as? Int else {
                throw ConfigurationError.invalidValue(key, String(describing: value))
            }
            if intValue < 10 {
                throw ConfigurationError.invalidValue(key, String(describing: value))
            }
            
        case "transaction.isolationLevel":
            guard let stringValue = value as? String else {
                throw ConfigurationError.invalidValue(key, String(describing: value))
            }
            let validLevels = ["READ_UNCOMMITTED", "READ_COMMITTED", "REPEATABLE_READ", "SERIALIZABLE"]
            if !validLevels.contains(stringValue) {
                throw ConfigurationError.invalidValue(key, String(describing: value))
            }
            
        case "query.maxExecutionTime":
            guard let doubleValue = value as? Double else {
                throw ConfigurationError.invalidValue(key, String(describing: value))
            }
            if doubleValue <= 0 {
                throw ConfigurationError.invalidValue(key, String(describing: value))
            }
            
        case "query.maxMemory":
            guard let intValue = value as? Int else {
                throw ConfigurationError.invalidValue(key, String(describing: value))
            }
            if intValue <= 0 {
                throw ConfigurationError.invalidValue(key, String(describing: value))
            }
            
        case "logging.level":
            guard let stringValue = value as? String else {
                throw ConfigurationError.invalidValue(key, String(describing: value))
            }
            let validLevels = ["DEBUG", "INFO", "WARN", "ERROR", "FATAL"]
            if !validLevels.contains(stringValue.uppercased()) {
                throw ConfigurationError.invalidValue(key, String(describing: value))
            }
            
        default:
            // No specific validation for this key
            break
        }
    }
    
    /// Validates all configurations
    public func validateAll(_ configurations: [String: Any]) throws {
        var errors: [String] = []
        
        for (key, value) in configurations {
            do {
                try validate(key, value: value)
            } catch {
                errors.append("\(key): \(error.localizedDescription)")
            }
        }
        
        if !errors.isEmpty {
            throw ConfigurationError.validationFailed(errors)
        }
    }
}

/// Configuration loader
public final class ConfigurationLoader {
    private let logger = Logger(subsystem: "com.colibridb.config", category: "loader")
    
    public init() {}
    
    /// Loads configurations from environment variables
    public func loadFromEnvironment() -> [String: Any] {
        var configs: [String: Any] = [:]
        
        let envVars = ProcessInfo.processInfo.environment
        
        for (key, value) in envVars {
            if key.hasPrefix("COLIBRIDB_") {
                let configKey = key.dropFirst(10).lowercased().replacingOccurrences(of: "_", with: ".")
                
                // Try to parse as different types
                if let intValue = Int(value) {
                    configs[configKey] = intValue
                } else if let doubleValue = Double(value) {
                    configs[configKey] = doubleValue
                } else if value.lowercased() == "true" {
                    configs[configKey] = true
                } else if value.lowercased() == "false" {
                    configs[configKey] = false
                } else {
                    configs[configKey] = value
                }
            }
        }
        
        logger.info("Loaded \(configs.count) configurations from environment")
        return configs
    }
    
    /// Loads configurations from command line arguments
    public func loadFromCommandLine(_ arguments: [String]) -> [String: Any] {
        var configs: [String: Any] = [:]
        
        var i = 0
        while i < arguments.count {
            let arg = arguments[i]
            
            if arg.hasPrefix("--") {
                let key = String(arg.dropFirst(2))
                
                if i + 1 < arguments.count {
                    let value = arguments[i + 1]
                    
                    // Try to parse as different types
                    if let intValue = Int(value) {
                        configs[key] = intValue
                    } else if let doubleValue = Double(value) {
                        configs[key] = doubleValue
                    } else if value.lowercased() == "true" {
                        configs[key] = true
                    } else if value.lowercased() == "false" {
                        configs[key] = false
                    } else {
                        configs[key] = value
                    }
                    
                    i += 2
                } else {
                    i += 1
                }
            } else {
                i += 1
            }
        }
        
        logger.info("Loaded \(configs.count) configurations from command line")
        return configs
    }
    
    /// Loads configurations from JSON file
    public func loadFromJSONFile(_ path: String) throws -> [String: Any] {
        let data = try Data(contentsOf: URL(fileURLWithPath: path))
        let json = try JSONSerialization.jsonObject(with: data, options: [])
        
        guard let configDict = json as? [String: Any] else {
            throw ConfigurationError.invalidFormat
        }
        
        logger.info("Loaded configurations from JSON file: \(path)")
        return configDict
    }
    
    /// Loads configurations from Property List file
    public func loadFromPlistFile(_ path: String) throws -> [String: Any] {
        let data = try Data(contentsOf: URL(fileURLWithPath: path))
        let plist = try PropertyListSerialization.propertyList(from: data, options: [], format: nil)
        
        guard let configDict = plist as? [String: Any] else {
            throw ConfigurationError.invalidFormat
        }
        
        logger.info("Loaded configurations from Property List file: \(path)")
        return configDict
    }
}
