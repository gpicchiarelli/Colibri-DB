//
//  Configurations.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Configuration definitions for the catalog system.

import Foundation
import os.log

// MARK: - Runtime Configuration

/// Represents a runtime configuration parameter
public struct RuntimeConfiguration {
    public let id: UUID
    public let name: String
    public let category: ConfigurationCategory
    public let value: String
    public let dataType: ConfigurationDataType
    public let defaultValue: String
    public let minValue: String?
    public let maxValue: String?
    public let allowedValues: [String]?
    public let description: String
    public let isDynamic: Bool
    public let isReadOnly: Bool
    public let lastModified: Date
    public let modifiedBy: UUID?
    
    public init(id: UUID, name: String, category: ConfigurationCategory, value: String, 
                dataType: ConfigurationDataType, defaultValue: String, minValue: String? = nil, 
                maxValue: String? = nil, allowedValues: [String]? = nil, description: String, 
                isDynamic: Bool = true, isReadOnly: Bool = false, lastModified: Date, 
                modifiedBy: UUID? = nil) {
        self.id = id
        self.name = name
        self.category = category
        self.value = value
        self.dataType = dataType
        self.defaultValue = defaultValue
        self.minValue = minValue
        self.maxValue = maxValue
        self.allowedValues = allowedValues
        self.description = description
        self.isDynamic = isDynamic
        self.isReadOnly = isReadOnly
        self.lastModified = lastModified
        self.modifiedBy = modifiedBy
    }
}

public enum ConfigurationCategory: String, CaseIterable {
    case memory = "MEMORY"
    case storage = "STORAGE"
    case network = "NETWORK"
    case security = "SECURITY"
    case performance = "PERFORMANCE"
    case logging = "LOGGING"
    case backup = "BACKUP"
    case replication = "REPLICATION"
    case monitoring = "MONITORING"
    case maintenance = "MAINTENANCE"
    case compatibility = "COMPATIBILITY"
    case development = "DEVELOPMENT"
}

public enum ConfigurationDataType: String, CaseIterable {
    case string = "STRING"
    case integer = "INTEGER"
    case boolean = "BOOLEAN"
    case double = "DOUBLE"
    case duration = "DURATION"
    case size = "SIZE"
    case percentage = "PERCENTAGE"
    case enumType = "ENUM"
    case list = "LIST"
    case map = "MAP"
}

// MARK: - Eviction Policy

/// Represents an eviction policy configuration
public struct EvictionPolicy {
    public let id: UUID
    public let name: String
    public let type: EvictionPolicyType
    public let target: EvictionTarget
    public let threshold: Double
    public let thresholdUnit: ThresholdUnit
    public let action: EvictionAction
    public let parameters: [String: String]
    public let enabled: Bool
    public let created: Date
    public let lastModified: Date
    
    public init(id: UUID, name: String, type: EvictionPolicyType, target: EvictionTarget, 
                threshold: Double, thresholdUnit: ThresholdUnit, action: EvictionAction, 
                parameters: [String: String] = [:], enabled: Bool = true, created: Date, 
                lastModified: Date) {
        self.id = id
        self.name = name
        self.type = type
        self.target = target
        self.threshold = threshold
        self.thresholdUnit = thresholdUnit
        self.action = action
        self.parameters = parameters
        self.enabled = enabled
        self.created = created
        self.lastModified = lastModified
    }
}

public enum EvictionPolicyType: String, CaseIterable {
    case lru = "LRU"
    case lfu = "LFU"
    case fifo = "FIFO"
    case random = "RANDOM"
    case timeBased = "TIME_BASED"
    case sizeBased = "SIZE_BASED"
    case custom = "CUSTOM"
}

public enum EvictionTarget: String, CaseIterable {
    case bufferPool = "BUFFER_POOL"
    case queryCache = "QUERY_CACHE"
    case indexCache = "INDEX_CACHE"
    case tempTables = "TEMP_TABLES"
    case logFiles = "LOG_FILES"
    case checkpointFiles = "CHECKPOINT_FILES"
    case archiveFiles = "ARCHIVE_FILES"
}

public enum ThresholdUnit: String, CaseIterable {
    case bytes = "BYTES"
    case kilobytes = "KILOBYTES"
    case megabytes = "MEGABYTES"
    case gigabytes = "GIGABYTES"
    case percentage = "PERCENTAGE"
    case count = "COUNT"
    case seconds = "SECONDS"
    case minutes = "MINUTES"
    case hours = "HOURS"
}

public enum EvictionAction: String, CaseIterable {
    case flush = "FLUSH"
    case drop = "DROP"
    case archive = "ARCHIVE"
    case compress = "COMPRESS"
    case move = "MOVE"
    case notify = "NOTIFY"
    case custom = "CUSTOM"
}

// MARK: - Index Configuration

/// Represents index configuration
public struct IndexConfiguration {
    public let id: UUID
    public let indexType: CatalogIndexType
    public let defaultOptions: IndexOptions
    public let compressionSettings: CompressionSettings
    public let memorySettings: ConfigurationMemorySettings
    public let performanceSettings: PerformanceSettings
    public let maintenanceSettings: MaintenanceSettings
    public let enabled: Bool
    public let lastModified: Date
    
    public init(id: UUID, indexType: CatalogIndexType, defaultOptions: IndexOptions, 
                compressionSettings: CompressionSettings, memorySettings: ConfigurationMemorySettings, 
                performanceSettings: PerformanceSettings, maintenanceSettings: MaintenanceSettings, 
                enabled: Bool = true, lastModified: Date) {
        self.id = id
        self.indexType = indexType
        self.defaultOptions = defaultOptions
        self.compressionSettings = compressionSettings
        self.memorySettings = memorySettings
        self.performanceSettings = performanceSettings
        self.maintenanceSettings = maintenanceSettings
        self.enabled = enabled
        self.lastModified = lastModified
    }
}

// MARK: - Compression Settings

/// Represents compression settings
public struct CompressionSettings {
    public let algorithm: CompressionType
    public let level: Int
    public let threshold: UInt64
    public let enabled: Bool
    public let parameters: [String: String]
    
    public init(algorithm: CompressionType, level: Int = 6, threshold: UInt64 = 1024, 
                enabled: Bool = true, parameters: [String: String] = [:]) {
        self.algorithm = algorithm
        self.level = level
        self.threshold = threshold
        self.enabled = enabled
        self.parameters = parameters
    }
}

// MARK: - Memory Settings

/// Represents memory settings
public struct ConfigurationMemorySettings {
    public let maxMemoryBytes: UInt64
    public let pageSizeBytes: UInt32
    public let bufferPoolSize: UInt64
    public let cacheSize: UInt64
    public let tempTableSize: UInt64
    public let sortBufferSize: UInt64
    public let joinBufferSize: UInt64
    public let readBufferSize: UInt64
    public let writeBufferSize: UInt64
    
    public init(maxMemoryBytes: UInt64, pageSizeBytes: UInt32 = 8192, bufferPoolSize: UInt64, 
                cacheSize: UInt64, tempTableSize: UInt64, sortBufferSize: UInt64, 
                joinBufferSize: UInt64, readBufferSize: UInt64, writeBufferSize: UInt64) {
        self.maxMemoryBytes = maxMemoryBytes
        self.pageSizeBytes = pageSizeBytes
        self.bufferPoolSize = bufferPoolSize
        self.cacheSize = cacheSize
        self.tempTableSize = tempTableSize
        self.sortBufferSize = sortBufferSize
        self.joinBufferSize = joinBufferSize
        self.readBufferSize = readBufferSize
        self.writeBufferSize = writeBufferSize
    }
}

// MARK: - Performance Settings

/// Represents performance settings
public struct PerformanceSettings {
    public let maxConnections: UInt32
    public let maxPreparedStatements: UInt32
    public let queryCacheSize: UInt64
    public let queryCacheType: QueryCacheType
    public let slowQueryLog: Bool
    public let slowQueryTime: TimeInterval
    public let profiling: Bool
    public let profilingHistorySize: UInt32
    public let optimizerSettings: OptimizerSettings
    
    public init(maxConnections: UInt32, maxPreparedStatements: UInt32 = 1000, 
                queryCacheSize: UInt64 = 0, queryCacheType: QueryCacheType = .off, 
                slowQueryLog: Bool = false, slowQueryTime: TimeInterval = 2.0, 
                profiling: Bool = false, profilingHistorySize: UInt32 = 100, 
                optimizerSettings: OptimizerSettings) {
        self.maxConnections = maxConnections
        self.maxPreparedStatements = maxPreparedStatements
        self.queryCacheSize = queryCacheSize
        self.queryCacheType = queryCacheType
        self.slowQueryLog = slowQueryLog
        self.slowQueryTime = slowQueryTime
        self.profiling = profiling
        self.profilingHistorySize = profilingHistorySize
        self.optimizerSettings = optimizerSettings
    }
}

public enum QueryCacheType: String, CaseIterable {
    case off = "OFF"
    case on = "ON"
    case demand = "DEMAND"
}

// MARK: - Optimizer Settings

/// Represents optimizer settings
public struct OptimizerSettings {
    public let enableCostBasedOptimizer: Bool
    public let enableStatistics: Bool
    public let enableIndexHints: Bool
    public let enableJoinOptimization: Bool
    public let enableSubqueryOptimization: Bool
    public let enableOrderByOptimization: Bool
    public let enableGroupByOptimization: Bool
    public let enableDistinctOptimization: Bool
    public let maxJoinSize: UInt64
    public let maxSelectSize: UInt64
    public let maxSortLength: UInt32
    public let maxGroupConcatLength: UInt32
    
    public init(enableCostBasedOptimizer: Bool = true, enableStatistics: Bool = true, 
                enableIndexHints: Bool = true, enableJoinOptimization: Bool = true, 
                enableSubqueryOptimization: Bool = true, enableOrderByOptimization: Bool = true, 
                enableGroupByOptimization: Bool = true, enableDistinctOptimization: Bool = true, 
                maxJoinSize: UInt64 = 1000000, maxSelectSize: UInt64 = 1000000, 
                maxSortLength: UInt32 = 1024, maxGroupConcatLength: UInt32 = 1024) {
        self.enableCostBasedOptimizer = enableCostBasedOptimizer
        self.enableStatistics = enableStatistics
        self.enableIndexHints = enableIndexHints
        self.enableJoinOptimization = enableJoinOptimization
        self.enableSubqueryOptimization = enableSubqueryOptimization
        self.enableOrderByOptimization = enableOrderByOptimization
        self.enableGroupByOptimization = enableGroupByOptimization
        self.enableDistinctOptimization = enableDistinctOptimization
        self.maxJoinSize = maxJoinSize
        self.maxSelectSize = maxSelectSize
        self.maxSortLength = maxSortLength
        self.maxGroupConcatLength = maxGroupConcatLength
    }
}

// MARK: - Maintenance Settings

/// Represents maintenance settings
public struct MaintenanceSettings {
    public let autoVacuum: Bool
    public let vacuumInterval: TimeInterval
    public let vacuumThreshold: Double
    public let autoAnalyze: Bool
    public let analyzeInterval: TimeInterval
    public let autoReindex: Bool
    public let reindexInterval: TimeInterval
    public let checkpointInterval: TimeInterval
    public let walRetention: TimeInterval
    public let logRotation: Bool
    public let logRotationSize: UInt64
    public let logRotationCount: UInt32
    
    public init(autoVacuum: Bool = true, vacuumInterval: TimeInterval = 3600, 
                vacuumThreshold: Double = 0.1, autoAnalyze: Bool = true, 
                analyzeInterval: TimeInterval = 1800, autoReindex: Bool = false, 
                reindexInterval: TimeInterval = 86400, checkpointInterval: TimeInterval = 300, 
                walRetention: TimeInterval = 3600, logRotation: Bool = true, 
                logRotationSize: UInt64 = 100 * 1024 * 1024, logRotationCount: UInt32 = 10) {
        self.autoVacuum = autoVacuum
        self.vacuumInterval = vacuumInterval
        self.vacuumThreshold = vacuumThreshold
        self.autoAnalyze = autoAnalyze
        self.analyzeInterval = analyzeInterval
        self.autoReindex = autoReindex
        self.reindexInterval = reindexInterval
        self.checkpointInterval = checkpointInterval
        self.walRetention = walRetention
        self.logRotation = logRotation
        self.logRotationSize = logRotationSize
        self.logRotationCount = logRotationCount
    }
}

// MARK: - Security Configuration

/// Represents security configuration
public struct SecurityConfiguration {
    public let id: UUID
    public let passwordPolicy: PasswordPolicy
    public let sessionSettings: SessionSettings
    public let encryptionSettings: EncryptionSettings
    public let auditSettings: AuditSettings
    public let firewallSettings: FirewallSettings
    public let sslSettings: SSLSettings
    public let lastModified: Date
    
    public init(id: UUID, passwordPolicy: PasswordPolicy, sessionSettings: SessionSettings, 
                encryptionSettings: EncryptionSettings, auditSettings: AuditSettings, 
                firewallSettings: FirewallSettings, sslSettings: SSLSettings, lastModified: Date) {
        self.id = id
        self.passwordPolicy = passwordPolicy
        self.sessionSettings = sessionSettings
        self.encryptionSettings = encryptionSettings
        self.auditSettings = auditSettings
        self.firewallSettings = firewallSettings
        self.sslSettings = sslSettings
        self.lastModified = lastModified
    }
}

// MARK: - Password Policy

/// Represents password policy
public struct PasswordPolicy {
    public let minLength: Int
    public let maxLength: Int
    public let requireUppercase: Bool
    public let requireLowercase: Bool
    public let requireNumbers: Bool
    public let requireSpecialChars: Bool
    public let maxAge: TimeInterval
    public let historyCount: Int
    public let lockoutAttempts: Int
    public let lockoutDuration: TimeInterval
    
    public init(minLength: Int = 8, maxLength: Int = 128, requireUppercase: Bool = true, 
                requireLowercase: Bool = true, requireNumbers: Bool = true, 
                requireSpecialChars: Bool = true, maxAge: TimeInterval = 90 * 24 * 3600, 
                historyCount: Int = 5, lockoutAttempts: Int = 5, 
                lockoutDuration: TimeInterval = 30 * 60) {
        self.minLength = minLength
        self.maxLength = maxLength
        self.requireUppercase = requireUppercase
        self.requireLowercase = requireLowercase
        self.requireNumbers = requireNumbers
        self.requireSpecialChars = requireSpecialChars
        self.maxAge = maxAge
        self.historyCount = historyCount
        self.lockoutAttempts = lockoutAttempts
        self.lockoutDuration = lockoutDuration
    }
}

// MARK: - Session Settings

/// Represents session settings
public struct SessionSettings {
    public let timeout: TimeInterval
    public let maxSessions: UInt32
    public let idleTimeout: TimeInterval
    public let absoluteTimeout: TimeInterval
    public let allowConcurrentSessions: Bool
    public let maxConcurrentSessions: UInt32
    
    public init(timeout: TimeInterval = 30 * 60, maxSessions: UInt32 = 1000, 
                idleTimeout: TimeInterval = 15 * 60, absoluteTimeout: TimeInterval = 8 * 3600, 
                allowConcurrentSessions: Bool = true, maxConcurrentSessions: UInt32 = 5) {
        self.timeout = timeout
        self.maxSessions = maxSessions
        self.idleTimeout = idleTimeout
        self.absoluteTimeout = absoluteTimeout
        self.allowConcurrentSessions = allowConcurrentSessions
        self.maxConcurrentSessions = maxConcurrentSessions
    }
}

// MARK: - Encryption Settings

/// Represents encryption settings
public struct EncryptionSettings {
    public let enabled: Bool
    public let algorithm: EncryptionAlgorithm
    public let keySize: Int
    public let keyRotationInterval: TimeInterval
    public let encryptDataAtRest: Bool
    public let encryptDataInTransit: Bool
    public let encryptLogs: Bool
    public let encryptBackups: Bool
    
    public init(enabled: Bool = false, algorithm: EncryptionAlgorithm = .aes256, 
                keySize: Int = 256, keyRotationInterval: TimeInterval = 90 * 24 * 3600, 
                encryptDataAtRest: Bool = false, encryptDataInTransit: Bool = true, 
                encryptLogs: Bool = false, encryptBackups: Bool = true) {
        self.enabled = enabled
        self.algorithm = algorithm
        self.keySize = keySize
        self.keyRotationInterval = keyRotationInterval
        self.encryptDataAtRest = encryptDataAtRest
        self.encryptDataInTransit = encryptDataInTransit
        self.encryptLogs = encryptLogs
        self.encryptBackups = encryptBackups
    }
}

public enum EncryptionAlgorithm: String, CaseIterable {
    case aes128 = "AES128"
    case aes256 = "AES256"
    case chacha20 = "CHACHA20"
    case rsa2048 = "RSA2048"
    case rsa4096 = "RSA4096"
}

// MARK: - Audit Settings

/// Represents audit settings
public struct AuditSettings {
    public let enabled: Bool
    public let logLevel: AuditLogLevel
    public let logEvents: [AuditEventType]
    public let retentionPeriod: TimeInterval
    public let maxLogSize: UInt64
    public let compressLogs: Bool
    public let encryptLogs: Bool
    
    public init(enabled: Bool = true, logLevel: AuditLogLevel = .medium, 
                logEvents: [AuditEventType] = [.login, .logout, .query, .dataModification], 
                retentionPeriod: TimeInterval = 365 * 24 * 3600, maxLogSize: UInt64 = 100 * 1024 * 1024, 
                compressLogs: Bool = true, encryptLogs: Bool = false) {
        self.enabled = enabled
        self.logLevel = logLevel
        self.logEvents = logEvents
        self.retentionPeriod = retentionPeriod
        self.maxLogSize = maxLogSize
        self.compressLogs = compressLogs
        self.encryptLogs = encryptLogs
    }
}

public enum AuditLogLevel: String, CaseIterable {
    case low = "LOW"
    case medium = "MEDIUM"
    case high = "HIGH"
    case critical = "CRITICAL"
}

public enum AuditEventType: String, CaseIterable {
    case login = "LOGIN"
    case logout = "LOGOUT"
    case query = "QUERY"
    case dataModification = "DATA_MODIFICATION"
    case schemaChange = "SCHEMA_CHANGE"
    case permissionChange = "PERMISSION_CHANGE"
    case configurationChange = "CONFIGURATION_CHANGE"
    case systemEvent = "SYSTEM_EVENT"
    case error = "ERROR"
}

// MARK: - Firewall Settings

/// Represents firewall settings
public struct FirewallSettings {
    public let enabled: Bool
    public let allowLocalhost: Bool
    public let allowedIPs: [String]
    public let blockedIPs: [String]
    public let allowedNetworks: [String]
    public let blockedNetworks: [String]
    public let maxConnectionsPerIP: UInt32
    public let connectionRateLimit: UInt32
    
    public init(enabled: Bool = false, allowLocalhost: Bool = true, allowedIPs: [String] = [], 
                blockedIPs: [String] = [], allowedNetworks: [String] = [], 
                blockedNetworks: [String] = [], maxConnectionsPerIP: UInt32 = 10, 
                connectionRateLimit: UInt32 = 100) {
        self.enabled = enabled
        self.allowLocalhost = allowLocalhost
        self.allowedIPs = allowedIPs
        self.blockedIPs = blockedIPs
        self.allowedNetworks = allowedNetworks
        self.blockedNetworks = blockedNetworks
        self.maxConnectionsPerIP = maxConnectionsPerIP
        self.connectionRateLimit = connectionRateLimit
    }
}

// MARK: - SSL Settings

/// Represents SSL settings
public struct SSLSettings {
    public let enabled: Bool
    public let requireSSL: Bool
    public let certificatePath: String?
    public let privateKeyPath: String?
    public let caCertificatePath: String?
    public let cipherSuites: [String]
    public let protocolVersion: SSLProtocolVersion
    public let verifyMode: SSLVerifyMode
    
    public init(enabled: Bool = false, requireSSL: Bool = false, certificatePath: String? = nil, 
                privateKeyPath: String? = nil, caCertificatePath: String? = nil, 
                cipherSuites: [String] = [], protocolVersion: SSLProtocolVersion = .tls12, 
                verifyMode: SSLVerifyMode = .none) {
        self.enabled = enabled
        self.requireSSL = requireSSL
        self.certificatePath = certificatePath
        self.privateKeyPath = privateKeyPath
        self.caCertificatePath = caCertificatePath
        self.cipherSuites = cipherSuites
        self.protocolVersion = protocolVersion
        self.verifyMode = verifyMode
    }
}

public enum SSLProtocolVersion: String, CaseIterable {
    case tls10 = "TLS1.0"
    case tls11 = "TLS1.1"
    case tls12 = "TLS1.2"
    case tls13 = "TLS1.3"
}

public enum SSLVerifyMode: String, CaseIterable {
    case none = "NONE"
    case peer = "PEER"
    case failIfNoPeerCert = "FAIL_IF_NO_PEER_CERT"
    case clientOnce = "CLIENT_ONCE"
}

// MARK: - Configuration Manager

/// Manages configurations in the catalog
public class CatalogConfigurationManager {
    private let database: Database
    private let logger = Logger(subsystem: "com.colibridb.catalog", category: "configuration")
    
    public init(database: Database) {
        self.database = database
    }
    
    // MARK: - Runtime Configuration
    
    /// Gets a runtime configuration value
    public func getRuntimeConfiguration(_ name: String) throws -> RuntimeConfiguration? {
        // Implementation would query runtime configuration table
        return nil
    }
    
    /// Sets a runtime configuration value
    public func setRuntimeConfiguration(_ config: RuntimeConfiguration) throws {
        logger.info("Setting runtime configuration: \(config.name) = \(config.value)")
        // Implementation would update runtime configuration table
    }
    
    /// Gets all runtime configurations
    public func getAllRuntimeConfigurations() throws -> [RuntimeConfiguration] {
        // Implementation would query runtime configuration table
        return []
    }
    
    /// Gets runtime configurations by category
    public func getRuntimeConfigurations(category: ConfigurationCategory) throws -> [RuntimeConfiguration] {
        // Implementation would query runtime configuration table
        return []
    }
    
    // MARK: - Eviction Policy
    
    /// Gets eviction policies
    public func getEvictionPolicies() throws -> [EvictionPolicy] {
        // Implementation would query eviction policy table
        return []
    }
    
    /// Creates an eviction policy
    public func createEvictionPolicy(_ policy: EvictionPolicy) throws {
        logger.info("Creating eviction policy: \(policy.name)")
        // Implementation would insert into eviction policy table
    }
    
    /// Updates an eviction policy
    public func updateEvictionPolicy(_ policy: EvictionPolicy) throws {
        logger.info("Updating eviction policy: \(policy.name)")
        // Implementation would update eviction policy table
    }
    
    /// Deletes an eviction policy
    public func deleteEvictionPolicy(_ policyId: UUID) throws {
        logger.info("Deleting eviction policy: \(policyId)")
        // Implementation would delete from eviction policy table
    }
    
    // MARK: - Index Configuration
    
    /// Gets index configurations
    public func getIndexConfigurations() throws -> [IndexConfiguration] {
        // Implementation would query index configuration table
        return []
    }
    
    /// Gets index configuration for a specific type
    public func getIndexConfiguration(for indexType: IndexType) throws -> IndexConfiguration? {
        // Implementation would query index configuration table
        return nil
    }
    
    /// Updates index configuration
    public func updateIndexConfiguration(_ config: IndexConfiguration) throws {
        logger.info("Updating index configuration for: \(config.indexType.rawValue)")
        // Implementation would update index configuration table
    }
    
    // MARK: - Security Configuration
    
    /// Gets security configuration
    public func getSecurityConfiguration() throws -> SecurityConfiguration? {
        // Implementation would query security configuration table
        return nil
    }
    
    /// Updates security configuration
    public func updateSecurityConfiguration(_ config: SecurityConfiguration) throws {
        logger.info("Updating security configuration")
        // Implementation would update security configuration table
    }
    
    // MARK: - Configuration Validation
    
    /// Validates a configuration value
    public func validateConfiguration(_ config: RuntimeConfiguration) throws -> Bool {
        // Implementation would validate configuration value
        return true
    }
    
    /// Gets configuration recommendations
    public func getConfigurationRecommendations() throws -> [ConfigurationRecommendation] {
        // Implementation would analyze current configuration and provide recommendations
        return []
    }
}

// MARK: - Configuration Recommendation

/// Represents a configuration recommendation
public struct ConfigurationRecommendation {
    public let name: String
    public let currentValue: String
    public let recommendedValue: String
    public let reason: String
    public let priority: RecommendationPriority
    public let category: ConfigurationCategory
    
    public init(name: String, currentValue: String, recommendedValue: String, reason: String, 
                priority: RecommendationPriority, category: ConfigurationCategory) {
        self.name = name
        self.currentValue = currentValue
        self.recommendedValue = recommendedValue
        self.reason = reason
        self.priority = priority
        self.category = category
    }
}
