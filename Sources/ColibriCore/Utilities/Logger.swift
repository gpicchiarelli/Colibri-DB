/*
 * Logger.swift
 * ColibrìDB - Professional Logging System
 *
 * A comprehensive logging system for ColibrìDB using swift-log
 *
 * Author: ColibrìDB Team
 * Date: 2025-01-02
 */

import Foundation
import Logging

// MARK: - Log Levels

/// Log levels for ColibrìDB
public enum LogLevel: String, CaseIterable, Codable, Sendable {
    case trace = "TRACE"
    case debug = "DEBUG"
    case info = "INFO"
    case warning = "WARNING"
    case error = "ERROR"
    case fatal = "FATAL"
    
    var swiftLogLevel: Logging.Logger.Level {
        switch self {
        case .trace: return .trace
        case .debug: return .debug
        case .info: return .info
        case .warning: return .warning
        case .error: return .error
        case .fatal: return .critical
        }
    }
    
    var priority: Int {
        switch self {
        case .trace: return 0
        case .debug: return 1
        case .info: return 2
        case .warning: return 3
        case .error: return 4
        case .fatal: return 5
        }
    }
}

// MARK: - Log Categories

/// Log categories for different subsystems
public enum LogCategory: String, CaseIterable, Codable, Sendable {
    case database = "Database"
    case transaction = "Transaction"
    case storage = "Storage"
    case query = "Query"
    case recovery = "Recovery"
    case security = "Security"
    case network = "Network"
    case performance = "Performance"
    case system = "System"
    case testing = "Testing"
    case distributed = "Distributed"
    case consensus = "Consensus"
    case replication = "Replication"
    case sharding = "Sharding"
    case monitoring = "Monitoring"
    case backup = "Backup"
    case optimization = "Optimization"
    case clock = "Clock"
    case policy = "Policy"
    case platform = "Platform"
    case general = "General"
}

// MARK: - Logger

/// Main logger for ColibrìDB (wrapper around swift-log)
public actor Logger {
    private let swiftLogger: Logging.Logger
    private let minLevel: LogLevel
    private let isEnabled: Bool
    
    public init(
        label: String = "com.colibridb",
        minLevel: LogLevel = .info,
        isEnabled: Bool = true
    ) {
        var logger = Logging.Logger(label: label)
        logger.logLevel = minLevel.swiftLogLevel
        self.swiftLogger = logger
        self.minLevel = minLevel
        self.isEnabled = isEnabled
    }
    
    public func log(
        _ level: LogLevel,
        category: LogCategory = .general,
        _ message: String,
        file: String = #file,
        function: String = #function,
        line: Int = #line,
        metadata: [String: Any]? = nil
    ) {
        guard isEnabled && level.priority >= minLevel.priority else { return }
        
        var logMetadata: Logging.Logger.Metadata = [
            "category": "\(category.rawValue)",
            "file": "\(file)",
            "function": "\(function)",
            "line": "\(line)"
        ]
        
        if let metadata = metadata {
            for (key, value) in metadata {
                logMetadata[key] = "\(value)"
            }
        }
        
        swiftLogger.log(
            level: level.swiftLogLevel,
            "\(message)",
            metadata: logMetadata,
            file: file,
            function: function,
            line: UInt(line)
        )
    }
    
    // Convenience methods
    public func trace(_ message: String, category: LogCategory = .general, metadata: [String: Any]? = nil, file: String = #file, function: String = #function, line: Int = #line) {
        log(.trace, category: category, message, file: file, function: function, line: line, metadata: metadata)
    }
    
    public func debug(_ message: String, category: LogCategory = .general, metadata: [String: Any]? = nil, file: String = #file, function: String = #function, line: Int = #line) {
        log(.debug, category: category, message, file: file, function: function, line: line, metadata: metadata)
    }
    
    public func info(_ message: String, category: LogCategory = .general, metadata: [String: Any]? = nil, file: String = #file, function: String = #function, line: Int = #line) {
        log(.info, category: category, message, file: file, function: function, line: line, metadata: metadata)
    }
    
    public func warning(_ message: String, category: LogCategory = .general, metadata: [String: Any]? = nil, file: String = #file, function: String = #function, line: Int = #line) {
        log(.warning, category: category, message, file: file, function: function, line: line, metadata: metadata)
    }
    
    public func error(_ message: String, category: LogCategory = .general, metadata: [String: Any]? = nil, file: String = #file, function: String = #function, line: Int = #line) {
        log(.error, category: category, message, file: file, function: function, line: line, metadata: metadata)
    }
    
    public func fatal(_ message: String, category: LogCategory = .general, metadata: [String: Any]? = nil, file: String = #file, function: String = #function, line: Int = #line) {
        log(.fatal, category: category, message, file: file, function: function, line: line, metadata: metadata)
    }
}

// MARK: - Type Alias for Compatibility

/// Type alias for ColibriLogger to maintain compatibility with existing code
public typealias ColibriLogger = Logger

// MARK: - Global Logger Instance

/// Global logger instance for ColibrìDB
@MainActor
public var colibriLogger: Logger = Logger()

// MARK: - Convenience Functions

/// Global convenience functions for logging
public func logTrace(_ message: String, category: LogCategory = .general, metadata: [String: Any]? = nil, file: String = #file, function: String = #function, line: Int = #line) {
    let sendableMetadata = metadata.map { $0.mapValues { String(describing: $0) } }
    Task { @MainActor in
        await colibriLogger.trace(message, category: category, metadata: sendableMetadata, file: file, function: function, line: line)
    }
}

public func logDebug(_ message: String, category: LogCategory = .general, metadata: [String: Any]? = nil, file: String = #file, function: String = #function, line: Int = #line) {
    let sendableMetadata = metadata.map { $0.mapValues { String(describing: $0) } }
    Task { @MainActor in
        await colibriLogger.debug(message, category: category, metadata: sendableMetadata, file: file, function: function, line: line)
    }
}

public func logInfo(_ message: String, category: LogCategory = .general, metadata: [String: Any]? = nil, file: String = #file, function: String = #function, line: Int = #line) {
    let sendableMetadata = metadata.map { $0.mapValues { String(describing: $0) } }
    Task { @MainActor in
        await colibriLogger.info(message, category: category, metadata: sendableMetadata, file: file, function: function, line: line)
    }
}

public func logWarning(_ message: String, category: LogCategory = .general, metadata: [String: Any]? = nil, file: String = #file, function: String = #function, line: Int = #line) {
    let sendableMetadata = metadata.map { $0.mapValues { String(describing: $0) } }
    Task { @MainActor in
        await colibriLogger.warning(message, category: category, metadata: sendableMetadata, file: file, function: function, line: line)
    }
}

public func logError(_ message: String, category: LogCategory = .general, metadata: [String: Any]? = nil, file: String = #file, function: String = #function, line: Int = #line) {
    let sendableMetadata = metadata.map { $0.mapValues { String(describing: $0) } }
    Task { @MainActor in
        await colibriLogger.error(message, category: category, metadata: sendableMetadata, file: file, function: function, line: line)
    }
}

public func logFatal(_ message: String, category: LogCategory = .general, metadata: [String: Any]? = nil, file: String = #file, function: String = #function, line: Int = #line) {
    let sendableMetadata = metadata.map { $0.mapValues { String(describing: $0) } }
    Task { @MainActor in
        await colibriLogger.fatal(message, category: category, metadata: sendableMetadata, file: file, function: function, line: line)
    }
}
