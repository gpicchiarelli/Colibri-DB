/*
 * Logger.swift
 * ColibrìDB - Professional Logging System
 *
 * A comprehensive logging system for ColibrìDB that replaces all print statements
 * with proper structured logging suitable for production environments.
 *
 * Author: ColibrìDB Team
 * Date: 2025-01-02
 */

import Foundation
import os.log

// MARK: - Log Levels

/// Log levels for ColibrìDB
public enum LogLevel: String, CaseIterable, Codable {
    case trace = "TRACE"
    case debug = "DEBUG"
    case info = "INFO"
    case warning = "WARNING"
    case error = "ERROR"
    case fatal = "FATAL"
    
    var osLogType: OSLogType {
        switch self {
        case .trace, .debug:
            return .debug
        case .info:
            return .info
        case .warning:
            return .default
        case .error:
            return .error
        case .fatal:
            return .fault
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
public enum LogCategory: String, CaseIterable {
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

// MARK: - Log Entry

/// A structured log entry
public struct LogEntry {
    public let timestamp: Date
    public let level: LogLevel
    public let category: LogCategory
    public let message: String
    public let file: String
    public let function: String
    public let line: Int
    public let metadata: [String: Any]?
    
    public init(
        level: LogLevel,
        category: LogCategory,
        message: String,
        file: String = #file,
        function: String = #function,
        line: Int = #line,
        metadata: [String: Any]? = nil
    ) {
        self.timestamp = Date()
        self.level = level
        self.category = category
        self.message = message
        self.file = URL(fileURLWithPath: file).lastPathComponent
        self.function = function
        self.line = line
        self.metadata = metadata
    }
}

// MARK: - Log Formatter

/// Formats log entries for different outputs
public protocol LogFormatter {
    func format(_ entry: LogEntry) -> String
}

/// JSON formatter for structured logging
public struct JSONLogFormatter: LogFormatter {
    public init() {}
    
    public func format(_ entry: LogEntry) -> String {
        let formatter = ISO8601DateFormatter()
        formatter.formatOptions = [.withInternetDateTime, .withFractionalSeconds]
        
        var json: [String: Any] = [
            "timestamp": formatter.string(from: entry.timestamp),
            "level": entry.level.rawValue,
            "category": entry.category.rawValue,
            "message": entry.message,
            "file": entry.file,
            "function": entry.function,
            "line": entry.line
        ]
        
        if let metadata = entry.metadata {
            json["metadata"] = metadata
        }
        
        do {
            let data = try JSONSerialization.data(withJSONObject: json, options: [.prettyPrinted])
            return String(data: data, encoding: .utf8) ?? "{}"
        } catch {
            return "{\"error\": \"Failed to serialize log entry\"}"
        }
    }
}

/// Human-readable formatter for development
public struct HumanReadableLogFormatter: LogFormatter {
    public init() {}
    
    public func format(_ entry: LogEntry) -> String {
        let formatter = DateFormatter()
        formatter.dateFormat = "yyyy-MM-dd HH:mm:ss.SSS"
        
        let timestamp = formatter.string(from: entry.timestamp)
        let level = entry.level.rawValue.padding(toLength: 7, withPad: " ", startingAt: 0)
        let category = "[\(entry.category.rawValue)]"
        let location = "\(entry.file):\(entry.line) \(entry.function)"
        
        var output = "\(timestamp) \(level) \(category) \(location) - \(entry.message)"
        
        if let metadata = entry.metadata, !metadata.isEmpty {
            let metadataStr = metadata.map { "\($0.key)=\($0.value)" }.joined(separator: ", ")
            output += " | \(metadataStr)"
        }
        
        return output
    }
}

// MARK: - Log Handler

/// Handles log entries (console, file, etc.)
public protocol LogHandler {
    func handle(_ entry: LogEntry)
}

/// Console log handler
public struct ConsoleLogHandler: LogHandler {
    private let formatter: LogFormatter
    
    public init(formatter: LogFormatter = HumanReadableLogFormatter()) {
        self.formatter = formatter
    }
    
    public func handle(_ entry: LogEntry) {
        let formattedMessage = formatter.format(entry)
        print(formattedMessage)
    }
}

/// File log handler
public struct FileLogHandler: LogHandler {
    private let fileURL: URL
    private let formatter: LogFormatter
    private let fileHandle: FileHandle?
    
    public init(fileURL: URL, formatter: LogFormatter = JSONLogFormatter()) throws {
        self.fileURL = fileURL
        self.formatter = formatter
        
        // Create directory if it doesn't exist
        try FileManager.default.createDirectory(
            at: fileURL.deletingLastPathComponent(),
            withIntermediateDirectories: true
        )
        
        // Create file if it doesn't exist
        if !FileManager.default.fileExists(atPath: fileURL.path) {
            FileManager.default.createFile(atPath: fileURL.path, contents: nil)
        }
        
        self.fileHandle = try FileHandle(forWritingTo: fileURL)
        self.fileHandle?.seekToEndOfFile()
    }
    
    public func handle(_ entry: LogEntry) {
        let formattedMessage = formatter.format(entry) + "\n"
        
        if let data = formattedMessage.data(using: .utf8) {
            fileHandle?.write(data)
        }
    }
    
    deinit {
        fileHandle?.closeFile()
    }
}

/// OS Log handler for system integration
public struct OSLogHandler: LogHandler {
    private let osLog: OSLog
    private let category: String
    
    public init(subsystem: String = "com.colibridb.database", category: String = "Database") {
        self.osLog = OSLog(subsystem: subsystem, category: category)
        self.category = category
    }
    
    public func handle(_ entry: LogEntry) {
        os_log("%{public}@", log: osLog, type: entry.level.osLogType, entry.message)
    }
}

// MARK: - Logger

/// Main logger for ColibrìDB
public actor Logger {
    private let handlers: [LogHandler]
    private let minLevel: LogLevel
    private let isEnabled: Bool
    
    public init(
        handlers: [LogHandler] = [ConsoleLogHandler()],
        minLevel: LogLevel = .info,
        isEnabled: Bool = true
    ) {
        self.handlers = handlers
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
        
        let entry = LogEntry(
            level: level,
            category: category,
            message: message,
            file: file,
            function: function,
            line: line,
            metadata: metadata
        )
        
        for handler in handlers {
            handler.handle(entry)
        }
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

// MARK: - Global Logger Instance

/// Global logger instance for ColibrìDB
public var colibriLogger: Logger = Logger()

// MARK: - Convenience Functions

/// Global convenience functions for logging
public func logTrace(_ message: String, category: LogCategory = .general, metadata: [String: Any]? = nil, file: String = #file, function: String = #function, line: Int = #line) {
    Task {
        await colibriLogger.trace(message, category: category, metadata: metadata, file: file, function: function, line: line)
    }
}

public func logDebug(_ message: String, category: LogCategory = .general, metadata: [String: Any]? = nil, file: String = #file, function: String = #function, line: Int = #line) {
    Task {
        await colibriLogger.debug(message, category: category, metadata: metadata, file: file, function: function, line: line)
    }
}

public func logInfo(_ message: String, category: LogCategory = .general, metadata: [String: Any]? = nil, file: String = #file, function: String = #function, line: Int = #line) {
    Task {
        await colibriLogger.info(message, category: category, metadata: metadata, file: file, function: function, line: line)
    }
}

public func logWarning(_ message: String, category: LogCategory = .general, metadata: [String: Any]? = nil, file: String = #file, function: String = #function, line: Int = #line) {
    Task {
        await colibriLogger.warning(message, category: category, metadata: metadata, file: file, function: function, line: line)
    }
}

public func logError(_ message: String, category: LogCategory = .general, metadata: [String: Any]? = nil, file: String = #file, function: String = #function, line: Int = #line) {
    Task {
        await colibriLogger.error(message, category: category, metadata: metadata, file: file, function: function, line: line)
    }
}

public func logFatal(_ message: String, category: LogCategory = .general, metadata: [String: Any]? = nil, file: String = #file, function: String = #function, line: Int = #line) {
    Task {
        await colibriLogger.fatal(message, category: category, metadata: metadata, file: file, function: function, line: line)
    }
}