//
//  Logger.swift
//  coldb-server
//
//  Created by Giacomo Picchiarelli on 2025-09-27.
//
// Theme: Structured logging system for the database server

import Foundation

// MARK: - Logger

public final class Logger {
    private let level: LogLevel
    private let formatter: LogFormatter
    private let output: LogOutput
    
    public init(level: LogLevel = .info, formatter: LogFormatter = DefaultLogFormatter(), output: LogOutput = ConsoleLogOutput()) {
        self.level = level
        self.formatter = formatter
        self.output = output
    }
    
    public func debug(_ message: String, file: String = #file, function: String = #function, line: Int = #line) {
        log(level: .debug, message: message, file: file, function: function, line: line)
    }
    
    public func info(_ message: String, file: String = #file, function: String = #function, line: Int = #line) {
        log(level: .info, message: message, file: file, function: function, line: line)
    }
    
    public func warning(_ message: String, file: String = #file, function: String = #function, line: Int = #line) {
        log(level: .warning, message: message, file: file, function: function, line: line)
    }
    
    public func error(_ message: String, file: String = #file, function: String = #function, line: Int = #line) {
        log(level: .error, message: message, file: file, function: function, line: line)
    }
    
    private func log(level: LogLevel, message: String, file: String, function: String, line: Int) {
        guard level.priority >= self.level.priority else { return }
        
        let logEntry = LogEntry(
            level: level,
            message: message,
            timestamp: Date(),
            file: file,
            function: function,
            line: line
        )
        
        let formattedMessage = formatter.format(entry: logEntry)
        output.write(formattedMessage)
    }
}

// MARK: - Log Entry

public struct LogEntry {
    public let level: LogLevel
    public let message: String
    public let timestamp: Date
    public let file: String
    public let function: String
    public let line: Int
    
    public init(level: LogLevel, message: String, timestamp: Date, file: String, function: String, line: Int) {
        self.level = level
        self.message = message
        self.timestamp = timestamp
        self.file = file
        self.function = function
        self.line = line
    }
}

// MARK: - Log Formatter

public protocol LogFormatter {
    func format(entry: LogEntry) -> String
}

public struct DefaultLogFormatter: LogFormatter {
    private let dateFormatter: DateFormatter
    
    public init() {
        self.dateFormatter = DateFormatter()
        self.dateFormatter.dateFormat = "yyyy-MM-dd HH:mm:ss.SSS"
    }
    
    public func format(entry: LogEntry) -> String {
        let timestamp = dateFormatter.string(from: entry.timestamp)
        let filename = URL(fileURLWithPath: entry.file).lastPathComponent
        let level = entry.level.rawValue.padding(toLength: 7, withPad: " ", startingAt: 0)
        
        return "[\(timestamp)] \(level) [\(filename):\(entry.line)] \(entry.function) - \(entry.message)"
    }
}

public struct JSONLogFormatter: LogFormatter {
    private let encoder: JSONEncoder
    
    public init() {
        self.encoder = JSONEncoder()
        self.encoder.dateEncodingStrategy = .iso8601
    }
    
    public func format(entry: LogEntry) -> String {
        let logData = LogData(
            timestamp: entry.timestamp,
            level: entry.level.rawValue,
            message: entry.message,
            file: entry.file,
            function: entry.function,
            line: entry.line
        )
        
        do {
            let data = try encoder.encode(logData)
            return String(data: data, encoding: .utf8) ?? ""
        } catch {
            return "{\"error\":\"Failed to encode log entry\"}"
        }
    }
}

private struct LogData: Codable {
    let timestamp: Date
    let level: String
    let message: String
    let file: String
    let function: String
    let line: Int
}

// MARK: - Log Output

public protocol LogOutput {
    func write(_ message: String)
}

public struct ConsoleLogOutput: LogOutput {
    public init() {}
    
    public func write(_ message: String) {
        print(message)
    }
}

public final class FileLogOutput: LogOutput {
    private let fileHandle: FileHandle
    private let queue: DispatchQueue
    
    public init(filePath: String) throws {
        let url = URL(fileURLWithPath: filePath)
        
        // Create directory if it doesn't exist
        try FileManager.default.createDirectory(
            at: url.deletingLastPathComponent(),
            withIntermediateDirectories: true
        )
        
        // Create file if it doesn't exist
        if !FileManager.default.fileExists(atPath: filePath) {
            FileManager.default.createFile(atPath: filePath, contents: nil)
        }
        
        self.fileHandle = try FileHandle(forWritingTo: url)
        self.queue = DispatchQueue(label: "com.colibridb.logger", qos: .utility)
    }
    
    public func write(_ message: String) {
        queue.async {
            let data = (message + "\n").data(using: .utf8) ?? Data()
            self.fileHandle.write(data)
        }
    }
    
    deinit {
        fileHandle.closeFile()
    }
}

// MARK: - Global Logger Instance

@MainActor
public let logger = Logger()

// MARK: - Convenience Functions

@MainActor
public func logDebug(_ message: String, file: String = #file, function: String = #function, line: Int = #line) {
    logger.debug(message, file: file, function: function, line: line)
}

@MainActor
public func logInfo(_ message: String, file: String = #file, function: String = #function, line: Int = #line) {
    logger.info(message, file: file, function: function, line: line)
}

@MainActor
public func logWarning(_ message: String, file: String = #file, function: String = #function, line: Int = #line) {
    logger.warning(message, file: file, function: function, line: line)
}

@MainActor
public func logError(_ message: String, file: String = #file, function: String = #function, line: Int = #line) {
    logger.error(message, file: file, function: function, line: line)
}
