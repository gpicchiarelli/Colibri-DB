//
//  Logger.swift
//

import Foundation


public struct LoggerEntry {
    public let level: LogLevel
    public let message: String
    public let timestamp: Date
    public let component: String
    public let file: String
    public let function: String
    public let line: Int
    
    public init(level: LogLevel, message: String, component: String, file: String, function: String, line: Int) {
        self.level = level
        self.message = message
        self.timestamp = Date()
        self.component = component
        self.file = file
        self.function = function
        self.line = line
    }
}

public actor Logger {
    public static let shared = Logger()
    
    private var entries: [LoggerEntry] = []
    private var minimumLevel: LogLevel = .info
    private let maxEntries = 10000
    
    private init() {}
    
    public func setMinimumLevel(_ level: LogLevel) {
        minimumLevel = level
    }
    
    public func log(
        level: LogLevel,
        message: String,
        component: String = "Core",
        file: String = #file,
        function: String = #function,
        line: Int = #line
    ) {
        guard level.rawValue >= minimumLevel.rawValue else {
            return
        }
        
        let entry = LoggerEntry(
            level: level,
            message: message,
            component: component,
            file: file,
            function: function,
            line: line
        )
        
        entries.append(entry)
        
        if entries.count > maxEntries {
            entries.removeFirst()
        }
        
        printEntry(entry)
    }
    
    private func printEntry(_ entry: LoggerEntry) {
        let levelStr: String
        switch entry.level {
        case .debug: levelStr = "DEBUG"
        case .info: levelStr = "INFO "
        case .warning: levelStr = "WARN "
        case .error: levelStr = "ERROR"
        case .fatal: levelStr = "FATAL"
        }
        
        let formatter = DateFormatter()
        formatter.dateFormat = "HH:mm:ss.SSS"
        let timeStr = formatter.string(from: entry.timestamp)
        
        print("[\(timeStr)] [\(levelStr)] [\(entry.component)] \(entry.message)")
    }
    
    public func getEntries(level: LogLevel? = nil, component: String? = nil) -> [LoggerEntry] {
        var filtered = entries
        
        if let level = level {
            filtered = filtered.filter { $0.level == level }
        }
        
        if let component = component {
            filtered = filtered.filter { $0.component == component }
        }
        
        return filtered
    }
    
    public func clear() {
        entries.removeAll()
    }
}

public func logDebug(_ message: String, component: String = "Core") {
    Task {
        await Logger.shared.log(level: .debug, message: message, component: component)
    }
}

public func logInfo(_ message: String, component: String = "Core") {
    Task {
        await Logger.shared.log(level: .info, message: message, component: component)
    }
}

public func logWarning(_ message: String, component: String = "Core") {
    Task {
        await Logger.shared.log(level: .warning, message: message, component: component)
    }
}

public func logError(_ message: String, component: String = "Core") {
    Task {
        await Logger.shared.log(level: .error, message: message, component: component)
    }
}

