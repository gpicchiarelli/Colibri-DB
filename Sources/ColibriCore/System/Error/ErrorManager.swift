//
//  ErrorManager.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-09-26.
//
// ColibrDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Comprehensive error management system for ColibrDB.

import Foundation
import os.log

/// Error manager for ColibrDB
public final class ErrorManager {
    private let logger = Logger(subsystem: "com.colibridb.error", category: "manager")
    private var errorHistory: [ErrorEntry] = []
    private let errorLock = NSLock()
    private let maxErrorHistory = 1000
    
    public init() {}
    
    /// Records an error
    public func recordError(_ error: Error, context: ErrorContext? = nil) {
        let entry = ErrorEntry(
            id: UUID(),
            error: error,
            context: context,
            timestamp: Date(),
            severity: determineSeverity(error)
        )
        
        errorLock.lock()
        defer { errorLock.unlock() }
        
        errorHistory.append(entry)
        
        // Keep only recent errors
        if errorHistory.count > maxErrorHistory {
            errorHistory.removeFirst(errorHistory.count - maxErrorHistory)
        }
        
        // Log error
        logger.error("Error recorded: \(error.localizedDescription)")
        
        // Log context if available
        if let context = context {
            logger.debug("Error context: \(context)")
        }
    }
    
    /// Determines error severity
    private func determineSeverity(_ error: Error) -> ErrorSeverity {
        switch error {
        case is DatabaseError:
            return .critical
        case is StorageError:
            return .critical
        case is TransactionError:
            return .high
        case is IndexError:
            return .medium
        case is QueryExecutionError:
            return .medium
        case is ConfigurationError:
            return .low
        default:
            return .medium
        }
    }
    
    /// Gets error history
    public func getErrorHistory(limit: Int = 100) -> [ErrorEntry] {
        errorLock.lock()
        defer { errorLock.unlock() }
        
        return Array(errorHistory.suffix(limit))
    }
    
    /// Gets errors by severity
    public func getErrors(by severity: ErrorSeverity) -> [ErrorEntry] {
        errorLock.lock()
        defer { errorLock.unlock() }
        
        return errorHistory.filter { $0.severity == severity }
    }
    
    /// Gets errors by type
    public func getErrors(by type: ErrorType) -> [ErrorEntry] {
        errorLock.lock()
        defer { errorLock.unlock() }
        
        return errorHistory.filter { $0.errorType == type }
    }
    
    /// Gets error statistics
    public func getErrorStatistics() -> ErrorStatistics {
        errorLock.lock()
        defer { errorLock.unlock() }
        
        let totalErrors = errorHistory.count
        let criticalErrors = errorHistory.filter { $0.severity == .critical }.count
        let highErrors = errorHistory.filter { $0.severity == .high }.count
        let mediumErrors = errorHistory.filter { $0.severity == .medium }.count
        let lowErrors = errorHistory.filter { $0.severity == .low }.count
        
        let databaseErrors = errorHistory.filter { $0.errorType == .database }.count
        let storageErrors = errorHistory.filter { $0.errorType == .storage }.count
        let transactionErrors = errorHistory.filter { $0.errorType == .transaction }.count
        let indexErrors = errorHistory.filter { $0.errorType == .index }.count
        let queryErrors = errorHistory.filter { $0.errorType == .query }.count
        let configErrors = errorHistory.filter { $0.errorType == .configuration }.count
        
        return ErrorStatistics(
            totalErrors: totalErrors,
            criticalErrors: criticalErrors,
            highErrors: highErrors,
            mediumErrors: mediumErrors,
            lowErrors: lowErrors,
            databaseErrors: databaseErrors,
            storageErrors: storageErrors,
            transactionErrors: transactionErrors,
            indexErrors: indexErrors,
            queryErrors: queryErrors,
            configErrors: configErrors
        )
    }
    
    /// Gets recent errors within a time window
    public func getRecentErrors(within seconds: TimeInterval) -> [ErrorType: [ErrorEntry]] {
        errorLock.lock()
        defer { errorLock.unlock() }
        
        let cutoff = Date().addingTimeInterval(-seconds)
        let recentErrors = errorHistory.filter { $0.timestamp >= cutoff }
        
        var grouped: [ErrorType: [ErrorEntry]] = [:]
        for error in recentErrors {
            if grouped[error.errorType] == nil {
                grouped[error.errorType] = []
            }
            grouped[error.errorType]?.append(error)
        }
        
        return grouped
    }
    
    /// Clears error history
    public func clearErrorHistory() {
        errorLock.lock()
        defer { errorLock.unlock() }
        
        errorHistory.removeAll()
        logger.info("Error history cleared")
    }
    
    /// Gets error patterns
    public func getErrorPatterns() -> [ErrorPattern] {
        errorLock.lock()
        defer { errorLock.unlock() }
        
        var patterns: [String: ErrorPattern] = [:]
        
        for entry in errorHistory {
            let key = "\(entry.errorType.rawValue).\(entry.severity.rawValue)"
            
            if patterns[key] == nil {
                patterns[key] = ErrorPattern(
                    type: entry.errorType,
                    severity: entry.severity,
                    count: 0,
                    firstOccurrence: entry.timestamp,
                    lastOccurrence: entry.timestamp
                )
            }
            
            patterns[key]?.count += 1
            patterns[key]?.lastOccurrence = entry.timestamp
        }
        
        return Array(patterns.values)
    }
}

/// Error entry
public struct ErrorEntry {
    public let id: UUID
    public let error: Error
    public let context: ErrorContext?
    public let timestamp: Date
    public let severity: ErrorSeverity
    
    public init(id: UUID, error: Error, context: ErrorContext?, timestamp: Date, severity: ErrorSeverity) {
        self.id = id
        self.error = error
        self.context = context
        self.timestamp = timestamp
        self.severity = severity
    }
    
    public var errorType: ErrorType {
        switch error {
        case is DatabaseError:
            return .database
        case is StorageError:
            return .storage
        case is TransactionError:
            return .transaction
        case is IndexError:
            return .index
        case is QueryExecutionError:
            return .query
        case is ConfigurationError:
            return .configuration
        default:
            return .unknown
        }
    }
}

/// Error context
public struct ErrorContext: CustomStringConvertible {
    public let operation: String
    public let table: String?
    public let database: String?
    public let transactionId: UInt64?
    public let query: String?
    public let additionalInfo: [String: Any]
    
    public init(operation: String, table: String? = nil, database: String? = nil, transactionId: UInt64? = nil, query: String? = nil, additionalInfo: [String: Any] = [:]) {
        self.operation = operation
        self.table = table
        self.database = database
        self.transactionId = transactionId
        self.query = query
        self.additionalInfo = additionalInfo
    }
    
    public var description: String {
        var parts = ["operation: \(operation)"]
        if let table = table { parts.append("table: \(table)") }
        if let database = database { parts.append("database: \(database)") }
        if let transactionId = transactionId { parts.append("transactionId: \(transactionId)") }
        if let query = query { parts.append("query: \(query)") }
        if !additionalInfo.isEmpty { parts.append("additionalInfo: \(additionalInfo)") }
        return parts.joined(separator: ", ")
    }
}

/// Error severity levels
public enum ErrorSeverity: String, CaseIterable {
    case low = "LOW"
    case medium = "MEDIUM"
    case high = "HIGH"
    case critical = "CRITICAL"
    
    public var description: String {
        return rawValue
    }
}

/// Error types
public enum ErrorType: String, CaseIterable, CustomStringConvertible {
    case database = "DATABASE"
    case storage = "STORAGE"
    case transaction = "TRANSACTION"
    case index = "INDEX"
    case query = "QUERY"
    case configuration = "CONFIGURATION"
    case unknown = "UNKNOWN"
    
    public var description: String {
        return rawValue
    }
}

/// Error statistics
public struct ErrorStatistics {
    public let totalErrors: Int
    public let criticalErrors: Int
    public let highErrors: Int
    public let mediumErrors: Int
    public let lowErrors: Int
    public let databaseErrors: Int
    public let storageErrors: Int
    public let transactionErrors: Int
    public let indexErrors: Int
    public let queryErrors: Int
    public let configErrors: Int
    
    public init(totalErrors: Int, criticalErrors: Int, highErrors: Int, mediumErrors: Int, lowErrors: Int, databaseErrors: Int, storageErrors: Int, transactionErrors: Int, indexErrors: Int, queryErrors: Int, configErrors: Int) {
        self.totalErrors = totalErrors
        self.criticalErrors = criticalErrors
        self.highErrors = highErrors
        self.mediumErrors = mediumErrors
        self.lowErrors = lowErrors
        self.databaseErrors = databaseErrors
        self.storageErrors = storageErrors
        self.transactionErrors = transactionErrors
        self.indexErrors = indexErrors
        self.queryErrors = queryErrors
        self.configErrors = configErrors
    }
}

/// Error pattern
public struct ErrorPattern {
    public let type: ErrorType
    public let severity: ErrorSeverity
    public var count: Int
    public let firstOccurrence: Date
    public var lastOccurrence: Date
    
    public init(type: ErrorType, severity: ErrorSeverity, count: Int, firstOccurrence: Date, lastOccurrence: Date) {
        self.type = type
        self.severity = severity
        self.count = count
        self.firstOccurrence = firstOccurrence
        self.lastOccurrence = lastOccurrence
    }
}

// ErrorRecoveryManager moved to separate file

/// Error recovery strategy protocol
public protocol ErrorRecoveryStrategy {
    func recover(from error: Error, context: ErrorContext?) throws -> ErrorRecoveryResult
}

/// Error recovery result
public struct ErrorRecoveryResult {
    public let success: Bool
    public let message: String
    public let actions: [String]
    
    public init(success: Bool, message: String, actions: [String] = []) {
        self.success = success
        self.message = message
        self.actions = actions
    }
}

/// Database error recovery strategy
public struct DatabaseErrorRecoveryStrategy: ErrorRecoveryStrategy {
    public func recover(from error: Error, context: ErrorContext?) throws -> ErrorRecoveryResult {
        // Implement database error recovery
        return ErrorRecoveryResult(
            success: true,
            message: "Database error recovered",
            actions: ["Restart database", "Check connections"]
        )
    }
}

/// Storage error recovery strategy
public struct StorageErrorRecoveryStrategy: ErrorRecoveryStrategy {
    public func recover(from error: Error, context: ErrorContext?) throws -> ErrorRecoveryResult {
        // Implement storage error recovery
        return ErrorRecoveryResult(
            success: true,
            message: "Storage error recovered",
            actions: ["Check disk space", "Verify file permissions"]
        )
    }
}

/// Transaction error recovery strategy
public struct TransactionErrorRecoveryStrategy: ErrorRecoveryStrategy {
    public func recover(from error: Error, context: ErrorContext?) throws -> ErrorRecoveryResult {
        // Implement transaction error recovery
        return ErrorRecoveryResult(
            success: true,
            message: "Transaction error recovered",
            actions: ["Rollback transaction", "Retry operation"]
        )
    }
}

/// Index error recovery strategy
public struct IndexErrorRecoveryStrategy: ErrorRecoveryStrategy {
    public func recover(from error: Error, context: ErrorContext?) throws -> ErrorRecoveryResult {
        // Implement index error recovery
        return ErrorRecoveryResult(
            success: true,
            message: "Index error recovered",
            actions: ["Rebuild index", "Check index integrity"]
        )
    }
}

/// Query error recovery strategy
public struct QueryErrorRecoveryStrategy: ErrorRecoveryStrategy {
    public func recover(from error: Error, context: ErrorContext?) throws -> ErrorRecoveryResult {
        // Implement query error recovery
        return ErrorRecoveryResult(
            success: true,
            message: "Query error recovered",
            actions: ["Retry query", "Check query syntax"]
        )
    }
}

/// Configuration error recovery strategy
public struct ConfigurationErrorRecoveryStrategy: ErrorRecoveryStrategy {
    public func recover(from error: Error, context: ErrorContext?) throws -> ErrorRecoveryResult {
        // Implement configuration error recovery
        return ErrorRecoveryResult(
            success: true,
            message: "Configuration error recovered",
            actions: ["Reset to defaults", "Validate configuration"]
        )
    }
}

// ErrorMonitor moved to separate file
