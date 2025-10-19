//
//  ErrorRecovery.swift
//  Based on: spec/ErrorRecovery.tla
//

import Foundation

public enum RecoveryAction {
    case retry
    case abort
    case rollback
    case checkpoint
    case escalate
}

public struct ErrorContext {
    public let error: Error
    public let component: String
    public let timestamp: Date
    public let txID: TxID?
    public let severity: ErrorSeverity
    
    public init(error: Error, component: String, txID: TxID? = nil, severity: ErrorSeverity = .warning) {
        self.error = error
        self.component = component
        self.timestamp = Date()
        self.txID = txID
        self.severity = severity
    }
}

public enum ErrorSeverity {
    case info
    case warning
    case error
    case fatal
}

public actor ErrorRecoveryManager {
    private var errorHistory: [ErrorContext] = []
    private let maxHistorySize = 1000
    private var retryAttempts: [String: Int] = [:]
    private let maxRetries = 3
    
    public init() {}
    
    public func handleError(_ context: ErrorContext) async -> RecoveryAction {
        errorHistory.append(context)
        
        if errorHistory.count > maxHistorySize {
            errorHistory.removeFirst()
        }
        
        switch context.severity {
        case .info:
            return .retry
            
        case .warning:
            let key = "\(context.component):\(type(of: context.error))"
            let attempts = retryAttempts[key, default: 0]
            
            if attempts < maxRetries {
                retryAttempts[key] = attempts + 1
                return .retry
            } else {
                retryAttempts[key] = nil
                return .abort
            }
            
        case .error:
            if context.txID != nil {
                return .rollback
            }
            return .abort
            
        case .fatal:
            return .escalate
        }
    }
    
    public func getErrorHistory() -> [ErrorContext] {
        return errorHistory
    }
    
    public func getErrorCount(component: String) -> Int {
        return errorHistory.filter { $0.component == component }.count
    }
    
    public func clearHistory() {
        errorHistory.removeAll()
        retryAttempts.removeAll()
    }
}

