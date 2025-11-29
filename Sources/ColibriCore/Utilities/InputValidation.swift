//
//  InputValidation.swift
//  ColibrìDB Input Validation & Rate Limiting
//
//  Exit Criteria: input limits, rate limits, no crashes on fuzz
//

import Foundation

// MARK: - Input Limits

/// Input size limits
public enum InputLimits {
    public static let maxQuerySize: Int = 1_048_576  // 1MB
    public static let maxKeySize: Int = 1024  // 1KB
    public static let maxValueSize: Int = 10_485_760  // 10MB
    public static let maxTableNameLength: Int = 128
    public static let maxColumnNameLength: Int = 128
    public static let maxBatchSize: Int = 10_000
}

// MARK: - Input Validator

/// Input validator
public enum InputValidator {
    
    /// Validate SQL query size
    public static func validateQuerySize(_ query: String) throws {
        guard query.utf8.count <= InputLimits.maxQuerySize else {
            throw ValidationError.querySizeTooLarge(query.utf8.count, max: InputLimits.maxQuerySize)
        }
    }
    
    /// Validate key size
    public static func validateKeySize(_ key: Data) throws {
        guard key.count <= InputLimits.maxKeySize else {
            throw ValidationError.keySizeTooLarge(key.count, max: InputLimits.maxKeySize)
        }
    }
    
    /// Validate value size
    public static func validateValueSize(_ value: Data) throws {
        guard value.count <= InputLimits.maxValueSize else {
            throw ValidationError.valueSizeTooLarge(value.count, max: InputLimits.maxValueSize)
        }
    }
    
    /// Validate table name
    public static func validateTableName(_ name: String) throws {
        guard !name.isEmpty else {
            throw ValidationError.emptyTableName
        }
        guard name.count <= InputLimits.maxTableNameLength else {
            throw ValidationError.tableNameTooLong(name.count, max: InputLimits.maxTableNameLength)
        }
        guard name.allSatisfy({ $0.isLetter || $0.isNumber || $0 == "_" }) else {
            throw ValidationError.invalidTableName(name)
        }
    }
    
    /// Validate column name
    public static func validateColumnName(_ name: String) throws {
        guard !name.isEmpty else {
            throw ValidationError.emptyColumnName
        }
        guard name.count <= InputLimits.maxColumnNameLength else {
            throw ValidationError.columnNameTooLong(name.count, max: InputLimits.maxColumnNameLength)
        }
        guard name.allSatisfy({ $0.isLetter || $0.isNumber || $0 == "_" }) else {
            throw ValidationError.invalidColumnName(name)
        }
    }
    
    /// Validate batch size
    public static func validateBatchSize(_ size: Int) throws {
        guard size > 0 else {
            throw ValidationError.invalidBatchSize(size)
        }
        guard size <= InputLimits.maxBatchSize else {
            throw ValidationError.batchSizeTooLarge(size, max: InputLimits.maxBatchSize)
        }
    }
}

// MARK: - Rate Limiter

/// Rate limiter for request throttling
public actor RateLimiter {
    private var requests: [Date] = []
    private let maxRequestsPerSecond: Int
    private let windowSize: TimeInterval = 1.0
    
    // MARK: - Initialization
    
    /// Initialize rate limiter
    /// - Parameter maxRequestsPerSecond: Maximum requests per second
    public init(maxRequestsPerSecond: Int = 1000) {
        self.maxRequestsPerSecond = maxRequestsPerSecond
    }
    
    // MARK: - Public Methods
    
    /// Check if request is allowed
    public func checkLimit() async throws {
        let now = Date()
        
        // Remove old requests
        requests = requests.filter { now.timeIntervalSince($0) < windowSize }
        
        // Check limit
        guard requests.count < maxRequestsPerSecond else {
            throw ValidationError.rateLimitExceeded(requests.count, max: maxRequestsPerSecond)
        }
        
        // Add current request
        requests.append(now)
    }
    
    /// Get current request count in the window
    /// - Returns: Number of requests in current window
    public func getCurrentCount() -> Int {
        return requests.count
    }
}

// MARK: - Error Types

/// Typed validation errors
public enum ValidationError: Error, LocalizedError {
    case querySizeTooLarge(Int, max: Int)
    case keySizeTooLarge(Int, max: Int)
    case valueSizeTooLarge(Int, max: Int)
    case emptyTableName
    case tableNameTooLong(Int, max: Int)
    case invalidTableName(String)
    case emptyColumnName
    case columnNameTooLong(Int, max: Int)
    case invalidColumnName(String)
    case invalidBatchSize(Int)
    case batchSizeTooLarge(Int, max: Int)
    case rateLimitExceeded(Int, max: Int)
    
    public var errorDescription: String? {
        switch self {
        case .querySizeTooLarge(let size, let max):
            return "Query size \(size) bytes exceeds maximum \(max) bytes"
        case .keySizeTooLarge(let size, let max):
            return "Key size \(size) bytes exceeds maximum \(max) bytes"
        case .valueSizeTooLarge(let size, let max):
            return "Value size \(size) bytes exceeds maximum \(max) bytes"
        case .emptyTableName:
            return "Table name cannot be empty"
        case .tableNameTooLong(let length, let max):
            return "Table name length \(length) exceeds maximum \(max) characters"
        case .invalidTableName(let name):
            return "Invalid table name '\(name)': must contain only letters, numbers, and underscores"
        case .emptyColumnName:
            return "Column name cannot be empty"
        case .columnNameTooLong(let length, let max):
            return "Column name length \(length) exceeds maximum \(max) characters"
        case .invalidColumnName(let name):
            return "Invalid column name '\(name)': must contain only letters, numbers, and underscores"
        case .invalidBatchSize(let size):
            return "Invalid batch size: \(size)"
        case .batchSizeTooLarge(let size, let max):
            return "Batch size \(size) exceeds maximum \(max)"
        case .rateLimitExceeded(let current, let max):
            return "Rate limit exceeded: \(current) requests/sec (max: \(max))"
        }
    }
    
    /// Check if error is retryable
    public var isRetryable: Bool {
        switch self {
        case .rateLimitExceeded:
            return true
        default:
            return false
        }
    }
}

/// Typed database errors with retry classification
public enum TypedDBError: Error, LocalizedError {
    // Retryable errors
    case transactionConflict
    case lockTimeout
    case temporaryResourceExhaustion
    case networkTimeout
    
    // Non-retryable errors
    case corruptedData
    case invalidQuery
    case constraintViolation
    case permissionDenied
    case diskFull
    
    public var errorDescription: String? {
        switch self {
        case .transactionConflict:
            return "Transaction conflict detected"
        case .lockTimeout:
            return "Lock acquisition timeout"
        case .temporaryResourceExhaustion:
            return "Temporary resource exhaustion"
        case .networkTimeout:
            return "Network operation timeout"
        case .corruptedData:
            return "Data corruption detected"
        case .invalidQuery:
            return "Invalid SQL query"
        case .constraintViolation:
            return "Constraint violation"
        case .permissionDenied:
            return "Permission denied"
        case .diskFull:
            return "Disk full"
        }
    }
    
    public var isRetryable: Bool {
        switch self {
        case .transactionConflict, .lockTimeout, .temporaryResourceExhaustion, .networkTimeout:
            return true
        case .corruptedData, .invalidQuery, .constraintViolation, .permissionDenied, .diskFull:
            return false
        }
    }
}

