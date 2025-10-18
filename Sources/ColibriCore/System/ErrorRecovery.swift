//
//  ErrorRecovery.swift
//  ColibrDB
//
//  Issue #22 - Error Recovery System
//  Created by Giacomo Picchiarelli on 2025-10-18.
//
// ColibrDB — BSD 3-Clause License

import Foundation

// MARK: - Error Severity Classification

/// Classifies errors by severity and recoverability
public enum ErrorSeverity {
    case retriable      // Can be retried automatically
    case userAction     // Requires user intervention
    case fatal          // Must abort operation
}

/// Classifies specific error types
public struct ErrorClassifier {
    
    /// Classify a database error
    public static func classify(_ error: Error) -> ErrorSeverity {
        if let dbError = error as? DBError {
            switch dbError {
            // Retriable errors
            case .lockTimeout:
                return .retriable
            case .transactionAborted:
                return .retriable
            case .deadlock:
                return .retriable
                
            // User action required
            case .notFound:
                return .userAction
            case .alreadyExists:
                return .userAction
            case .invalidArgument:
                return .userAction
            case .config:
                return .userAction
                
            // Fatal errors
            case .corruption:
                return .fatal
            case .io:
                return .fatal
                
            default:
                return .userAction
            }
        }
        
        // Network errors are typically retriable
        if (error as NSError).domain == NSURLErrorDomain {
            return .retriable
        }
        
        // Default to user action
        return .userAction
    }
}

// MARK: - Backoff Strategy

/// Strategy for retry backoff
public enum BackoffStrategy {
    case constant(TimeInterval)
    case linear(initial: TimeInterval, increment: TimeInterval)
    case exponential(initial: TimeInterval, multiplier: Double)
    case fibonacci(initial: TimeInterval)
    
    func delay(for attempt: Int) -> TimeInterval {
        switch self {
        case .constant(let interval):
            return interval
            
        case .linear(let initial, let increment):
            return initial + (TimeInterval(attempt) * increment)
            
        case .exponential(let initial, let multiplier):
            return initial * pow(multiplier, Double(attempt))
            
        case .fibonacci(let initial):
            let fib = fibonacci(attempt)
            return initial * TimeInterval(fib)
        }
    }
    
    private func fibonacci(_ n: Int) -> Int {
        if n <= 1 { return 1 }
        var a = 1, b = 1
        for _ in 2...n {
            let temp = a + b
            a = b
            b = temp
        }
        return b
    }
}

// MARK: - Circuit Breaker

/// Circuit breaker pattern implementation
public final class CircuitBreaker {
    public enum State {
        case closed      // Normal operation
        case open        // Failing, reject requests
        case halfOpen    // Testing if recovered
    }
    
    private var state: State = .closed
    private var failureCount: Int = 0
    private var successCount: Int = 0
    private var lastFailureTime: Date?
    private let lock = NSLock()
    
    // Configuration
    public let failureThreshold: Int
    public let successThreshold: Int
    public let timeout: TimeInterval
    
    public init(
        failureThreshold: Int = 5,
        successThreshold: Int = 2,
        timeout: TimeInterval = 60.0
    ) {
        self.failureThreshold = failureThreshold
        self.successThreshold = successThreshold
        self.timeout = timeout
    }
    
    /// Check if request should be allowed
    public func allowRequest() -> Bool {
        lock.lock()
        defer { lock.unlock() }
        
        switch state {
        case .closed:
            return true
            
        case .open:
            // Check if timeout has passed
            if let lastFailure = lastFailureTime,
               Date().timeIntervalSince(lastFailure) > timeout {
                state = .halfOpen
                successCount = 0
                return true
            }
            return false
            
        case .halfOpen:
            return true
        }
    }
    
    /// Record successful operation
    public func recordSuccess() {
        lock.lock()
        defer { lock.unlock() }
        
        failureCount = 0
        
        switch state {
        case .closed:
            break
            
        case .halfOpen:
            successCount += 1
            if successCount >= successThreshold {
                state = .closed
                successCount = 0
            }
            
        case .open:
            break
        }
    }
    
    /// Record failed operation
    public func recordFailure() {
        lock.lock()
        defer { lock.unlock() }
        
        failureCount += 1
        lastFailureTime = Date()
        
        switch state {
        case .closed:
            if failureCount >= failureThreshold {
                state = .open
            }
            
        case .halfOpen:
            state = .open
            successCount = 0
            
        case .open:
            break
        }
    }
    
    /// Get current state
    public func getState() -> State {
        lock.lock()
        defer { lock.unlock() }
        return state
    }
    
    /// Reset circuit breaker
    public func reset() {
        lock.lock()
        defer { lock.unlock() }
        state = .closed
        failureCount = 0
        successCount = 0
        lastFailureTime = nil
    }
}

// MARK: - Recovery Policy

/// Comprehensive recovery policy
public struct RecoveryPolicy {
    public var maxRetries: Int
    public var backoffStrategy: BackoffStrategy
    public var circuitBreaker: CircuitBreaker?
    public var classifyError: (Error) -> ErrorSeverity
    
    public init(
        maxRetries: Int = 3,
        backoffStrategy: BackoffStrategy = .exponential(initial: 0.1, multiplier: 2.0),
        circuitBreaker: CircuitBreaker? = nil,
        classifyError: @escaping (Error) -> ErrorSeverity = ErrorClassifier.classify
    ) {
        self.maxRetries = maxRetries
        self.backoffStrategy = backoffStrategy
        self.circuitBreaker = circuitBreaker
        self.classifyError = classifyError
    }
    
    /// Execute operation with retry logic
    public func recover<T>(
        _ operation: () throws -> T
    ) throws -> T {
        var lastError: Error?
        
        for attempt in 0...maxRetries {
            // Check circuit breaker
            if let breaker = circuitBreaker {
                guard breaker.allowRequest() else {
                    throw DBError.io("Circuit breaker is open")
                }
            }
            
            do {
                let result = try operation()
                
                // Success - record and return
                circuitBreaker?.recordSuccess()
                return result
                
            } catch {
                lastError = error
                
                // Classify error
                let severity = classifyError(error)
                
                // Fatal errors - don't retry
                if severity == .fatal {
                    circuitBreaker?.recordFailure()
                    throw error
                }
                
                // User action required - don't retry
                if severity == .userAction {
                    circuitBreaker?.recordFailure()
                    throw error
                }
                
                // Retriable - continue if attempts remain
                if attempt < maxRetries {
                    circuitBreaker?.recordFailure()
                    
                    // Calculate backoff delay
                    let delay = backoffStrategy.delay(for: attempt)
                    
                    // Sleep before retry
                    Thread.sleep(forTimeInterval: delay)
                    
                    continue
                }
                
                // Max retries exhausted
                circuitBreaker?.recordFailure()
                throw error
            }
        }
        
        // Should never reach here, but satisfy compiler
        throw lastError ?? DBError.io("Recovery failed")
    }
}

// MARK: - Async Recovery (Swift Concurrency)

#if compiler(>=5.5) && canImport(_Concurrency)
@available(macOS 10.15, iOS 13.0, watchOS 6.0, tvOS 13.0, *)
extension RecoveryPolicy {
    /// Execute async operation with retry logic
    public func recoverAsync<T>(
        _ operation: @Sendable () async throws -> T
    ) async throws -> T {
        var lastError: Error?
        
        for attempt in 0...maxRetries {
            // Check circuit breaker
            if let breaker = circuitBreaker {
                guard breaker.allowRequest() else {
                    throw DBError.io("Circuit breaker is open")
                }
            }
            
            do {
                let result = try await operation()
                
                // Success - record and return
                circuitBreaker?.recordSuccess()
                return result
                
            } catch {
                lastError = error
                
                // Classify error
                let severity = classifyError(error)
                
                // Fatal errors - don't retry
                if severity == .fatal {
                    circuitBreaker?.recordFailure()
                    throw error
                }
                
                // User action required - don't retry
                if severity == .userAction {
                    circuitBreaker?.recordFailure()
                    throw error
                }
                
                // Retriable - continue if attempts remain
                if attempt < maxRetries {
                    circuitBreaker?.recordFailure()
                    
                    // Calculate backoff delay
                    let delay = backoffStrategy.delay(for: attempt)
                    
                    // Async sleep
                    try await Task.sleep(nanoseconds: UInt64(delay * 1_000_000_000))
                    
                    continue
                }
                
                // Max retries exhausted
                circuitBreaker?.recordFailure()
                throw error
            }
        }
        
        // Should never reach here, but satisfy compiler
        throw lastError ?? DBError.io("Recovery failed")
    }
}
#endif

// MARK: - Global Recovery Manager

/// Global error recovery manager
public final class RecoveryManager {
    public static let shared = RecoveryManager()
    
    private var policies: [String: RecoveryPolicy] = [:]
    private let lock = NSLock()
    
    private init() {
        // Setup default policies
        setupDefaultPolicies()
    }
    
    private func setupDefaultPolicies() {
        // Default policy for transactions
        let transactionPolicy = RecoveryPolicy(
            maxRetries: 3,
            backoffStrategy: .exponential(initial: 0.1, multiplier: 2.0),
            circuitBreaker: CircuitBreaker(failureThreshold: 5, successThreshold: 2, timeout: 60.0)
        )
        registerPolicy("transaction", policy: transactionPolicy)
        
        // Default policy for I/O operations
        let ioPolicy = RecoveryPolicy(
            maxRetries: 5,
            backoffStrategy: .exponential(initial: 0.05, multiplier: 1.5),
            circuitBreaker: CircuitBreaker(failureThreshold: 10, successThreshold: 3, timeout: 30.0)
        )
        registerPolicy("io", policy: ioPolicy)
        
        // Default policy for network operations
        let networkPolicy = RecoveryPolicy(
            maxRetries: 3,
            backoffStrategy: .fibonacci(initial: 0.5),
            circuitBreaker: CircuitBreaker(failureThreshold: 3, successThreshold: 2, timeout: 120.0)
        )
        registerPolicy("network", policy: networkPolicy)
    }
    
    /// Register a custom recovery policy
    public func registerPolicy(_ name: String, policy: RecoveryPolicy) {
        lock.lock()
        defer { lock.unlock() }
        policies[name] = policy
    }
    
    /// Get a registered policy
    public func getPolicy(_ name: String) -> RecoveryPolicy? {
        lock.lock()
        defer { lock.unlock() }
        return policies[name]
    }
    
    /// Execute operation with named policy
    public func recover<T>(
        using policyName: String = "transaction",
        _ operation: () throws -> T
    ) throws -> T {
        guard let policy = getPolicy(policyName) else {
            // Fallback to direct execution
            return try operation()
        }
        
        return try policy.recover(operation)
    }
}

// MARK: - Convenience Extensions

extension Database {
    /// Execute transaction with automatic retry
    public func executeWithRetry<T>(
        policy: RecoveryPolicy? = nil,
        _ block: (UInt64) throws -> T
    ) throws -> T {
        let recoveryPolicy = policy ?? RecoveryManager.shared.getPolicy("transaction") ?? RecoveryPolicy()
        
        return try recoveryPolicy.recover {
            let tid = try self.begin()
            do {
                let result = try block(tid)
                try self.commit(tid)
                return result
            } catch {
                try? self.rollback(tid)
                throw error
            }
        }
    }
}

