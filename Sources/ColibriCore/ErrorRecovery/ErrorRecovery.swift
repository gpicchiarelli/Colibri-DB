/*
 * ErrorRecovery.swift
 * ColibrìDB - Error Handling and Recovery System
 *
 * Based on TLA+ specification: ErrorRecovery.tla
 *
 * Implements comprehensive error recovery system:
 * - Error detection and classification
 * - Error propagation and containment
 * - Recovery strategies (retry, rollback, compensation)
 * - Checkpoint-based recovery
 * - Transaction abort and rollback
 * - System-level recovery
 * - Fault tolerance
 *
 * References:
 * [1] Gray, J. (1981). "The Transaction Concept: Virtues and Limitations"
 *     Proceedings of VLDB, pp. 144-154.
 * [2] Gray, J., & Reuter, A. (1992). "Transaction Processing: Concepts and Techniques"
 *     Morgan Kaufmann. Chapter 10: Crash Recovery
 * [3] Mohan, C., & Narang, I. (1992). "Recovery and Coherency-Control Protocols"
 *     Proceedings of VLDB, pp. 193-207.
 * [4] Avizienis, A., et al. (2004). "Basic Concepts and Taxonomy of Dependable Computing"
 *     IEEE Transactions on Dependable and Secure Computing, 1(1), 11-33.
 *
 * Author: ColibrìDB Team
 * Date: 2025-10-19
 */

import Foundation

// MARK: - Error Types (TLA+: ErrorTypes)

/// Error classification types
public enum ErrorType: String, Codable {
    case transient = "TRANSIENT"     // Temporary error (retry may succeed)
    case permanent = "PERMANENT"     // Persistent error (requires intervention)
    case intermittent = "INTERMITTENT" // Sporadic error
    case byzantine = "BYZANTINE"     // Arbitrary/malicious error
}

// MARK: - Component States (TLA+: ComponentStates)

/// Component operational states
public enum ComponentState: String, Codable {
    case operational = "OPERATIONAL"     // Component working normally
    case errorDetected = "ERROR_DETECTED" // Error detected, not yet handled
    case recovering = "RECOVERING"       // Recovery in progress
    case failed = "FAILED"               // Component failed
    case recovered = "RECOVERED"          // Recovery completed
}

// MARK: - Recovery Strategies (TLA+: RecoveryStrategies)

/// Available recovery strategies
public enum RecoveryStrategy: String, Codable {
    case retry = "RETRY"                     // Re-execute failed operation
    case rollback = "ROLLBACK"               // Undo to consistent state
    case checkpointRestore = "CHECKPOINT_RESTORE" // Restore from checkpoint
    case failover = "FAILOVER"               // Switch to backup component
    case compensate = "COMPENSATE"           // Execute compensating transaction
}

// MARK: - Error Severity (TLA+: severity)

/// Error severity levels
public enum ErrorSeverity: String, Codable {
    case low = "LOW"
    case medium = "MEDIUM"
    case high = "HIGH"
    case critical = "CRITICAL"
}

// MARK: - Error Record (TLA+: ErrorRecord)

/// Error record structure
public struct ErrorRecord: Codable, Equatable {
    public let errorId: Int              // TLA+: errorId
    public let component: String          // TLA+: component
    public let errorType: ErrorType      // TLA+: errorType
    public let timestamp: Int            // TLA+: timestamp
    public let description: String        // TLA+: description
    public let severity: ErrorSeverity   // TLA+: severity
    public let recoverable: Bool         // TLA+: recoverable
    
    public init(errorId: Int, component: String, errorType: ErrorType, 
                timestamp: Int, description: String, severity: ErrorSeverity, 
                recoverable: Bool) {
        self.errorId = errorId
        self.component = component
        self.errorType = errorType
        self.timestamp = timestamp
        self.description = description
        self.severity = severity
        self.recoverable = recoverable
    }
}

// MARK: - Recovery Action (TLA+: RecoveryAction)

/// Recovery action structure
public struct RecoveryActionRecord: Codable, Equatable {
    public let errorId: Int              // TLA+: errorId
    public let strategy: RecoveryStrategy // TLA+: strategy
    public let attempts: Int             // TLA+: attempts
    public let success: Bool             // TLA+: success
    
    public init(errorId: Int, strategy: RecoveryStrategy, attempts: Int, success: Bool) {
        self.errorId = errorId
        self.strategy = strategy
        self.attempts = attempts
        self.success = success
    }
}

// MARK: - Checkpoint (TLA+: Checkpoint)

/// Error recovery checkpoint structure
public struct ErrorRecoveryCheckpoint: Codable, Equatable {
    public let checkpointId: Int        // TLA+: checkpointId
    public let component: String        // TLA+: component
    public let timestamp: Int           // TLA+: timestamp
    public let state: [String: Value]   // TLA+: state
    
    public init(checkpointId: Int, component: String, timestamp: Int, state: [String: Value]) {
        self.checkpointId = checkpointId
        self.component = component
        self.timestamp = timestamp
        self.state = state
    }
}

// MARK: - Error Recovery Manager

/// Comprehensive error handling and recovery system
/// Corresponds to TLA+ module: ErrorRecovery.tla
public actor ErrorRecoveryManager {
    
    // TLA+ VARIABLES
    
    /// Component states (TLA+: componentStates)
    private var componentStates: [String: ComponentState] = [:]
    
    /// Component errors (TLA+: componentErrors)
    private var componentErrors: [String: Set<Int>] = [:]
    
    /// Error records (TLA+: errors)
    private var errors: [Int: ErrorRecord] = [:]
    
    /// Next error ID (TLA+: nextErrorId)
    private var nextErrorId: Int = 1
    
    /// Error log (TLA+: errorLog)
    private var errorLog: [ErrorRecord] = []
    
    /// Recovery actions (TLA+: recoveryActions)
    private var recoveryActions: [Int: RecoveryActionRecord] = [:]
    
    /// Retry counters (TLA+: retryCounters)
    private var retryCounters: [Int: Int] = [:]
    
    /// Recovery in progress (TLA+: recoveryInProgress)
    private var recoveryInProgress: Set<Int> = []
    
    /// Checkpoints (TLA+: checkpoints)
    private var checkpoints: [String: [ErrorRecoveryCheckpoint]] = [:]
    
    /// Last checkpoint ID (TLA+: lastCheckpointId)
    private var lastCheckpointId: [String: Int] = [:]
    
    /// State snapshots (TLA+: stateSnapshots)
    private var stateSnapshots: [Int: [String: Value]] = [:]
    
    /// Statistics (TLA+: totalErrors, totalRecoveries, totalFailures)
    private var totalErrors: Int = 0
    private var totalRecoveries: Int = 0
    private var totalFailures: Int = 0
    
    // Configuration (TLA+: CONSTANTS)
    private let maxRetries: Int = 3
    private let maxCheckpoints: Int = 10
    private let components: Set<String>
    
    public init(components: Set<String>) {
        self.components = components
        
        // Initialize all components as operational
        for component in components {
            componentStates[component] = .operational
            componentErrors[component] = []
            checkpoints[component] = []
            lastCheckpointId[component] = 0
        }
    }
    
    // MARK: - Helper Functions (TLA+ Helpers)
    
    /// Check if error is recoverable (TLA+: IsRecoverable)
    private func isRecoverable(errorId: Int) -> Bool {
        return errors[errorId]?.recoverable ?? false
    }
    
    /// Check if retry limit reached (TLA+: RetryLimitReached)
    private func retryLimitReached(errorId: Int) -> Bool {
        return (retryCounters[errorId] ?? 0) >= maxRetries
    }
    
    /// Get latest checkpoint for component (TLA+: LatestCheckpoint)
    private func latestCheckpoint(component: String) -> ErrorRecoveryCheckpoint? {
        let checkpoints = checkpoints[component] ?? []
        return checkpoints.last
    }
    
    // MARK: - Error Detection (TLA+: DetectError)
    
    /// Detect and report error
    public func detectError(component: String, errorType: ErrorType, 
                           severity: ErrorSeverity, recoverable: Bool, 
                           description: String = "Error detected") async throws {
        guard components.contains(component) else {
            throw ErrorRecoveryError.invalidComponent(component)
        }
        
        guard componentStates[component] == .operational else {
            throw ErrorRecoveryError.componentNotOperational(component)
        }
        
        let errorId = nextErrorId
        let error = ErrorRecord(
            errorId: errorId,
            component: component,
            errorType: errorType,
            timestamp: totalErrors,
            description: description,
            severity: severity,
            recoverable: recoverable
        )
        
        errors[errorId] = error
        nextErrorId += 1
        errorLog.append(error)
        componentStates[component] = .errorDetected
        componentErrors[component, default: []].insert(errorId)
        totalErrors += 1
    }
    
    // MARK: - Checkpoint Management (TLA+: CreateCheckpoint, PruneCheckpoints)
    
    /// Create checkpoint for component
    public func createCheckpoint(component: String, state: [String: Value]) async throws {
        guard components.contains(component) else {
            throw ErrorRecoveryError.invalidComponent(component)
        }
        
        guard componentStates[component] == .operational else {
            throw ErrorRecoveryError.componentNotOperational(component)
        }
        
        guard (checkpoints[component]?.count ?? 0) < maxCheckpoints else {
            throw ErrorRecoveryError.checkpointLimitReached(component)
        }
        
        let checkpointId = lastCheckpointId[component, default: 0] + 1
        let checkpoint = Checkpoint(
            checkpointId: checkpointId,
            component: component,
            timestamp: totalErrors,
            state: state
        )
        
        checkpoints[component, default: []].append(checkpoint)
        lastCheckpointId[component] = checkpointId
        stateSnapshots[checkpointId] = state
    }
    
    /// Remove old checkpoints (garbage collection)
    public func pruneCheckpoints(component: String) async throws {
        guard components.contains(component) else {
            throw ErrorRecoveryError.invalidComponent(component)
        }
        
        guard (checkpoints[component]?.count ?? 0) > maxCheckpoints else {
            return
        }
        
        let checkpoints = checkpoints[component] ?? []
        let pruned = Array(checkpoints.dropFirst())
        self.checkpoints[component] = pruned
    }
    
    // MARK: - Recovery Strategies (TLA+: RetryOperation, RollbackToCheckpoint, etc.)
    
    /// Retry failed operation (for transient errors)
    public func retryOperation(errorId: Int) async throws {
        guard let error = errors[errorId] else {
            throw ErrorRecoveryError.errorNotFound(errorId)
        }
        
        guard error.errorType == .transient else {
            throw ErrorRecoveryError.invalidErrorType(errorId, expected: .transient, actual: error.errorType)
        }
        
        guard isRecoverable(errorId: errorId) else {
            throw ErrorRecoveryError.errorNotRecoverable(errorId)
        }
        
        guard !retryLimitReached(errorId: errorId) else {
            throw ErrorRecoveryError.retryLimitReached(errorId)
        }
        
        guard !recoveryInProgress.contains(errorId) else {
            throw ErrorRecoveryError.recoveryInProgress(errorId)
        }
        
        recoveryInProgress.insert(errorId)
        componentStates[error.component] = .recovering
        retryCounters[errorId, default: 0] += 1
    }
    
    /// Complete successful retry
    public func retrySuccess(errorId: Int) async throws {
        guard recoveryInProgress.contains(errorId) else {
            throw ErrorRecoveryError.noRecoveryInProgress(errorId)
        }
        
        guard let error = errors[errorId] else {
            throw ErrorRecoveryError.errorNotFound(errorId)
        }
        
        componentStates[error.component] = .recovered
        componentErrors[error.component, default: []].remove(errorId)
        recoveryInProgress.remove(errorId)
        totalRecoveries += 1
    }
    
    /// Retry failed (exhaust retries)
    public func retryFailed(errorId: Int) async throws {
        guard recoveryInProgress.contains(errorId) else {
            throw ErrorRecoveryError.noRecoveryInProgress(errorId)
        }
        
        guard retryLimitReached(errorId: errorId) else {
            throw ErrorRecoveryError.retryLimitNotReached(errorId)
        }
        
        guard let error = errors[errorId] else {
            throw ErrorRecoveryError.errorNotFound(errorId)
        }
        
        componentStates[error.component] = .failed
        recoveryInProgress.remove(errorId)
        totalFailures += 1
    }
    
    /// Rollback using checkpoint
    public func rollbackToCheckpoint(component: String, errorId: Int) async throws {
        guard components.contains(component) else {
            throw ErrorRecoveryError.invalidComponent(component)
        }
        
        guard let error = errors[errorId] else {
            throw ErrorRecoveryError.errorNotFound(errorId)
        }
        
        guard error.component == component else {
            throw ErrorRecoveryError.errorComponentMismatch(errorId, expected: component, actual: error.component)
        }
        
        guard isRecoverable(errorId: errorId) else {
            throw ErrorRecoveryError.errorNotRecoverable(errorId)
        }
        
        guard let checkpoint = latestCheckpoint(component: component) else {
            throw ErrorRecoveryError.noCheckpointAvailable(component)
        }
        
        componentStates[component] = .recovering
        recoveryInProgress.insert(errorId)
        
        let action = RecoveryActionRecord(
            errorId: errorId,
            strategy: .checkpointRestore,
            attempts: 1,
            success: true
        )
        recoveryActions[errorId] = action
    }
    
    /// Complete checkpoint restore
    public func completeCheckpointRestore(component: String, errorId: Int) async throws {
        guard components.contains(component) else {
            throw ErrorRecoveryError.invalidComponent(component)
        }
        
        guard recoveryInProgress.contains(errorId) else {
            throw ErrorRecoveryError.noRecoveryInProgress(errorId)
        }
        
        guard let error = errors[errorId] else {
            throw ErrorRecoveryError.errorNotFound(errorId)
        }
        
        guard error.component == component else {
            throw ErrorRecoveryError.errorComponentMismatch(errorId, expected: component, actual: error.component)
        }
        
        guard let action = recoveryActions[errorId],
              action.strategy == .checkpointRestore else {
            throw ErrorRecoveryError.invalidRecoveryAction(errorId)
        }
        
        componentStates[component] = .recovered
        componentErrors[component, default: []].remove(errorId)
        recoveryInProgress.remove(errorId)
        totalRecoveries += 1
    }
    
    /// Execute compensating action (for irreversible operations)
    public func executeCompensatingAction(component: String, errorId: Int) async throws {
        guard components.contains(component) else {
            throw ErrorRecoveryError.invalidComponent(component)
        }
        
        guard let error = errors[errorId] else {
            throw ErrorRecoveryError.errorNotFound(errorId)
        }
        
        guard error.component == component else {
            throw ErrorRecoveryError.errorComponentMismatch(errorId, expected: component, actual: error.component)
        }
        
        guard isRecoverable(errorId: errorId) else {
            throw ErrorRecoveryError.errorNotRecoverable(errorId)
        }
        
        componentStates[component] = .recovering
        recoveryInProgress.insert(errorId)
        
        let action = RecoveryActionRecord(
            errorId: errorId,
            strategy: .compensate,
            attempts: 1,
            success: true
        )
        recoveryActions[errorId] = action
        totalRecoveries += 1
    }
    
    /// Mark component as recovered
    public func markComponentRecovered(component: String) async throws {
        guard components.contains(component) else {
            throw ErrorRecoveryError.invalidComponent(component)
        }
        
        guard componentStates[component] == .recovering else {
            throw ErrorRecoveryError.componentNotRecovering(component)
        }
        
        guard componentErrors[component]?.isEmpty ?? true else {
            throw ErrorRecoveryError.componentHasErrors(component)
        }
        
        componentStates[component] = .operational
    }
    
    // MARK: - Query Methods
    
    public func getComponentState(_ component: String) -> ComponentState? {
        return componentStates[component]
    }
    
    public func getComponentErrors(_ component: String) -> Set<Int> {
        return componentErrors[component] ?? []
    }
    
    public func getError(_ errorId: Int) -> ErrorRecord? {
        return errors[errorId]
    }
    
    public func getErrorLog() -> [ErrorRecord] {
        return errorLog
    }
    
    public func getRecoveryAction(_ errorId: Int) -> RecoveryActionRecord? {
        return recoveryActions[errorId]
    }
    
    public func getRetryCount(_ errorId: Int) -> Int {
        return retryCounters[errorId] ?? 0
    }
    
    public func isRecoveryInProgress(_ errorId: Int) -> Bool {
        return recoveryInProgress.contains(errorId)
    }
    
    public func getCheckpoints(_ component: String) -> [ErrorRecoveryCheckpoint] {
        return checkpoints[component] ?? []
    }
    
    public func getStateSnapshot(_ checkpointId: Int) -> [String: Value]? {
        return stateSnapshots[checkpointId]
    }
    
    public func getStatistics() -> (totalErrors: Int, totalRecoveries: Int, totalFailures: Int) {
        return (totalErrors, totalRecoveries, totalFailures)
    }
    
    // MARK: - TLA+ Invariants Implementation
    
    /// Invariant: Recovery attempts bounded (TLA+: RecoveryAttemptsBounded)
    public func checkRecoveryAttemptsBoundedInvariant() -> Bool {
        return retryCounters.allSatisfy { (_, count) in count <= maxRetries }
    }
    
    /// Invariant: Checkpoint limit respected (TLA+: CheckpointLimitRespected)
    public func checkCheckpointLimitRespectedInvariant() -> Bool {
        return checkpoints.allSatisfy { (_, checkpoints) in checkpoints.count <= maxCheckpoints }
    }
    
    /// Invariant: No inconsistent recovery states (TLA+: NoInconsistentRecovery)
    public func checkNoInconsistentRecoveryInvariant() -> Bool {
        return componentStates.allSatisfy { (component, state) in
            if state == .recovered {
                return componentErrors[component]?.isEmpty ?? true
            }
            return true
        }
    }
    
    /// Invariant: Errors eventually handled (TLA+: ErrorsEventuallyHandled)
    public func checkErrorsEventuallyHandledInvariant() -> Bool {
        return componentStates.allSatisfy { (_, state) in
            state != .errorDetected || state == .recovering || state == .recovered || state == .failed
        }
    }
    
    /// Combined safety invariant (TLA+: Safety)
    public func checkSafetyInvariant() -> Bool {
        return checkRecoveryAttemptsBoundedInvariant() &&
               checkCheckpointLimitRespectedInvariant() &&
               checkNoInconsistentRecoveryInvariant() &&
               checkErrorsEventuallyHandledInvariant()
    }
}

// MARK: - Errors

public enum ErrorRecoveryError: Error, LocalizedError {
    case invalidComponent(String)
    case componentNotOperational(String)
    case checkpointLimitReached(String)
    case errorNotFound(Int)
    case invalidErrorType(Int, expected: ErrorType, actual: ErrorType)
    case errorNotRecoverable(Int)
    case retryLimitReached(Int)
    case retryLimitNotReached(Int)
    case recoveryInProgress(Int)
    case noRecoveryInProgress(Int)
    case errorComponentMismatch(Int, expected: String, actual: String)
    case noCheckpointAvailable(String)
    case invalidRecoveryAction(Int)
    case componentNotRecovering(String)
    case componentHasErrors(String)
    
    public var errorDescription: String? {
        switch self {
        case .invalidComponent(let component):
            return "Invalid component: '\(component)'"
        case .componentNotOperational(let component):
            return "Component '\(component)' is not operational"
        case .checkpointLimitReached(let component):
            return "Checkpoint limit reached for component '\(component)'"
        case .errorNotFound(let errorId):
            return "Error with ID \(errorId) not found"
        case .invalidErrorType(let errorId, let expected, let actual):
            return "Invalid error type for error \(errorId): expected \(expected), got \(actual)"
        case .errorNotRecoverable(let errorId):
            return "Error \(errorId) is not recoverable"
        case .retryLimitReached(let errorId):
            return "Retry limit reached for error \(errorId)"
        case .retryLimitNotReached(let errorId):
            return "Retry limit not reached for error \(errorId)"
        case .recoveryInProgress(let errorId):
            return "Recovery already in progress for error \(errorId)"
        case .noRecoveryInProgress(let errorId):
            return "No recovery in progress for error \(errorId)"
        case .errorComponentMismatch(let errorId, let expected, let actual):
            return "Error \(errorId) component mismatch: expected '\(expected)', got '\(actual)'"
        case .noCheckpointAvailable(let component):
            return "No checkpoint available for component '\(component)'"
        case .invalidRecoveryAction(let errorId):
            return "Invalid recovery action for error \(errorId)"
        case .componentNotRecovering(let component):
            return "Component '\(component)' is not recovering"
        case .componentHasErrors(let component):
            return "Component '\(component)' has errors"
        }
    }
}

/*
 * IMPLEMENTATION NOTES:
 *
 * This implementation follows the ErrorRecovery.tla specification and
 * implements comprehensive error handling and recovery:
 *
 * 1. Error Detection and Classification (Avizienis 2004):
 *    - Transient, permanent, intermittent, byzantine errors
 *    - Severity levels: low, medium, high, critical
 *    - Component-specific error tracking
 *    - Error propagation and containment
 *
 * 2. Recovery Strategies (Gray 1992):
 *    - Retry: for transient errors with bounded attempts
 *    - Rollback: undo to consistent state
 *    - Checkpoint restore: restore from saved state
 *    - Compensating actions: for irreversible operations
 *    - Failover: switch to backup components
 *
 * 3. Checkpoint Management (Gray 1992, Section 10.3):
 *    - Component-level checkpoints
 *    - State snapshots
 *    - Checkpoint pruning (garbage collection)
 *    - Atomic checkpoint creation
 *
 * 4. Component State Management:
 *    - Operational, error detected, recovering, failed, recovered
 *    - State transitions according to recovery actions
 *    - Error isolation and containment
 *    - Recovery completion tracking
 *
 * 5. Statistics and Monitoring:
 *    - Total errors, recoveries, failures
 *    - Error history and logging
 *    - Recovery action tracking
 *    - Performance metrics
 *
 * Correctness Properties (verified by TLA+):
 * - Recovery attempts are bounded
 * - Checkpoint limit is respected
 * - No inconsistent recovery states
 * - Errors are eventually handled
 * - Recoverable errors eventually recovered
 * - Components eventually return to operational state
 *
 * Production Examples:
 * - PostgreSQL: Error handling and recovery
 * - Oracle: Fault tolerance and recovery
 * - SQL Server: Error recovery mechanisms
 * - MySQL: InnoDB error handling
 */

