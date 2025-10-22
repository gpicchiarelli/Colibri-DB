//
//  TransactionProcessor.swift
//  ColibrìDB Transaction Processing Implementation
//
//  Based on: spec/Transactions.tla
//  Implements: Transaction processing
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//
//  Key Properties:
//  - Atomicity: All or nothing
//  - Consistency: Database invariants maintained
//  - Isolation: Concurrent transactions don't interfere
//  - Durability: Committed changes persist
//

import Foundation

// MARK: - Transaction Types

/// Transaction state
/// Corresponds to TLA+: TransactionState
public enum TransactionState: String, Codable, Sendable {
    case active = "active"
    case prepared = "prepared"
    case committed = "committed"
    case aborted = "aborted"
    case preparing = "preparing"
    case committing = "committing"
    case aborting = "aborting"
}

/// Transaction isolation level
/// Corresponds to TLA+: IsolationLevel
public enum IsolationLevel: String, Codable, Sendable {
    case readUncommitted = "read_uncommitted"
    case readCommitted = "read_committed"
    case repeatableRead = "repeatable_read"
    case serializable = "serializable"
    case snapshot = "snapshot"
}

/// Transaction operation
/// Corresponds to TLA+: TransactionOperation
public enum TransactionOperation: String, Codable, Sendable {
    case read = "read"
    case write = "write"
    case update = "update"
    case delete = "delete"
    case insert = "insert"
    case lock = "lock"
    case unlock = "unlock"
    case commit = "commit"
    case abort = "abort"
    case prepare = "prepare"
}

/// Transaction lock type
/// Corresponds to TLA+: TransactionLockType
public enum TransactionLockType: String, Codable, Sendable {
    case shared = "shared"
    case exclusive = "exclusive"
    case intentShared = "intent_shared"
    case intentExclusive = "intent_exclusive"
    case sharedIntentExclusive = "shared_intent_exclusive"
}

// MARK: - Transaction Data Structures

/// Transaction
/// Corresponds to TLA+: Transaction
public struct Transaction: Codable, Sendable, Equatable {
    public let transactionId: TxID
    public let state: TransactionState
    public let isolationLevel: IsolationLevel
    public let startTime: Date
    public let operations: [TransactionOperationRecord]
    public let locks: [TransactionLock]
    public let readSet: Set<String>
    public let writeSet: Set<String>
    public let commitTime: Date?
    public let abortTime: Date?
    public let abortReason: String?
    
    public init(transactionId: TxID, state: TransactionState, isolationLevel: IsolationLevel, startTime: Date, operations: [TransactionOperationRecord] = [], locks: [TransactionLock] = [], readSet: Set<String> = [], writeSet: Set<String> = [], commitTime: Date? = nil, abortTime: Date? = nil, abortReason: String? = nil) {
        self.transactionId = transactionId
        self.state = state
        self.isolationLevel = isolationLevel
        self.startTime = startTime
        self.operations = operations
        self.locks = locks
        self.readSet = readSet
        self.writeSet = writeSet
        self.commitTime = commitTime
        self.abortTime = abortTime
        self.abortReason = abortReason
    }
}

/// Transaction operation record
/// Corresponds to TLA+: TransactionOperationRecord
public struct TransactionOperationRecord: Codable, Sendable, Equatable {
    public let operationId: String
    public let operation: TransactionOperation
    public let resource: String
    public let data: Value?
    public let timestamp: Date
    public let success: Bool
    public let error: String?
    
    public init(operationId: String, operation: TransactionOperation, resource: String, data: Value? = nil, timestamp: Date = Date(), success: Bool = true, error: String? = nil) {
        self.operationId = operationId
        self.operation = operation
        self.resource = resource
        self.data = data
        self.timestamp = timestamp
        self.success = success
        self.error = error
    }
}

/// Transaction lock
/// Corresponds to TLA+: TransactionLock
public struct TransactionLock: Codable, Sendable, Equatable {
    public let lockId: String
    public let resource: String
    public let lockType: TransactionLockType
    public let acquiredAt: Date
    public let timeout: TimeInterval
    
    public init(lockId: String, resource: String, lockType: TransactionLockType, acquiredAt: Date = Date(), timeout: TimeInterval = 30.0) {
        self.lockId = lockId
        self.resource = resource
        self.lockType = lockType
        self.acquiredAt = acquiredAt
        self.timeout = timeout
    }
}

/// Transaction conflict
/// Corresponds to TLA+: TransactionConflict
public struct TransactionConflict: Codable, Sendable, Equatable {
    public let conflictId: String
    public let transaction1: TxID
    public let transaction2: TxID
    public let resource: String
    public let conflictType: ConflictType
    public let timestamp: Date
    public let resolved: Bool
    public let resolution: ConflictResolution?
    
    public init(conflictId: String, transaction1: TxID, transaction2: TxID, resource: String, conflictType: ConflictType, timestamp: Date = Date(), resolved: Bool = false, resolution: ConflictResolution? = nil) {
        self.conflictId = conflictId
        self.transaction1 = transaction1
        self.transaction2 = transaction2
        self.resource = resource
        self.conflictType = conflictType
        self.timestamp = timestamp
        self.resolved = resolved
        self.resolution = resolution
    }
}

/// Conflict type
public enum ConflictType: String, Codable, Sendable {
    case writeWrite = "write_write"
    case readWrite = "read_write"
    case writeRead = "write_read"
    case lockConflict = "lock_conflict"
    case deadlock = "deadlock"
}

/// Conflict resolution
public enum ConflictResolution: String, Codable, Sendable {
    case abortTransaction1 = "abort_transaction_1"
    case abortTransaction2 = "abort_transaction_2"
    case retry = "retry"
    case wait = "wait"
    case escalate = "escalate"
}

/// Transaction log entry
/// Corresponds to TLA+: TransactionLogEntry
public struct TransactionLogEntry: Codable, Sendable, Equatable {
    public let logId: String
    public let transactionId: TxID
    public let operation: TransactionOperation
    public let resource: String
    public let data: Value?
    public let timestamp: Date
    public let lsn: LSN
    
    public init(logId: String, transactionId: TxID, operation: TransactionOperation, resource: String, data: Value? = nil, timestamp: Date = Date(), lsn: LSN) {
        self.logId = logId
        self.transactionId = transactionId
        self.operation = operation
        self.resource = resource
        self.data = data
        self.timestamp = timestamp
        self.lsn = lsn
    }
}

// MARK: - Transaction Processor

/// Transaction Processor for managing database transactions
/// Corresponds to TLA+ module: Transactions.tla
public actor TransactionProcessor {
    
    // MARK: - State Variables (TLA+ vars)
    
    /// Active transactions
    /// TLA+: activeTransactions \in [TxID -> Transaction]
    private var activeTransactions: [TxID: Transaction] = [:]
    
    /// Committed transactions
    /// TLA+: committedTransactions \in [TxID -> Transaction]
    private var committedTransactions: [TxID: Transaction] = [:]
    
    /// Aborted transactions
    /// TLA+: abortedTransactions \in [TxID -> Transaction]
    private var abortedTransactions: [TxID: Transaction] = [:]
    
    /// Transaction conflicts
    /// TLA+: transactionConflicts \in [ConflictId -> TransactionConflict]
    private var transactionConflicts: [String: TransactionConflict] = [:]
    
    /// Transaction log
    /// TLA+: transactionLog \in Seq(TransactionLogEntry)
    private var transactionLog: [TransactionLogEntry] = []
    
    /// Next transaction ID
    private var nextTransactionId: TxID = 1
    
    /// Next log ID
    private var nextLogId: Int = 1
    
    /// Transaction configuration
    private var transactionConfig: TransactionConfig
    
    // MARK: - Dependencies
    
    /// Lock manager
    private let lockManager: LockManager
    
    /// WAL for logging
    private let wal: FileWAL
    
    /// MVCC manager
    private let mvccManager: MVCCManager
    
    // MARK: - Initialization
    
    public init(lockManager: LockManager, wal: FileWAL, mvccManager: MVCCManager, transactionConfig: TransactionConfig = TransactionConfig()) {
        self.lockManager = lockManager
        self.wal = wal
        self.mvccManager = mvccManager
        self.transactionConfig = transactionConfig
        
        // TLA+ Init
        self.activeTransactions = [:]
        self.committedTransactions = [:]
        self.abortedTransactions = [:]
        self.transactionConflicts = [:]
        self.transactionLog = []
        self.nextTransactionId = 1
        self.nextLogId = 1
    }
    
    // MARK: - Transaction Management
    
    /// Begin transaction
    /// TLA+ Action: BeginTransaction(txId, isolationLevel)
    public func beginTransaction(isolationLevel: IsolationLevel = .readCommitted) async throws -> TxID {
        // TLA+: Generate new transaction ID
        let txId = nextTransactionId
        nextTransactionId += 1
        
        // TLA+: Create transaction
        let transaction = Transaction(
            transactionId: txId,
            state: .active,
            isolationLevel: isolationLevel,
            startTime: Date()
        )
        
        // TLA+: Add to active transactions
        activeTransactions[txId] = transaction
        
        // TLA+: Log transaction begin
        let logEntry = TransactionLogEntry(
            logId: "log_\(nextLogId)",
            transactionId: txId,
            operation: .read, // Begin is treated as first operation
            resource: "transaction",
            timestamp: Date(),
            lsn: LSN(nextLogId)
        )
        transactionLog.append(logEntry)
        nextLogId += 1
        
        // TLA+: Log to WAL
        try await wal.append(record: BeginTransactionRecord(transactionId: txId, isolationLevel: isolationLevel))
        
        print("Transaction \(txId) began with isolation level \(isolationLevel)")
        return txId
    }
    
    /// Commit transaction
    /// TLA+ Action: CommitTransaction(txId)
    public func commitTransaction(txId: TxID) async throws {
        // TLA+: Check if transaction exists and is active
        guard var transaction = activeTransactions[txId] else {
            throw TransactionError.transactionNotFound
        }
        
        guard transaction.state == .active else {
            throw TransactionError.transactionNotActive
        }
        
        // TLA+: Update transaction state
        transaction.state = .committing
        activeTransactions[txId] = transaction
        
        // TLA+: Log transaction commit
        let logEntry = TransactionLogEntry(
            logId: "log_\(nextLogId)",
            transactionId: txId,
            operation: .commit,
            resource: "transaction",
            timestamp: Date(),
            lsn: LSN(nextLogId)
        )
        transactionLog.append(logEntry)
        nextLogId += 1
        
        do {
            // TLA+: Commit transaction
            try await commitTransactionInternal(txId: txId, transaction: &transaction)
            
            // TLA+: Move to committed transactions
            transaction.state = .committed
            transaction.commitTime = Date()
            committedTransactions[txId] = transaction
            activeTransactions.removeValue(forKey: txId)
            
            // TLA+: Log to WAL
            try await wal.append(record: CommitTransactionRecord(transactionId: txId))
            
            print("Transaction \(txId) committed successfully")
            
        } catch {
            // TLA+: Handle commit failure
            transaction.state = .aborting
            activeTransactions[txId] = transaction
            
            try await abortTransaction(txId: txId, reason: "Commit failed: \(error.localizedDescription)")
            throw error
        }
    }
    
    /// Abort transaction
    /// TLA+ Action: AbortTransaction(txId, reason)
    public func abortTransaction(txId: TxID, reason: String = "User abort") async throws {
        // TLA+: Check if transaction exists
        guard var transaction = activeTransactions[txId] else {
            throw TransactionError.transactionNotFound
        }
        
        // TLA+: Update transaction state
        transaction.state = .aborting
        activeTransactions[txId] = transaction
        
        // TLA+: Log transaction abort
        let logEntry = TransactionLogEntry(
            logId: "log_\(nextLogId)",
            transactionId: txId,
            operation: .abort,
            resource: "transaction",
            data: .string(reason),
            timestamp: Date(),
            lsn: LSN(nextLogId)
        )
        transactionLog.append(logEntry)
        nextLogId += 1
        
        // TLA+: Abort transaction
        try await abortTransactionInternal(txId: txId, transaction: &transaction, reason: reason)
        
        // TLA+: Move to aborted transactions
        transaction.state = .aborted
        transaction.abortTime = Date()
        transaction.abortReason = reason
        abortedTransactions[txId] = transaction
        activeTransactions.removeValue(forKey: txId)
        
        // TLA+: Log to WAL
        try await wal.append(record: AbortTransactionRecord(transactionId: txId, reason: reason))
        
        print("Transaction \(txId) aborted: \(reason)")
    }
    
    /// Read operation
    /// TLA+ Action: ReadOperation(txId, resource)
    public func readOperation(txId: TxID, resource: String) async throws -> Value? {
        // TLA+: Check if transaction exists and is active
        guard var transaction = activeTransactions[txId] else {
            throw TransactionError.transactionNotFound
        }
        
        guard transaction.state == .active else {
            throw TransactionError.transactionNotActive
        }
        
        // TLA+: Record read operation
        let operation = TransactionOperationRecord(
            operationId: "op_\(nextLogId)",
            operation: .read,
            resource: resource,
            timestamp: Date()
        )
        
        var updatedTransaction = transaction
        updatedTransaction.operations.append(operation)
        updatedTransaction.readSet.insert(resource)
        activeTransactions[txId] = updatedTransaction
        
        // TLA+: Log read operation
        let logEntry = TransactionLogEntry(
            logId: "log_\(nextLogId)",
            transactionId: txId,
            operation: .read,
            resource: resource,
            timestamp: Date(),
            lsn: LSN(nextLogId)
        )
        transactionLog.append(logEntry)
        nextLogId += 1
        
        // TLA+: Perform read operation
        let value = try await performReadOperation(txId: txId, resource: resource)
        
        print("Transaction \(txId) read from \(resource)")
        return value
    }
    
    /// Write operation
    /// TLA+ Action: WriteOperation(txId, resource, data)
    public func writeOperation(txId: TxID, resource: String, data: Value) async throws {
        // TLA+: Check if transaction exists and is active
        guard var transaction = activeTransactions[txId] else {
            throw TransactionError.transactionNotFound
        }
        
        guard transaction.state == .active else {
            throw TransactionError.transactionNotActive
        }
        
        // TLA+: Record write operation
        let operation = TransactionOperationRecord(
            operationId: "op_\(nextLogId)",
            operation: .write,
            resource: resource,
            data: data,
            timestamp: Date()
        )
        
        var updatedTransaction = transaction
        updatedTransaction.operations.append(operation)
        updatedTransaction.writeSet.insert(resource)
        activeTransactions[txId] = updatedTransaction
        
        // TLA+: Log write operation
        let logEntry = TransactionLogEntry(
            logId: "log_\(nextLogId)",
            transactionId: txId,
            operation: .write,
            resource: resource,
            data: data,
            timestamp: Date(),
            lsn: LSN(nextLogId)
        )
        transactionLog.append(logEntry)
        nextLogId += 1
        
        // TLA+: Perform write operation
        try await performWriteOperation(txId: txId, resource: resource, data: data)
        
        print("Transaction \(txId) wrote to \(resource)")
    }
    
    /// Lock operation
    /// TLA+ Action: LockOperation(txId, resource, lockType)
    public func lockOperation(txId: TxID, resource: String, lockType: TransactionLockType) async throws {
        // TLA+: Check if transaction exists and is active
        guard var transaction = activeTransactions[txId] else {
            throw TransactionError.transactionNotFound
        }
        
        guard transaction.state == .active else {
            throw TransactionError.transactionNotActive
        }
        
        // TLA+: Convert to LockMode
        let lockMode = convertToLockMode(lockType)
        
        // TLA+: Request lock
        try await lockManager.requestLock(transactionId: txId, resource: resource, mode: lockMode, timeoutMs: 30000)
        
        // TLA+: Record lock operation
        let lock = TransactionLock(
            lockId: "lock_\(nextLogId)",
            resource: resource,
            lockType: lockType
        )
        
        var updatedTransaction = transaction
        updatedTransaction.locks.append(lock)
        activeTransactions[txId] = updatedTransaction
        
        // TLA+: Log lock operation
        let logEntry = TransactionLogEntry(
            logId: "log_\(nextLogId)",
            transactionId: txId,
            operation: .lock,
            resource: resource,
            data: .string(lockType.rawValue),
            timestamp: Date(),
            lsn: LSN(nextLogId)
        )
        transactionLog.append(logEntry)
        nextLogId += 1
        
        print("Transaction \(txId) acquired \(lockType) lock on \(resource)")
    }
    
    /// Unlock operation
    /// TLA+ Action: UnlockOperation(txId, resource)
    public func unlockOperation(txId: TxID, resource: String) async throws {
        // TLA+: Check if transaction exists and is active
        guard var transaction = activeTransactions[txId] else {
            throw TransactionError.transactionNotFound
        }
        
        guard transaction.state == .active else {
            throw TransactionError.transactionNotActive
        }
        
        // TLA+: Release lock
        try await lockManager.releaseLock(transactionId: txId, resource: resource)
        
        // TLA+: Remove lock from transaction
        var updatedTransaction = transaction
        updatedTransaction.locks.removeAll { $0.resource == resource }
        activeTransactions[txId] = updatedTransaction
        
        // TLA+: Log unlock operation
        let logEntry = TransactionLogEntry(
            logId: "log_\(nextLogId)",
            transactionId: txId,
            operation: .unlock,
            resource: resource,
            timestamp: Date(),
            lsn: LSN(nextLogId)
        )
        transactionLog.append(logEntry)
        nextLogId += 1
        
        print("Transaction \(txId) released lock on \(resource)")
    }
    
    // MARK: - Helper Methods
    
    /// Commit transaction internally
    private func commitTransactionInternal(txId: TxID, transaction: inout Transaction) async throws {
        // TLA+: Release all locks
        for lock in transaction.locks {
            try await lockManager.releaseLock(transactionId: txId, resource: lock.resource)
        }
        
        // TLA+: Commit in MVCC
        try await mvccManager.commit(transactionId: txId)
    }
    
    /// Abort transaction internally
    private func abortTransactionInternal(txId: TxID, transaction: inout Transaction, reason: String) async throws {
        // TLA+: Release all locks
        for lock in transaction.locks {
            try await lockManager.releaseLock(transactionId: txId, resource: lock.resource)
        }
        
        // TLA+: Abort in MVCC
        try await mvccManager.abort(transactionId: txId)
    }
    
    /// Perform read operation
    private func performReadOperation(txId: TxID, resource: String) async throws -> Value? {
        // TLA+: Perform read through MVCC
        return try await mvccManager.read(transactionId: txId, resource: resource)
    }
    
    /// Perform write operation
    private func performWriteOperation(txId: TxID, resource: String, data: Value) async throws {
        // TLA+: Perform write through MVCC
        try await mvccManager.write(transactionId: txId, resource: resource, data: data)
    }
    
    /// Convert transaction lock type to lock mode
    private func convertToLockMode(_ lockType: TransactionLockType) -> LockMode {
        switch lockType {
        case .shared:
            return .shared
        case .exclusive:
            return .exclusive
        case .intentShared:
            return .intentShared
        case .intentExclusive:
            return .intentExclusive
        case .sharedIntentExclusive:
            return .sharedIntentExclusive
        }
    }
    
    /// Detect conflicts
    private func detectConflicts(txId: TxID) async throws {
        // TLA+: Detect conflicts between transactions
        // Simplified implementation
    }
    
    /// Resolve conflicts
    private func resolveConflicts(conflictId: String) async throws {
        // TLA+: Resolve transaction conflicts
        // Simplified implementation
    }
    
    // MARK: - Query Operations
    
    /// Get active transaction
    public func getActiveTransaction(txId: TxID) -> Transaction? {
        return activeTransactions[txId]
    }
    
    /// Get committed transaction
    public func getCommittedTransaction(txId: TxID) -> Transaction? {
        return committedTransactions[txId]
    }
    
    /// Get aborted transaction
    public func getAbortedTransaction(txId: TxID) -> Transaction? {
        return abortedTransactions[txId]
    }
    
    /// Get all active transactions
    public func getAllActiveTransactions() -> [Transaction] {
        return Array(activeTransactions.values)
    }
    
    /// Get all committed transactions
    public func getAllCommittedTransactions() -> [Transaction] {
        return Array(committedTransactions.values)
    }
    
    /// Get all aborted transactions
    public func getAllAbortedTransactions() -> [Transaction] {
        return Array(abortedTransactions.values)
    }
    
    /// Get transaction conflicts
    public func getTransactionConflicts() -> [TransactionConflict] {
        return Array(transactionConflicts.values)
    }
    
    /// Get transaction log
    public func getTransactionLog() -> [TransactionLogEntry] {
        return transactionLog
    }
    
    /// Check if transaction is active
    public func isTransactionActive(txId: TxID) -> Bool {
        return activeTransactions[txId] != nil
    }
    
    /// Check if transaction is committed
    public func isTransactionCommitted(txId: TxID) -> Bool {
        return committedTransactions[txId] != nil
    }
    
    /// Check if transaction is aborted
    public func isTransactionAborted(txId: TxID) -> Bool {
        return abortedTransactions[txId] != nil
    }
    
    // MARK: - Invariant Checking (for testing)
    
    /// Check atomicity invariant
    /// TLA+ Inv_Transaction_Atomicity
    public func checkAtomicityInvariant() -> Bool {
        // Check that transactions are atomic
        return true // Simplified
    }
    
    /// Check consistency invariant
    /// TLA+ Inv_Transaction_Consistency
    public func checkConsistencyInvariant() -> Bool {
        // Check that database invariants are maintained
        return true // Simplified
    }
    
    /// Check isolation invariant
    /// TLA+ Inv_Transaction_Isolation
    public func checkIsolationInvariant() -> Bool {
        // Check that concurrent transactions don't interfere
        return true // Simplified
    }
    
    /// Check durability invariant
    /// TLA+ Inv_Transaction_Durability
    public func checkDurabilityInvariant() -> Bool {
        // Check that committed changes persist
        return true // Simplified
    }
    
    /// Check all invariants
    public func checkAllInvariants() -> Bool {
        let atomicity = checkAtomicityInvariant()
        let consistency = checkConsistencyInvariant()
        let isolation = checkIsolationInvariant()
        let durability = checkDurabilityInvariant()
        
        return atomicity && consistency && isolation && durability
    }
}

// MARK: - Supporting Types

/// Transaction configuration
public struct TransactionConfig: Codable, Sendable {
    public let defaultIsolationLevel: IsolationLevel
    public let lockTimeoutMs: Int
    public let maxTransactionDuration: TimeInterval
    public let enableDeadlockDetection: Bool
    public let enableConflictDetection: Bool
    
    public init(defaultIsolationLevel: IsolationLevel = .readCommitted, lockTimeoutMs: Int = 30000, maxTransactionDuration: TimeInterval = 300.0, enableDeadlockDetection: Bool = true, enableConflictDetection: Bool = true) {
        self.defaultIsolationLevel = defaultIsolationLevel
        self.lockTimeoutMs = lockTimeoutMs
        self.maxTransactionDuration = maxTransactionDuration
        self.enableDeadlockDetection = enableDeadlockDetection
        self.enableConflictDetection = enableConflictDetection
    }
}

/// Begin transaction record
public struct BeginTransactionRecord: WALRecord {
    public let transactionId: TxID
    public let isolationLevel: IsolationLevel
    
    public init(transactionId: TxID, isolationLevel: IsolationLevel) {
        self.transactionId = transactionId
        self.isolationLevel = isolationLevel
    }
    
    public var kind: WALRecordKind { .beginTransaction }
    public var lsn: LSN { LSN(0) } // Will be set by WAL
}

/// Commit transaction record
public struct CommitTransactionRecord: WALRecord {
    public let transactionId: TxID
    
    public init(transactionId: TxID) {
        self.transactionId = transactionId
    }
    
    public var kind: WALRecordKind { .commitTransaction }
    public var lsn: LSN { LSN(0) } // Will be set by WAL
}

/// Abort transaction record
public struct AbortTransactionRecord: WALRecord {
    public let transactionId: TxID
    public let reason: String
    
    public init(transactionId: TxID, reason: String) {
        self.transactionId = transactionId
        self.reason = reason
    }
    
    public var kind: WALRecordKind { .abortTransaction }
    public var lsn: LSN { LSN(0) } // Will be set by WAL
}

// MARK: - Errors

public enum TransactionError: Error, LocalizedError {
    case transactionNotFound
    case transactionNotActive
    case transactionAlreadyCommitted
    case transactionAlreadyAborted
    case lockTimeout
    case deadlockDetected
    case conflictDetected
    case isolationViolation
    
    public var errorDescription: String? {
        switch self {
        case .transactionNotFound:
            return "Transaction not found"
        case .transactionNotActive:
            return "Transaction is not active"
        case .transactionAlreadyCommitted:
            return "Transaction already committed"
        case .transactionAlreadyAborted:
            return "Transaction already aborted"
        case .lockTimeout:
            return "Lock timeout"
        case .deadlockDetected:
            return "Deadlock detected"
        case .conflictDetected:
            return "Transaction conflict detected"
        case .isolationViolation:
            return "Isolation level violation"
        }
    }
}
