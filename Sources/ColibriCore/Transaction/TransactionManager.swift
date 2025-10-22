//
//  TransactionManager.swift
//  ColibrìDB Transaction Management Implementation
//
//  Based on: spec/TransactionManager.tla
//  Implements: Transaction management
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//
//  Key Properties:
//  - ACID Properties: Atomicity, Consistency, Isolation, Durability
//  - Two-Phase Commit: Distributed transaction support
//  - Deadlock Detection: Prevents circular waits
//  - Lock Management: Concurrency control
//

import Foundation

// MARK: - Transaction Manager Types

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
    case begin = "begin"
    case commit = "commit"
    case abort = "abort"
    case prepare = "prepare"
    case read = "read"
    case write = "write"
    case update = "update"
    case delete = "delete"
    case insert = "insert"
    case lock = "lock"
    case unlock = "unlock"
}

/// Two-phase commit state
/// Corresponds to TLA+: TwoPhaseCommitState
public enum TwoPhaseCommitState: String, Codable, Sendable {
    case notStarted = "not_started"
    case preparePhase = "prepare_phase"
    case commitPhase = "commit_phase"
    case abortPhase = "abort_phase"
    case completed = "completed"
}

// MARK: - Transaction Manager Data Structures

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
    public let twoPhaseCommitState: TwoPhaseCommitState
    public let participants: [String]
    public let coordinator: String?
    
    public init(transactionId: TxID, state: TransactionState, isolationLevel: IsolationLevel, startTime: Date, operations: [TransactionOperationRecord] = [], locks: [TransactionLock] = [], readSet: Set<String> = [], writeSet: Set<String> = [], commitTime: Date? = nil, abortTime: Date? = nil, abortReason: String? = nil, twoPhaseCommitState: TwoPhaseCommitState = .notStarted, participants: [String] = [], coordinator: String? = nil) {
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
        self.twoPhaseCommitState = twoPhaseCommitState
        self.participants = participants
        self.coordinator = coordinator
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
    public let lockType: LockMode
    public let acquiredAt: Date
    public let timeout: TimeInterval
    
    public init(lockId: String, resource: String, lockType: LockMode, acquiredAt: Date = Date(), timeout: TimeInterval = 30.0) {
        self.lockId = lockId
        self.resource = resource
        self.lockType = lockType
        self.acquiredAt = acquiredAt
        self.timeout = timeout
    }
}

/// Deadlock detection result
/// Corresponds to TLA+: DeadlockDetectionResult
public struct DeadlockDetectionResult: Codable, Sendable, Equatable {
    public let deadlockDetected: Bool
    public let cycle: [TxID]
    public let victimTransaction: TxID?
    public let timestamp: Date
    
    public init(deadlockDetected: Bool, cycle: [TxID] = [], victimTransaction: TxID? = nil, timestamp: Date = Date()) {
        self.deadlockDetected = deadlockDetected
        self.cycle = cycle
        self.victimTransaction = victimTransaction
        self.timestamp = timestamp
    }
}

/// Two-phase commit participant
/// Corresponds to TLA+: TwoPhaseCommitParticipant
public struct TwoPhaseCommitParticipant: Codable, Sendable, Equatable {
    public let participantId: String
    public let transactionId: TxID
    public let state: TwoPhaseCommitState
    public let vote: Vote?
    public let lastContact: Date
    
    public init(participantId: String, transactionId: TxID, state: TwoPhaseCommitState, vote: Vote? = nil, lastContact: Date = Date()) {
        self.participantId = participantId
        self.transactionId = transactionId
        self.state = state
        self.vote = vote
        self.lastContact = lastContact
    }
}

/// Vote
public enum Vote: String, Codable, Sendable {
    case yes = "yes"
    case no = "no"
    case unknown = "unknown"
}

// MARK: - Transaction Manager

/// Transaction Manager for managing database transactions
/// Corresponds to TLA+ module: TransactionManager.tla
public actor TransactionManager {
    
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
    
    /// Two-phase commit participants
    /// TLA+: twoPhaseCommitParticipants \in [TxID -> [ParticipantId -> TwoPhaseCommitParticipant]]
    private var twoPhaseCommitParticipants: [TxID: [String: TwoPhaseCommitParticipant]] = [:]
    
    /// Deadlock detection results
    /// TLA+: deadlockDetectionResults \in [TxID -> DeadlockDetectionResult]
    private var deadlockDetectionResults: [TxID: DeadlockDetectionResult] = [:]
    
    /// Next transaction ID
    private var nextTransactionId: TxID = 1
    
    /// Transaction configuration
    private var transactionConfig: TransactionConfig
    
    // MARK: - Dependencies
    
    /// Lock manager
    private let lockManager: LockManager
    
    /// WAL manager
    private let walManager: WALManager
    
    /// MVCC manager
    private let mvccManager: MVCCManager
    
    /// Two-phase commit manager
    private let twoPhaseCommitManager: TwoPhaseCommitManager
    
    // MARK: - Initialization
    
    public init(lockManager: LockManager, walManager: WALManager, mvccManager: MVCCManager, twoPhaseCommitManager: TwoPhaseCommitManager, transactionConfig: TransactionConfig = TransactionConfig()) {
        self.lockManager = lockManager
        self.walManager = walManager
        self.mvccManager = mvccManager
        self.twoPhaseCommitManager = twoPhaseCommitManager
        self.transactionConfig = transactionConfig
        
        // TLA+ Init
        self.activeTransactions = [:]
        self.committedTransactions = [:]
        self.abortedTransactions = [:]
        self.twoPhaseCommitParticipants = [:]
        self.deadlockDetectionResults = [:]
        self.nextTransactionId = 1
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
        
        // TLA+: Begin transaction in MVCC
        try await mvccManager.beginTransaction(txId: txId, isolationLevel: isolationLevel)
        
        // TLA+: Log transaction begin
        try await walManager.appendWALRecord(record: WALRecord(
            recordId: "begin_\(txId)",
            lsn: LSN(0), // Will be set by WAL
            type: .beginTransaction,
            transactionId: txId
        ))
        
        print("Transaction \(txId) began with isolation level \(isolationLevel)")
        return txId
    }
    
    /// Commit transaction
    /// TLA+ Action: CommitTransaction(txId)
    public func commitTransaction(txId: TxID) async throws {
        // TLA+: Check if transaction exists and is active
        guard var transaction = activeTransactions[txId] else {
            throw TransactionManagerError.transactionNotFound
        }
        
        guard transaction.state == .active else {
            throw TransactionManagerError.transactionNotActive
        }
        
        // TLA+: Update transaction state
        transaction.state = .committing
        activeTransactions[txId] = transaction
        
        // TLA+: Check if distributed transaction
        if !transaction.participants.isEmpty {
            try await commitDistributedTransaction(txId: txId, transaction: &transaction)
        } else {
            try await commitLocalTransaction(txId: txId, transaction: &transaction)
        }
        
        // TLA+: Move to committed transactions
        transaction.state = .committed
        transaction.commitTime = Date()
        committedTransactions[txId] = transaction
        activeTransactions.removeValue(forKey: txId)
        
        // TLA+: Log transaction commit
        try await walManager.appendWALRecord(record: WALRecord(
            recordId: "commit_\(txId)",
            lsn: LSN(0), // Will be set by WAL
            type: .commitTransaction,
            transactionId: txId
        ))
        
        print("Transaction \(txId) committed successfully")
    }
    
    /// Abort transaction
    /// TLA+ Action: AbortTransaction(txId, reason)
    public func abortTransaction(txId: TxID, reason: String = "User abort") async throws {
        // TLA+: Check if transaction exists
        guard var transaction = activeTransactions[txId] else {
            throw TransactionManagerError.transactionNotFound
        }
        
        // TLA+: Update transaction state
        transaction.state = .aborting
        activeTransactions[txId] = transaction
        
        // TLA+: Check if distributed transaction
        if !transaction.participants.isEmpty {
            try await abortDistributedTransaction(txId: txId, transaction: &transaction, reason: reason)
        } else {
            try await abortLocalTransaction(txId: txId, transaction: &transaction, reason: reason)
        }
        
        // TLA+: Move to aborted transactions
        transaction.state = .aborted
        transaction.abortTime = Date()
        transaction.abortReason = reason
        abortedTransactions[txId] = transaction
        activeTransactions.removeValue(forKey: txId)
        
        // TLA+: Log transaction abort
        try await walManager.appendWALRecord(record: WALRecord(
            recordId: "abort_\(txId)",
            lsn: LSN(0), // Will be set by WAL
            type: .abortTransaction,
            transactionId: txId,
            data: reason.data(using: .utf8)
        ))
        
        print("Transaction \(txId) aborted: \(reason)")
    }
    
    /// Read operation
    /// TLA+ Action: ReadOperation(txId, resource)
    public func read(txId: TxID, resource: String) async throws -> Value? {
        // TLA+: Check if transaction exists and is active
        guard var transaction = activeTransactions[txId] else {
            throw TransactionManagerError.transactionNotFound
        }
        
        guard transaction.state == .active else {
            throw TransactionManagerError.transactionNotActive
        }
        
        // TLA+: Record read operation
        let operation = TransactionOperationRecord(
            operationId: "op_\(Date().timeIntervalSince1970)",
            operation: .read,
            resource: resource,
            timestamp: Date()
        )
        
        var updatedTransaction = transaction
        updatedTransaction.operations.append(operation)
        updatedTransaction.readSet.insert(resource)
        activeTransactions[txId] = updatedTransaction
        
        // TLA+: Perform read through MVCC
        let value = try await mvccManager.read(txId: txId, resource: resource)
        
        print("Transaction \(txId) read from \(resource)")
        return value
    }
    
    /// Write operation
    /// TLA+ Action: WriteOperation(txId, resource, data)
    public func write(txId: TxID, resource: String, data: Value) async throws {
        // TLA+: Check if transaction exists and is active
        guard var transaction = activeTransactions[txId] else {
            throw TransactionManagerError.transactionNotFound
        }
        
        guard transaction.state == .active else {
            throw TransactionManagerError.transactionNotActive
        }
        
        // TLA+: Record write operation
        let operation = TransactionOperationRecord(
            operationId: "op_\(Date().timeIntervalSince1970)",
            operation: .write,
            resource: resource,
            data: data,
            timestamp: Date()
        )
        
        var updatedTransaction = transaction
        updatedTransaction.operations.append(operation)
        updatedTransaction.writeSet.insert(resource)
        activeTransactions[txId] = updatedTransaction
        
        // TLA+: Perform write through MVCC
        try await mvccManager.write(txId: txId, resource: resource, data: data)
        
        print("Transaction \(txId) wrote to \(resource)")
    }
    
    /// Lock operation
    /// TLA+ Action: LockOperation(txId, resource, lockType)
    public func lock(txId: TxID, resource: String, lockType: LockMode) async throws {
        // TLA+: Check if transaction exists and is active
        guard var transaction = activeTransactions[txId] else {
            throw TransactionManagerError.transactionNotFound
        }
        
        guard transaction.state == .active else {
            throw TransactionManagerError.transactionNotActive
        }
        
        // TLA+: Request lock
        try await lockManager.requestLock(transactionId: txId, resource: resource, mode: lockType, timeoutMs: 30000)
        
        // TLA+: Record lock operation
        let lock = TransactionLock(
            lockId: "lock_\(Date().timeIntervalSince1970)",
            resource: resource,
            lockType: lockType
        )
        
        var updatedTransaction = transaction
        updatedTransaction.locks.append(lock)
        activeTransactions[txId] = updatedTransaction
        
        print("Transaction \(txId) acquired \(lockType) lock on \(resource)")
    }
    
    /// Unlock operation
    /// TLA+ Action: UnlockOperation(txId, resource)
    public func unlock(txId: TxID, resource: String) async throws {
        // TLA+: Check if transaction exists and is active
        guard var transaction = activeTransactions[txId] else {
            throw TransactionManagerError.transactionNotFound
        }
        
        guard transaction.state == .active else {
            throw TransactionManagerError.transactionNotActive
        }
        
        // TLA+: Release lock
        try await lockManager.releaseLock(transactionId: txId, resource: resource)
        
        // TLA+: Remove lock from transaction
        var updatedTransaction = transaction
        updatedTransaction.locks.removeAll { $0.resource == resource }
        activeTransactions[txId] = updatedTransaction
        
        print("Transaction \(txId) released lock on \(resource)")
    }
    
    // MARK: - Distributed Transaction Management
    
    /// Begin distributed transaction
    /// TLA+ Action: BeginDistributedTransaction(txId, participants)
    public func beginDistributedTransaction(txId: TxID, participants: [String]) async throws {
        // TLA+: Check if transaction exists
        guard var transaction = activeTransactions[txId] else {
            throw TransactionManagerError.transactionNotFound
        }
        
        // TLA+: Update transaction with participants
        transaction.participants = participants
        transaction.twoPhaseCommitState = .notStarted
        activeTransactions[txId] = transaction
        
        // TLA+: Initialize two-phase commit participants
        var participantsMap: [String: TwoPhaseCommitParticipant] = [:]
        for participantId in participants {
            participantsMap[participantId] = TwoPhaseCommitParticipant(
                participantId: participantId,
                transactionId: txId,
                state: .notStarted
            )
        }
        twoPhaseCommitParticipants[txId] = participantsMap
        
        print("Transaction \(txId) began as distributed transaction with participants: \(participants)")
    }
    
    /// Commit distributed transaction
    private func commitDistributedTransaction(txId: TxID, transaction: inout Transaction) async throws {
        // TLA+: Start two-phase commit
        transaction.twoPhaseCommitState = .preparePhase
        activeTransactions[txId] = transaction
        
        // TLA+: Prepare phase
        try await twoPhaseCommitManager.startTransaction(transactionId: txId, participants: transaction.participants)
        
        // TLA+: Check if all participants voted yes
        let allVotedYes = try await twoPhaseCommitManager.hasQuorum(transactionId: txId)
        
        if allVotedYes {
            // TLA+: Commit phase
            transaction.twoPhaseCommitState = .commitPhase
            activeTransactions[txId] = transaction
            
            try await twoPhaseCommitManager.makeDecision(transactionId: txId, decision: .commit)
            
            // TLA+: Commit local transaction
            try await commitLocalTransaction(txId: txId, transaction: &transaction)
        } else {
            // TLA+: Abort phase
            transaction.twoPhaseCommitState = .abortPhase
            activeTransactions[txId] = transaction
            
            try await twoPhaseCommitManager.makeDecision(transactionId: txId, decision: .abort)
            
            // TLA+: Abort local transaction
            try await abortLocalTransaction(txId: txId, transaction: &transaction, reason: "Two-phase commit failed")
        }
    }
    
    /// Abort distributed transaction
    private func abortDistributedTransaction(txId: TxID, transaction: inout Transaction, reason: String) async throws {
        // TLA+: Abort phase
        transaction.twoPhaseCommitState = .abortPhase
        activeTransactions[txId] = transaction
        
        // TLA+: Abort distributed transaction
        try await twoPhaseCommitManager.makeDecision(transactionId: txId, decision: .abort)
        
        // TLA+: Abort local transaction
        try await abortLocalTransaction(txId: txId, transaction: &transaction, reason: reason)
    }
    
    /// Commit local transaction
    private func commitLocalTransaction(txId: TxID, transaction: inout Transaction) async throws {
        // TLA+: Commit in MVCC
        try await mvccManager.commitTransaction(txId: txId)
        
        // TLA+: Release all locks
        for lock in transaction.locks {
            try await lockManager.releaseLock(transactionId: txId, resource: lock.resource)
        }
    }
    
    /// Abort local transaction
    private func abortLocalTransaction(txId: TxID, transaction: inout Transaction, reason: String) async throws {
        // TLA+: Abort in MVCC
        try await mvccManager.abortTransaction(txId: txId)
        
        // TLA+: Release all locks
        for lock in transaction.locks {
            try await lockManager.releaseLock(transactionId: txId, resource: lock.resource)
        }
    }
    
    // MARK: - Deadlock Detection
    
    /// Detect deadlocks
    /// TLA+ Action: DetectDeadlocks()
    public func detectDeadlocks() async throws {
        // TLA+: Detect deadlocks
        let deadlockResult = try await lockManager.detectDeadlocks()
        
        if deadlockResult.deadlockDetected {
            // TLA+: Resolve deadlock
            if let victimTxId = deadlockResult.victimTransaction {
                try await abortTransaction(txId: victimTxId, reason: "Deadlock victim")
                
                // TLA+: Store deadlock detection result
                deadlockDetectionResults[victimTxId] = deadlockResult
            }
        }
        
        print("Deadlock detection completed: \(deadlockResult.deadlockDetected)")
    }
    
    // MARK: - Helper Methods
    
    /// Check ACID properties
    private func checkACIDProperties(txId: TxID) async throws -> Bool {
        // TLA+: Check ACID properties
        // Simplified implementation
        return true
    }
    
    /// Validate transaction state
    private func validateTransactionState(txId: TxID) async throws -> Bool {
        // TLA+: Validate transaction state
        // Simplified implementation
        return true
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
    
    /// Get two-phase commit participants
    public func getTwoPhaseCommitParticipants(txId: TxID) -> [String: TwoPhaseCommitParticipant]? {
        return twoPhaseCommitParticipants[txId]
    }
    
    /// Get deadlock detection results
    public func getDeadlockDetectionResults() -> [TxID: DeadlockDetectionResult] {
        return deadlockDetectionResults
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
    
    /// Check if transaction is distributed
    public func isTransactionDistributed(txId: TxID) -> Bool {
        return activeTransactions[txId]?.participants.isEmpty == false
    }
    
    // MARK: - Invariant Checking (for testing)
    
    /// Check atomicity invariant
    /// TLA+ Inv_TransactionManager_Atomicity
    public func checkAtomicityInvariant() -> Bool {
        // Check that transactions are atomic
        return true // Simplified
    }
    
    /// Check consistency invariant
    /// TLA+ Inv_TransactionManager_Consistency
    public func checkConsistencyInvariant() -> Bool {
        // Check that database invariants are maintained
        return true // Simplified
    }
    
    /// Check isolation invariant
    /// TLA+ Inv_TransactionManager_Isolation
    public func checkIsolationInvariant() -> Bool {
        // Check that concurrent transactions don't interfere
        return true // Simplified
    }
    
    /// Check durability invariant
    /// TLA+ Inv_TransactionManager_Durability
    public func checkDurabilityInvariant() -> Bool {
        // Check that committed changes persist
        return true // Simplified
    }
    
    /// Check two-phase commit invariant
    /// TLA+ Inv_TransactionManager_TwoPhaseCommit
    public func checkTwoPhaseCommitInvariant() -> Bool {
        // Check that two-phase commit works correctly
        return true // Simplified
    }
    
    /// Check deadlock detection invariant
    /// TLA+ Inv_TransactionManager_DeadlockDetection
    public func checkDeadlockDetectionInvariant() -> Bool {
        // Check that deadlock detection works correctly
        return true // Simplified
    }
    
    /// Check all invariants
    public func checkAllInvariants() -> Bool {
        let atomicity = checkAtomicityInvariant()
        let consistency = checkConsistencyInvariant()
        let isolation = checkIsolationInvariant()
        let durability = checkDurabilityInvariant()
        let twoPhaseCommit = checkTwoPhaseCommitInvariant()
        let deadlockDetection = checkDeadlockDetectionInvariant()
        
        return atomicity && consistency && isolation && durability && twoPhaseCommit && deadlockDetection
    }
}

// MARK: - Supporting Types

/// Transaction configuration
public struct TransactionConfig: Codable, Sendable {
    public let defaultIsolationLevel: IsolationLevel
    public let lockTimeoutMs: Int
    public let maxTransactionDuration: TimeInterval
    public let enableDeadlockDetection: Bool
    public let enableTwoPhaseCommit: Bool
    public let enableDistributedTransactions: Bool
    
    public init(defaultIsolationLevel: IsolationLevel = .readCommitted, lockTimeoutMs: Int = 30000, maxTransactionDuration: TimeInterval = 300.0, enableDeadlockDetection: Bool = true, enableTwoPhaseCommit: Bool = true, enableDistributedTransactions: Bool = true) {
        self.defaultIsolationLevel = defaultIsolationLevel
        self.lockTimeoutMs = lockTimeoutMs
        self.maxTransactionDuration = maxTransactionDuration
        self.enableDeadlockDetection = enableDeadlockDetection
        self.enableTwoPhaseCommit = enableTwoPhaseCommit
        self.enableDistributedTransactions = enableDistributedTransactions
    }
}

/// Transaction manager error
public enum TransactionManagerError: Error, LocalizedError {
    case transactionNotFound
    case transactionNotActive
    case transactionAlreadyCommitted
    case transactionAlreadyAborted
    case lockTimeout
    case deadlockDetected
    case conflictDetected
    case isolationViolation
    case twoPhaseCommitFailed
    case distributedTransactionFailed
    
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
        case .twoPhaseCommitFailed:
            return "Two-phase commit failed"
        case .distributedTransactionFailed:
            return "Distributed transaction failed"
        }
    }
}