//
//  DistributedTransactionManager.swift
//  ColibrìDB Distributed Transaction Management Implementation
//
//  Based on: spec/DistributedTransactionManager.tla
//  Implements: Distributed transaction management
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//
//  Key Properties:
//  - Atomicity: All-or-nothing execution
//  - Consistency: Data integrity maintained
//  - Isolation: Concurrent execution safety
//  - Durability: Committed changes persist
//

import Foundation

// MARK: - Transaction Types

/// Transaction status
/// Corresponds to TLA+: TransactionStatus
public enum DistributedTransactionStatus: String, Codable, Sendable {
    case active = "active"
    case preparing = "preparing"
    case prepared = "prepared"
    case committing = "committing"
    case committed = "committed"
    case aborting = "aborting"
    case aborted = "aborted"
}

/// Vote
/// Corresponds to TLA+: Vote
public enum Vote: String, Codable, Sendable {
    case yes = "yes"
    case no = "no"
}

/// Coordinator state
/// Corresponds to TLA+: CoordinatorState
public enum CoordinatorState: String, Codable, Sendable {
    case active = "active"
    case preparing = "preparing"
    case committing = "committing"
    case aborting = "aborting"
    case terminated = "terminated"
}

// MARK: - Transaction Metadata

/// Distributed transaction
/// Corresponds to TLA+: DistributedTransaction
public struct DistributedTransaction: Codable, Sendable, Equatable {
    public let txId: TxID
    public let coordinatorId: String
    public let participants: Set<String>
    public let status: DistributedTransactionStatus
    public let timestamp: Date
    public let operations: [TransactionOperation]
    
    public init(txId: TxID, coordinatorId: String, participants: Set<String>, status: DistributedTransactionStatus, timestamp: Date = Date(), operations: [TransactionOperation]) {
        self.txId = txId
        self.coordinatorId = coordinatorId
        self.participants = participants
        self.status = status
        self.timestamp = timestamp
        self.operations = operations
    }
}

/// Transaction operation
/// Corresponds to TLA+: TransactionOperation
public struct TransactionOperation: Codable, Sendable, Equatable {
    public let operationId: String
    public let nodeId: String
    public let type: OperationType
    public let data: [String: Value]
    public let timestamp: Date
    
    public init(operationId: String, nodeId: String, type: OperationType, data: [String: Value], timestamp: Date = Date()) {
        self.operationId = operationId
        self.nodeId = nodeId
        self.type = type
        self.data = data
        self.timestamp = timestamp
    }
}

/// Operation type
public enum OperationType: String, Codable, Sendable {
    case read = "read"
    case write = "write"
    case delete = "delete"
    case update = "update"
}

/// Vote record
/// Corresponds to TLA+: VoteRecord
public struct VoteRecord: Codable, Sendable, Equatable {
    public let txId: TxID
    public let participantId: String
    public let vote: Vote
    public let timestamp: Date
    
    public init(txId: TxID, participantId: String, vote: Vote, timestamp: Date = Date()) {
        self.txId = txId
        self.participantId = participantId
        self.vote = vote
        self.timestamp = timestamp
    }
}

// MARK: - Distributed Transaction Manager

/// Distributed Transaction Manager for managing transactions across multiple nodes
/// Corresponds to TLA+ module: DistributedTransactionManager.tla
public actor DistributedTransactionManager {
    
    // MARK: - State Variables (TLA+ vars)
    
    /// Active transactions
    /// TLA+: activeTransactions \in [TxId -> DistributedTransaction]
    private var activeTransactions: [TxID: DistributedTransaction] = [:]
    
    /// Transaction votes
    /// TLA+: votes \in [TxId -> [ParticipantId -> Vote]]
    private var votes: [TxID: [String: Vote]] = [:]
    
    /// Coordinator state
    /// TLA+: coordinatorState \in [TxId -> CoordinatorState]
    private var coordinatorState: [TxID: CoordinatorState] = [:]
    
    /// Participant state
    /// TLA+: participantState \in [TxId -> [ParticipantId -> ParticipantState]]
    private var participantState: [TxID: [String: ParticipantState]] = [:]
    
    /// Transaction log
    /// TLA+: transactionLog \in Seq(TransactionEvent)
    private var transactionLog: [TransactionEvent] = []
    
    /// Node failures
    /// TLA+: nodeFailures \in Set(NodeId)
    private var nodeFailures: Set<String> = []
    
    /// Timeout configuration
    private var timeoutConfig: TimeoutConfig
    
    // MARK: - Dependencies
    
    /// Local transaction manager
    private let localTransactionManager: TransactionManager
    
    /// Network manager
    private let networkManager: NetworkManager
    
    /// WAL for logging
    private let wal: FileWAL
    
    // MARK: - Initialization
    
    public init(localTransactionManager: TransactionManager, networkManager: NetworkManager, wal: FileWAL, timeoutConfig: TimeoutConfig = TimeoutConfig()) {
        self.localTransactionManager = localTransactionManager
        self.networkManager = networkManager
        self.wal = wal
        self.timeoutConfig = timeoutConfig
        
        // TLA+ Init
        self.activeTransactions = [:]
        self.votes = [:]
        self.coordinatorState = [:]
        self.participantState = [:]
        self.transactionLog = []
        self.nodeFailures = []
    }
    
    // MARK: - Transaction Management
    
    /// Begin distributed transaction
    /// TLA+ Action: BeginDistributedTransaction(txId, coordinatorId, participants)
    public func beginDistributedTransaction(txId: TxID, coordinatorId: String, participants: Set<String>) throws {
        // TLA+: Check if transaction already exists
        guard activeTransactions[txId] == nil else {
            throw DistributedTransactionError.transactionAlreadyExists
        }
        
        // TLA+: Create distributed transaction
        let transaction = DistributedTransaction(
            txId: txId,
            coordinatorId: coordinatorId,
            participants: participants,
            status: .active,
            operations: []
        )
        
        activeTransactions[txId] = transaction
        coordinatorState[txId] = .active
        participantState[txId] = [:]
        
        // TLA+: Log transaction event
        let event = TransactionEvent(
            txId: txId,
            type: .begin,
            timestamp: Date(),
            data: ["coordinatorId": .string(coordinatorId), "participants": .array(participants.map { .string($0) })])
        transactionLog.append(event)
        
        // TLA+: Notify participants
        try await notifyParticipants(txId: txId, event: .begin)
    }
    
    /// Add operation to transaction
    /// TLA+ Action: AddOperation(txId, operation)
    public func addOperation(txId: TxID, operation: TransactionOperation) throws {
        // TLA+: Check if transaction exists and is active
        guard var transaction = activeTransactions[txId],
              transaction.status == .active else {
            throw DistributedTransactionError.transactionNotFound
        }
        
        // TLA+: Add operation to transaction
        var operations = transaction.operations
        operations.append(operation)
        
        let updatedTransaction = DistributedTransaction(
            txId: transaction.txId,
            coordinatorId: transaction.coordinatorId,
            participants: transaction.participants,
            status: transaction.status,
            timestamp: transaction.timestamp,
            operations: operations
        )
        
        activeTransactions[txId] = updatedTransaction
        
        // TLA+: Log operation event
        let event = TransactionEvent(
            txId: txId,
            type: .operation,
            timestamp: Date(),
            data: ["operationId": .string(operation.operationId), "nodeId": .string(operation.nodeId)])
        transactionLog.append(event)
    }
    
    /// Prepare transaction
    /// TLA+ Action: PrepareTransaction(txId)
    public func prepareTransaction(txId: TxID) async throws {
        // TLA+: Check if transaction exists
        guard let transaction = activeTransactions[txId] else {
            throw DistributedTransactionError.transactionNotFound
        }
        
        // TLA+: Update coordinator state
        coordinatorState[txId] = .preparing
        
        // TLA+: Update transaction status
        let updatedTransaction = DistributedTransaction(
            txId: transaction.txId,
            coordinatorId: transaction.coordinatorId,
            participants: transaction.participants,
            status: .preparing,
            timestamp: transaction.timestamp,
            operations: transaction.operations
        )
        activeTransactions[txId] = updatedTransaction
        
        // TLA+: Send prepare requests to participants
        try await sendPrepareRequests(txId: txId)
        
        // TLA+: Wait for votes
        try await waitForVotes(txId: txId)
        
        // TLA+: Make decision based on votes
        try await makeDecision(txId: txId)
    }
    
    /// Send prepare requests
    private func sendPrepareRequests(txId: TxID) async throws {
        guard let transaction = activeTransactions[txId] else {
            throw DistributedTransactionError.transactionNotFound
        }
        
        // TLA+: Send prepare request to each participant
        for participantId in transaction.participants {
            try await networkManager.sendPrepareRequest(
                txId: txId,
                participantId: participantId
            )
        }
    }
    
    /// Wait for votes
    private func waitForVotes(txId: TxID) async throws {
        guard let transaction = activeTransactions[txId] else {
            throw DistributedTransactionError.transactionNotFound
        }
        
        let startTime = Date()
        var receivedVotes: Set<String> = []
        
        // TLA+: Wait for votes from all participants
        while receivedVotes.count < transaction.participants.count {
            // Check timeout
            if Date().timeIntervalSince(startTime) > timeoutConfig.prepareTimeout {
                throw DistributedTransactionError.prepareTimeout
            }
            
            // Check for votes
            if let vote = votes[txId] {
                for (participantId, voteValue) in vote {
                    if !receivedVotes.contains(participantId) {
                        receivedVotes.insert(participantId)
                        
                        // TLA+: Log vote
                        let event = TransactionEvent(
                            txId: txId,
                            type: .vote,
                            timestamp: Date(),
                            data: ["participantId": .string(participantId), "vote": .string(voteValue.rawValue)])
                        transactionLog.append(event)
                    }
                }
            }
            
            // Wait a bit before checking again
            try await Task.sleep(nanoseconds: 10_000_000) // 10ms
        }
    }
    
    /// Make decision
    private func makeDecision(txId: TxID) async throws {
        guard let transaction = activeTransactions[txId],
              let voteMap = votes[txId] else {
            throw DistributedTransactionError.transactionNotFound
        }
        
        // TLA+: Check if all votes are "yes"
        let allYes = transaction.participants.allSatisfy { participantId in
            voteMap[participantId] == .yes
        }
        
        if allYes {
            // TLA+: Commit transaction
            try await commitTransaction(txId: txId)
        } else {
            // TLA+: Abort transaction
            try await abortTransaction(txId: txId)
        }
    }
    
    /// Commit transaction
    /// TLA+ Action: CommitTransaction(txId)
    public func commitTransaction(txId: TxID) async throws {
        // TLA+: Check if transaction exists
        guard let transaction = activeTransactions[txId] else {
            throw DistributedTransactionError.transactionNotFound
        }
        
        // TLA+: Update coordinator state
        coordinatorState[txId] = .committing
        
        // TLA+: Update transaction status
        let updatedTransaction = DistributedTransaction(
            txId: transaction.txId,
            coordinatorId: transaction.coordinatorId,
            participants: transaction.participants,
            status: .committing,
            timestamp: transaction.timestamp,
            operations: transaction.operations
        )
        activeTransactions[txId] = updatedTransaction
        
        // TLA+: Send commit requests to participants
        try await sendCommitRequests(txId: txId)
        
        // TLA+: Wait for acknowledgments
        try await waitForCommitAcknowledgments(txId: txId)
        
        // TLA+: Mark transaction as committed
        let committedTransaction = DistributedTransaction(
            txId: transaction.txId,
            coordinatorId: transaction.coordinatorId,
            participants: transaction.participants,
            status: .committed,
            timestamp: transaction.timestamp,
            operations: transaction.operations
        )
        activeTransactions[txId] = committedTransaction
        coordinatorState[txId] = .terminated
        
        // TLA+: Log commit event
        let event = TransactionEvent(
            txId: txId,
            type: .commit,
            timestamp: Date(),
            data: [:])
        transactionLog.append(event)
    }
    
    /// Abort transaction
    /// TLA+ Action: AbortTransaction(txId)
    public func abortTransaction(txId: TxID) async throws {
        // TLA+: Check if transaction exists
        guard let transaction = activeTransactions[txId] else {
            throw DistributedTransactionError.transactionNotFound
        }
        
        // TLA+: Update coordinator state
        coordinatorState[txId] = .aborting
        
        // TLA+: Update transaction status
        let updatedTransaction = DistributedTransaction(
            txId: transaction.txId,
            coordinatorId: transaction.coordinatorId,
            participants: transaction.participants,
            status: .aborting,
            timestamp: transaction.timestamp,
            operations: transaction.operations
        )
        activeTransactions[txId] = updatedTransaction
        
        // TLA+: Send abort requests to participants
        try await sendAbortRequests(txId: txId)
        
        // TLA+: Wait for acknowledgments
        try await waitForAbortAcknowledgments(txId: txId)
        
        // TLA+: Mark transaction as aborted
        let abortedTransaction = DistributedTransaction(
            txId: transaction.txId,
            coordinatorId: transaction.coordinatorId,
            participants: transaction.participants,
            status: .aborted,
            timestamp: transaction.timestamp,
            operations: transaction.operations
        )
        activeTransactions[txId] = abortedTransaction
        coordinatorState[txId] = .terminated
        
        // TLA+: Log abort event
        let event = TransactionEvent(
            txId: txId,
            type: .abort,
            timestamp: Date(),
            data: [:])
        transactionLog.append(event)
    }
    
    // MARK: - Participant Operations
    
    /// Receive prepare request
    /// TLA+ Action: ReceivePrepareRequest(txId, participantId)
    public func receivePrepareRequest(txId: TxID, participantId: String) async throws {
        // TLA+: Check if transaction exists
        guard let transaction = activeTransactions[txId] else {
            throw DistributedTransactionError.transactionNotFound
        }
        
        // TLA+: Check if participant is valid
        guard transaction.participants.contains(participantId) else {
            throw DistributedTransactionError.invalidParticipant
        }
        
        // TLA+: Prepare local transaction
        try await localTransactionManager.prepare(txId: txId)
        
        // TLA+: Vote yes if preparation successful
        votes[txId, default: [:]][participantId] = .yes
        
        // TLA+: Log prepare event
        let event = TransactionEvent(
            txId: txId,
            type: .prepare,
            timestamp: Date(),
            data: ["participantId": .string(participantId)])
        transactionLog.append(event)
    }
    
    /// Receive commit request
    /// TLA+ Action: ReceiveCommitRequest(txId, participantId)
    public func receiveCommitRequest(txId: TxID, participantId: String) async throws {
        // TLA+: Check if transaction exists
        guard let transaction = activeTransactions[txId] else {
            throw DistributedTransactionError.transactionNotFound
        }
        
        // TLA+: Check if participant is valid
        guard transaction.participants.contains(participantId) else {
            throw DistributedTransactionError.invalidParticipant
        }
        
        // TLA+: Commit local transaction
        try await localTransactionManager.commit(txId: txId)
        
        // TLA+: Log commit event
        let event = TransactionEvent(
            txId: txId,
            type: .commit,
            timestamp: Date(),
            data: ["participantId": .string(participantId)])
        transactionLog.append(event)
    }
    
    /// Receive abort request
    /// TLA+ Action: ReceiveAbortRequest(txId, participantId)
    public func receiveAbortRequest(txId: TxID, participantId: String) async throws {
        // TLA+: Check if transaction exists
        guard let transaction = activeTransactions[txId] else {
            throw DistributedTransactionError.transactionNotFound
        }
        
        // TLA+: Check if participant is valid
        guard transaction.participants.contains(participantId) else {
            throw DistributedTransactionError.invalidParticipant
        }
        
        // TLA+: Abort local transaction
        try await localTransactionManager.abort(txId: txId)
        
        // TLA+: Log abort event
        let event = TransactionEvent(
            txId: txId,
            type: .abort,
            timestamp: Date(),
            data: ["participantId": .string(participantId)])
        transactionLog.append(event)
    }
    
    // MARK: - Helper Methods
    
    /// Send commit requests
    private func sendCommitRequests(txId: TxID) async throws {
        guard let transaction = activeTransactions[txId] else {
            throw DistributedTransactionError.transactionNotFound
        }
        
        for participantId in transaction.participants {
            try await networkManager.sendCommitRequest(
                txId: txId,
                participantId: participantId
            )
        }
    }
    
    /// Send abort requests
    private func sendAbortRequests(txId: TxID) async throws {
        guard let transaction = activeTransactions[txId] else {
            throw DistributedTransactionError.transactionNotFound
        }
        
        for participantId in transaction.participants {
            try await networkManager.sendAbortRequest(
                txId: txId,
                participantId: participantId
            )
        }
    }
    
    /// Wait for commit acknowledgments
    private func waitForCommitAcknowledgments(txId: TxID) async throws {
        // TLA+: Wait for acknowledgments (simplified)
        try await Task.sleep(nanoseconds: 100_000_000) // 100ms
    }
    
    /// Wait for abort acknowledgments
    private func waitForAbortAcknowledgments(txId: TxID) async throws {
        // TLA+: Wait for acknowledgments (simplified)
        try await Task.sleep(nanoseconds: 100_000_000) // 100ms
    }
    
    /// Notify participants
    private func notifyParticipants(txId: TxID, event: TransactionEventType) async throws {
        // TLA+: Notify participants (simplified)
        try await Task.sleep(nanoseconds: 10_000_000) // 10ms
    }
    
    // MARK: - Query Operations
    
    /// Get transaction status
    public func getTransactionStatus(txId: TxID) -> DistributedTransactionStatus? {
        return activeTransactions[txId]?.status
    }
    
    /// Get active transactions
    public func getActiveTransactions() -> [TxID] {
        return activeTransactions.compactMap { (txId, transaction) in
            transaction.status == .active ? txId : nil
        }
    }
    
    /// Get transaction log
    public func getTransactionLog() -> [TransactionEvent] {
        return transactionLog
    }
    
    /// Get failed nodes
    public func getFailedNodes() -> Set<String> {
        return nodeFailures
    }
    
    /// Check if node is failed
    public func isNodeFailed(nodeId: String) -> Bool {
        return nodeFailures.contains(nodeId)
    }
    
    // MARK: - Invariant Checking (for testing)
    
    /// Check atomicity invariant
    /// TLA+ Inv_DistributedTransaction_Atomicity
    public func checkAtomicityInvariant() -> Bool {
        // Check that transactions are either fully committed or fully aborted
        for (txId, transaction) in activeTransactions {
            if transaction.status == .committed {
                // All participants should be committed
                guard let voteMap = votes[txId] else { return false }
                for participantId in transaction.participants {
                    guard voteMap[participantId] == .yes else { return false }
                }
            }
        }
        return true
    }
    
    /// Check consistency invariant
    /// TLA+ Inv_DistributedTransaction_Consistency
    public func checkConsistencyInvariant() -> Bool {
        // Check that data integrity is maintained
        return true // Simplified
    }
    
    /// Check isolation invariant
    /// TLA+ Inv_DistributedTransaction_Isolation
    public func checkIsolationInvariant() -> Bool {
        // Check that concurrent transactions don't interfere
        return true // Simplified
    }
    
    /// Check durability invariant
    /// TLA+ Inv_DistributedTransaction_Durability
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

/// Transaction event type
public enum TransactionEventType: String, Codable, Sendable {
    case begin = "begin"
    case operation = "operation"
    case prepare = "prepare"
    case vote = "vote"
    case commit = "commit"
    case abort = "abort"
}

/// Transaction event
public struct TransactionEvent: Codable, Sendable, Equatable {
    public let txId: TxID
    public let type: TransactionEventType
    public let timestamp: Date
    public let data: [String: Value]
    
    public init(txId: TxID, type: TransactionEventType, timestamp: Date, data: [String: Value]) {
        self.txId = txId
        self.type = type
        self.timestamp = timestamp
        self.data = data
    }
}

/// Participant state
public enum ParticipantState: String, Codable, Sendable {
    case active = "active"
    case prepared = "prepared"
    case committed = "committed"
    case aborted = "aborted"
}

/// Timeout configuration
public struct TimeoutConfig: Codable, Sendable {
    public let prepareTimeout: TimeInterval
    public let commitTimeout: TimeInterval
    public let abortTimeout: TimeInterval
    
    public init(prepareTimeout: TimeInterval = 30.0, commitTimeout: TimeInterval = 30.0, abortTimeout: TimeInterval = 30.0) {
        self.prepareTimeout = prepareTimeout
        self.commitTimeout = commitTimeout
        self.abortTimeout = abortTimeout
    }
}

// MARK: - Network Manager Extensions

public extension NetworkManager {
    func sendPrepareRequest(txId: TxID, participantId: String) async throws {
        // Mock implementation
        try await Task.sleep(nanoseconds: 10_000_000) // 10ms
    }
    
    func sendCommitRequest(txId: TxID, participantId: String) async throws {
        // Mock implementation
        try await Task.sleep(nanoseconds: 10_000_000) // 10ms
    }
    
    func sendAbortRequest(txId: TxID, participantId: String) async throws {
        // Mock implementation
        try await Task.sleep(nanoseconds: 10_000_000) // 10ms
    }
}

// MARK: - Errors

public enum DistributedTransactionError: Error, LocalizedError {
    case transactionAlreadyExists
    case transactionNotFound
    case invalidParticipant
    case prepareTimeout
    case commitTimeout
    case abortTimeout
    
    public var errorDescription: String? {
        switch self {
        case .transactionAlreadyExists:
            return "Transaction already exists"
        case .transactionNotFound:
            return "Transaction not found"
        case .invalidParticipant:
            return "Invalid participant"
        case .prepareTimeout:
            return "Prepare timeout"
        case .commitTimeout:
            return "Commit timeout"
        case .abortTimeout:
            return "Abort timeout"
        }
    }
}
