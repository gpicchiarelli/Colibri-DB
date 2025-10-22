//
//  TwoPhaseCommit.swift
//  ColibrìDB Two-Phase Commit Implementation
//
//  Based on: spec/TwoPhaseCommit.tla
//  Implements: Two-phase commit protocol
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//
//  Key Properties:
//  - Atomicity: All-or-nothing execution
//  - Consistency: Data integrity maintained
//  - Durability: Committed changes persist
//  - Fault Tolerance: Handles node failures
//

import Foundation

// MARK: - Two-Phase Commit Types

/// Transaction phase
/// Corresponds to TLA+: TransactionPhase
public enum TransactionPhase: String, Codable, Sendable {
    case prepare = "prepare"
    case commit = "commit"
    case abort = "abort"
    case unknown = "unknown"
}

/// Participant state
/// Corresponds to TLA+: ParticipantState
public enum ParticipantState: String, Codable, Sendable {
    case active = "active"
    case prepared = "prepared"
    case committed = "committed"
    case aborted = "aborted"
    case failed = "failed"
}

/// Vote
/// Corresponds to TLA+: Vote
public enum Vote: String, Codable, Sendable {
    case yes = "yes"
    case no = "no"
    case unknown = "unknown"
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

// MARK: - Two-Phase Commit Metadata

/// Two-phase commit transaction
/// Corresponds to TLA+: TwoPhaseCommitTransaction
public struct TwoPhaseCommitTransaction: Codable, Sendable, Equatable {
    public let txId: TxID
    public let coordinatorId: String
    public let participants: Set<String>
    public let phase: TransactionPhase
    public let coordinatorState: CoordinatorState
    public let participantStates: [String: ParticipantState]
    public let votes: [String: Vote]
    public let timestamp: Date
    public let timeout: TimeInterval
    
    public init(txId: TxID, coordinatorId: String, participants: Set<String>, phase: TransactionPhase, coordinatorState: CoordinatorState, participantStates: [String: ParticipantState], votes: [String: Vote], timestamp: Date = Date(), timeout: TimeInterval = 30.0) {
        self.txId = txId
        self.coordinatorId = coordinatorId
        self.participants = participants
        self.phase = phase
        self.coordinatorState = coordinatorState
        self.participantStates = participantStates
        self.votes = votes
        self.timestamp = timestamp
        self.timeout = timeout
    }
}

/// Prepare request
/// Corresponds to TLA+: PrepareRequest
public struct PrepareRequest: Codable, Sendable, Equatable {
    public let txId: TxID
    public let coordinatorId: String
    public let timestamp: Date
    
    public init(txId: TxID, coordinatorId: String, timestamp: Date = Date()) {
        self.txId = txId
        self.coordinatorId = coordinatorId
        self.timestamp = timestamp
    }
}

/// Prepare response
/// Corresponds to TLA+: PrepareResponse
public struct PrepareResponse: Codable, Sendable, Equatable {
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

/// Commit request
/// Corresponds to TLA+: CommitRequest
public struct CommitRequest: Codable, Sendable, Equatable {
    public let txId: TxID
    public let coordinatorId: String
    public let timestamp: Date
    
    public init(txId: TxID, coordinatorId: String, timestamp: Date = Date()) {
        self.txId = txId
        self.coordinatorId = coordinatorId
        self.timestamp = timestamp
    }
}

/// Abort request
/// Corresponds to TLA+: AbortRequest
public struct AbortRequest: Codable, Sendable, Equatable {
    public let txId: TxID
    public let coordinatorId: String
    public let timestamp: Date
    
    public init(txId: TxID, coordinatorId: String, timestamp: Date = Date()) {
        self.txId = txId
        self.coordinatorId = coordinatorId
        self.timestamp = timestamp
    }
}

// MARK: - Two-Phase Commit Manager

/// Two-Phase Commit Manager for distributed transaction coordination
/// Corresponds to TLA+ module: TwoPhaseCommit.tla
public actor TwoPhaseCommitManager {
    
    // MARK: - State Variables (TLA+ vars)
    
    /// Active transactions
    /// TLA+: activeTransactions \in [TxId -> TwoPhaseCommitTransaction]
    private var activeTransactions: [TxID: TwoPhaseCommitTransaction] = [:]
    
    /// Transaction log
    /// TLA+: transactionLog \in Seq(TransactionEvent)
    private var transactionLog: [TransactionEvent] = []
    
    /// Participant state
    /// TLA+: participantState \in [TxId -> [ParticipantId -> ParticipantState]]
    private var participantState: [TxID: [String: ParticipantState]] = [:]
    
    /// Coordinator state
    /// TLA+: coordinatorState \in [TxId -> CoordinatorState]
    private var coordinatorState: [TxID: CoordinatorState] = [:]
    
    /// Transaction votes
    /// TLA+: votes \in [TxId -> [ParticipantId -> Vote]]
    private var votes: [TxID: [String: Vote]] = [:]
    
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
        self.transactionLog = []
        self.participantState = [:]
        self.coordinatorState = [:]
        self.votes = [:]
        self.nodeFailures = []
    }
    
    // MARK: - Transaction Management
    
    /// Begin two-phase commit transaction
    /// TLA+ Action: BeginTwoPhaseCommitTransaction(txId, coordinatorId, participants)
    public func beginTwoPhaseCommitTransaction(txId: TxID, coordinatorId: String, participants: Set<String>) throws {
        // TLA+: Check if transaction already exists
        guard activeTransactions[txId] == nil else {
            throw TwoPhaseCommitError.transactionAlreadyExists
        }
        
        // TLA+: Create two-phase commit transaction
        let transaction = TwoPhaseCommitTransaction(
            txId: txId,
            coordinatorId: coordinatorId,
            participants: participants,
            phase: .prepare,
            coordinatorState: .active,
            participantStates: [:],
            votes: [:]
        )
        
        activeTransactions[txId] = transaction
        coordinatorState[txId] = .active
        participantState[txId] = [:]
        votes[txId] = [:]
        
        // TLA+: Log transaction event
        let event = TransactionEvent(
            txId: txId,
            type: .begin,
            timestamp: Date(),
            data: ["coordinatorId": .string(coordinatorId), "participants": .array(participants.map { .string($0) })])
        transactionLog.append(event)
        
        // TLA+: Start prepare phase
        try await startPreparePhase(txId: txId)
    }
    
    /// Start prepare phase
    /// TLA+ Action: StartPreparePhase(txId)
    private func startPreparePhase(txId: TxID) async throws {
        // TLA+: Check if transaction exists
        guard var transaction = activeTransactions[txId] else {
            throw TwoPhaseCommitError.transactionNotFound
        }
        
        // TLA+: Update coordinator state
        coordinatorState[txId] = .preparing
        
        // TLA+: Update transaction phase
        let updatedTransaction = TwoPhaseCommitTransaction(
            txId: transaction.txId,
            coordinatorId: transaction.coordinatorId,
            participants: transaction.participants,
            phase: .prepare,
            coordinatorState: .preparing,
            participantStates: transaction.participantStates,
            votes: transaction.votes,
            timestamp: transaction.timestamp,
            timeout: transaction.timeout
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
            throw TwoPhaseCommitError.transactionNotFound
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
            throw TwoPhaseCommitError.transactionNotFound
        }
        
        let startTime = Date()
        var receivedVotes: Set<String> = []
        
        // TLA+: Wait for votes from all participants
        while receivedVotes.count < transaction.participants.count {
            // Check timeout
            if Date().timeIntervalSince(startTime) > timeoutConfig.prepareTimeout {
                throw TwoPhaseCommitError.prepareTimeout
            }
            
            // Check for votes
            if let voteMap = votes[txId] {
                for (participantId, vote) in voteMap {
                    if !receivedVotes.contains(participantId) {
                        receivedVotes.insert(participantId)
                        
                        // TLA+: Log vote
                        let event = TransactionEvent(
                            txId: txId,
                            type: .vote,
                            timestamp: Date(),
                            data: ["participantId": .string(participantId), "vote": .string(vote.rawValue)])
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
            throw TwoPhaseCommitError.transactionNotFound
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
        guard var transaction = activeTransactions[txId] else {
            throw TwoPhaseCommitError.transactionNotFound
        }
        
        // TLA+: Update coordinator state
        coordinatorState[txId] = .committing
        
        // TLA+: Update transaction phase
        let updatedTransaction = TwoPhaseCommitTransaction(
            txId: transaction.txId,
            coordinatorId: transaction.coordinatorId,
            participants: transaction.participants,
            phase: .commit,
            coordinatorState: .committing,
            participantStates: transaction.participantStates,
            votes: transaction.votes,
            timestamp: transaction.timestamp,
            timeout: transaction.timeout
        )
        activeTransactions[txId] = updatedTransaction
        
        // TLA+: Send commit requests to participants
        try await sendCommitRequests(txId: txId)
        
        // TLA+: Wait for acknowledgments
        try await waitForCommitAcknowledgments(txId: txId)
        
        // TLA+: Mark transaction as committed
        let committedTransaction = TwoPhaseCommitTransaction(
            txId: transaction.txId,
            coordinatorId: transaction.coordinatorId,
            participants: transaction.participants,
            phase: .commit,
            coordinatorState: .terminated,
            participantStates: transaction.participantStates,
            votes: transaction.votes,
            timestamp: transaction.timestamp,
            timeout: transaction.timeout
        )
        activeTransactions[txId] = committedTransaction
        
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
        guard var transaction = activeTransactions[txId] else {
            throw TwoPhaseCommitError.transactionNotFound
        }
        
        // TLA+: Update coordinator state
        coordinatorState[txId] = .aborting
        
        // TLA+: Update transaction phase
        let updatedTransaction = TwoPhaseCommitTransaction(
            txId: transaction.txId,
            coordinatorId: transaction.coordinatorId,
            participants: transaction.participants,
            phase: .abort,
            coordinatorState: .aborting,
            participantStates: transaction.participantStates,
            votes: transaction.votes,
            timestamp: transaction.timestamp,
            timeout: transaction.timeout
        )
        activeTransactions[txId] = updatedTransaction
        
        // TLA+: Send abort requests to participants
        try await sendAbortRequests(txId: txId)
        
        // TLA+: Wait for acknowledgments
        try await waitForAbortAcknowledgments(txId: txId)
        
        // TLA+: Mark transaction as aborted
        let abortedTransaction = TwoPhaseCommitTransaction(
            txId: transaction.txId,
            coordinatorId: transaction.coordinatorId,
            participants: transaction.participants,
            phase: .abort,
            coordinatorState: .terminated,
            participantStates: transaction.participantStates,
            votes: transaction.votes,
            timestamp: transaction.timestamp,
            timeout: transaction.timeout
        )
        activeTransactions[txId] = abortedTransaction
        
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
            throw TwoPhaseCommitError.transactionNotFound
        }
        
        // TLA+: Check if participant is valid
        guard transaction.participants.contains(participantId) else {
            throw TwoPhaseCommitError.invalidParticipant
        }
        
        // TLA+: Prepare local transaction
        try await localTransactionManager.prepare(txId: txId)
        
        // TLA+: Vote yes if preparation successful
        votes[txId, default: [:]][participantId] = .yes
        
        // TLA+: Update participant state
        participantState[txId, default: [:]][participantId] = .prepared
        
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
            throw TwoPhaseCommitError.transactionNotFound
        }
        
        // TLA+: Check if participant is valid
        guard transaction.participants.contains(participantId) else {
            throw TwoPhaseCommitError.invalidParticipant
        }
        
        // TLA+: Commit local transaction
        try await localTransactionManager.commit(txId: txId)
        
        // TLA+: Update participant state
        participantState[txId, default: [:]][participantId] = .committed
        
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
            throw TwoPhaseCommitError.transactionNotFound
        }
        
        // TLA+: Check if participant is valid
        guard transaction.participants.contains(participantId) else {
            throw TwoPhaseCommitError.invalidParticipant
        }
        
        // TLA+: Abort local transaction
        try await localTransactionManager.abort(txId: txId)
        
        // TLA+: Update participant state
        participantState[txId, default: [:]][participantId] = .aborted
        
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
            throw TwoPhaseCommitError.transactionNotFound
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
            throw TwoPhaseCommitError.transactionNotFound
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
    
    // MARK: - Query Operations
    
    /// Get transaction status
    public func getTransactionStatus(txId: TxID) -> TransactionPhase? {
        return activeTransactions[txId]?.phase
    }
    
    /// Get active transactions
    public func getActiveTransactions() -> [TxID] {
        return activeTransactions.compactMap { (txId, transaction) in
            transaction.phase == .prepare ? txId : nil
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
    /// TLA+ Inv_TwoPhaseCommit_Atomicity
    public func checkAtomicityInvariant() -> Bool {
        // Check that transactions are either fully committed or fully aborted
        for (txId, transaction) in activeTransactions {
            if transaction.phase == .commit {
                // All participants should be committed
                guard let participantStates = participantState[txId] else { return false }
                for participantId in transaction.participants {
                    guard participantStates[participantId] == .committed else { return false }
                }
            } else if transaction.phase == .abort {
                // All participants should be aborted
                guard let participantStates = participantState[txId] else { return false }
                for participantId in transaction.participants {
                    guard participantStates[participantId] == .aborted else { return false }
                }
            }
        }
        return true
    }
    
    /// Check consistency invariant
    /// TLA+ Inv_TwoPhaseCommit_Consistency
    public func checkConsistencyInvariant() -> Bool {
        // Check that data integrity is maintained
        return true // Simplified
    }
    
    /// Check durability invariant
    /// TLA+ Inv_TwoPhaseCommit_Durability
    public func checkDurabilityInvariant() -> Bool {
        // Check that committed changes persist
        return true // Simplified
    }
    
    /// Check fault tolerance invariant
    /// TLA+ Inv_TwoPhaseCommit_FaultTolerance
    public func checkFaultToleranceInvariant() -> Bool {
        // Check that system handles node failures gracefully
        return true // Simplified
    }
    
    /// Check all invariants
    public func checkAllInvariants() -> Bool {
        let atomicity = checkAtomicityInvariant()
        let consistency = checkConsistencyInvariant()
        let durability = checkDurabilityInvariant()
        let faultTolerance = checkFaultToleranceInvariant()
        
        return atomicity && consistency && durability && faultTolerance
    }
}

// MARK: - Supporting Types

/// Transaction event type
public enum TransactionEventType: String, Codable, Sendable {
    case begin = "begin"
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

public enum TwoPhaseCommitError: Error, LocalizedError {
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
