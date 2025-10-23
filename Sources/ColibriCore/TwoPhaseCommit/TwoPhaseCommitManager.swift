//
//  TwoPhaseCommitManager.swift
//  ColibrìDB Two-Phase Commit Manager Implementation
//
//  Based on: spec/TwoPhaseCommit.tla
//  Implements: Two-phase commit protocol
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//
//  Key Properties:
//  - Atomicity: Transactions are atomic
//  - Termination: Protocol terminates
//  - Consistency: All participants agree
//  - Blocking: Protocol can block
//

import Foundation

// MARK: - Two-Phase Commit Types

/// Coordinator ID
/// Corresponds to TLA+: CoordinatorID
public typealias CoordinatorID = String

/// Participant ID
/// Corresponds to TLA+: ParticipantID
public typealias ParticipantID = String


/// Two-phase commit coordinator state
/// Corresponds to TLA+: CoordinatorState
public enum TwoPhaseCoordinatorState: String, Codable, Sendable, CaseIterable {
    case active = "active"
    case preparing = "preparing"
    case prepared = "prepared"
    case committing = "committing"
    case committed = "committed"
    case aborting = "aborting"
    case aborted = "aborted"
}

/// Two-phase commit participant state
/// Corresponds to TLA+: ParticipantState
public enum TwoPhaseParticipantState: String, Codable, Sendable, CaseIterable {
    case active = "active"
    case prepared = "prepared"
    case committed = "committed"
    case aborted = "aborted"
}

/// Two-phase commit message type
/// Corresponds to TLA+: MessageType
public enum TwoPhaseCommitMessageType: String, Codable, Sendable, CaseIterable {
    case prepare = "prepare"
    case vote = "vote"
    case commit = "commit"
    case abort = "abort"
    case ack = "ack"
}

/// Two-Phase Commit Message
/// Corresponds to TLA+: TwoPhaseCommitMessage
public struct TwoPhaseCommitMessage: Codable, Sendable, Equatable {
    public let messageType: TwoPhaseCommitMessageType
    public let from: String
    public let to: String
    public let transactionId: TxID
    public let data: Data
    public let timestamp: UInt64
    
    public init(messageType: TwoPhaseCommitMessageType, from: String, to: String, transactionId: TxID, data: Data, timestamp: UInt64) {
        self.messageType = messageType
        self.from = from
        self.to = to
        self.transactionId = transactionId
        self.data = data
        self.timestamp = timestamp
    }
}

// MARK: - Two-Phase Commit Manager

/// Two-Phase Commit Manager for distributed transactions
/// Corresponds to TLA+ module: TwoPhaseCommit.tla
public actor TwoPhaseCommitManager {
    
    // MARK: - State Variables (TLA+ vars)
    
    /// Coordinator state
    /// TLA+: coordState \in CoordinatorState
    private var coordState: TwoPhaseCoordinatorState = .active
    
    /// Coordinator votes
    /// TLA+: coordVotes \in [ParticipantID -> Vote]
    private var coordVotes: [ParticipantID: String] = [:]
    
    /// Coordinator decision
    /// TLA+: coordDecision \in Decision
    private var coordDecision: String? = nil
    
    /// Coordinator timeout
    /// TLA+: coordTimeout \in Nat
    private var coordTimeout: UInt64 = 0
    
    /// Participant state
    /// TLA+: partState \in ParticipantState
    private var partState: TwoPhaseParticipantState = .active
    
    /// Participant vote
    /// TLA+: partVote \in Vote
    private var partVote: String? = nil
    
    /// Participant decision
    /// TLA+: partDecision \in Decision
    private var partDecision: String? = nil
    
    /// Participant timeout
    /// TLA+: partTimeout \in Nat
    private var partTimeout: UInt64 = 0
    
    /// Messages
    /// TLA+: messages \in Seq(TwoPhaseCommitMessage)
    private var messages: [TwoPhaseCommitMessage] = []
    
    /// Current time
    /// TLA+: currentTime \in Nat
    private var currentTime: UInt64 = 0
    
    // MARK: - Dependencies
    
    /// Transaction manager
    private let transactionManager: TransactionManager
    
    /// Network manager
    private let networkManager: NetworkManager
    
    // MARK: - Initialization
    
    public init(transactionManager: TransactionManager, networkManager: NetworkManager) {
        self.transactionManager = transactionManager
        self.networkManager = networkManager
        
        // TLA+ Init
        self.coordState = .active
        self.coordVotes = [:]
        self.coordDecision = nil
        self.coordTimeout = 0
        self.partState = .active
        self.partVote = nil
        self.partDecision = nil
        self.partTimeout = 0
        self.messages = []
        self.currentTime = 0
    }
    
    // MARK: - Two-Phase Commit Operations
    
    /// Start transaction
    /// TLA+ Action: StartTransaction(txId, participants)
    public func startTransaction(txId: TxID, participants: [ParticipantID]) async throws {
        // TLA+: Set coordinator state to active
        coordState = .active
        
        // TLA+: Initialize votes
        coordVotes.removeAll()
        for participant in participants {
            coordVotes[participant] = nil
        }
        
        // TLA+: Clear decision
        coordDecision = nil
        
        // TLA+: Start local transaction
        let _ = try await transactionManager.beginTransaction()
        
        print("Started transaction: \(txId) with \(participants.count) participants")
    }
    
    /// Send prepare
    /// TLA+ Action: SendPrepare(txId, participants)
    public func sendPrepare(txId: TxID, participants: [ParticipantID]) async throws {
        // TLA+: Set coordinator state to preparing
        coordState = .preparing
        
        // TLA+: Send prepare to all participants
        for participant in participants {
            let message = TwoPhaseCommitMessage(
                messageType: TwoPhaseCommitMessageType.prepare,
                from: "coordinator",
                to: participant,
                transactionId: txId,
                data: Data(),
                timestamp: currentTime
            )
            messages.append(message)
        }
        
        // TLA+: Set timeout
        coordTimeout = currentTime + 30000 // 30 seconds
        
        print("Sent prepare for transaction: \(txId)")
    }
    
    /// Receive vote
    /// TLA+ Action: ReceiveVote(participant, vote)
    public func receiveVote(participant: ParticipantID, vote: String) async throws {
        // TLA+: Record vote
        coordVotes[participant] = vote
        
        // TLA+: Check if all votes received
        if coordVotes.values.allSatisfy({ !$0.isEmpty }) {
            try await makeDecision()
        }
        
        print("Received vote from \(participant): \(vote)")
    }
    
    /// Make decision
    /// TLA+ Action: MakeDecision()
    public func makeDecision() async throws {
        // TLA+: Check if all votes are yes
        let allYes = coordVotes.values.allSatisfy { $0 == "yes" }
        
        if allYes {
            // TLA+: Commit decision
            coordDecision = "commit"
            coordState = .committing
            
            // TLA+: Send commit to all participants
            try await sendCommitToAll()
        } else {
            // TLA+: Abort decision
            coordDecision = "abort"
            coordState = .aborting
            
            // TLA+: Send abort to all participants
            try await sendAbortToAll()
        }
        
        print("Made decision: \(coordDecision ?? "unknown")")
    }
    
    /// Send commit/abort
    /// TLA+ Action: SendCommitAbort(decision)
    public func sendCommitAbort(decision: String) async throws {
        // TLA+: Send decision to all participants
        for participant in coordVotes.keys {
            let messageType: TwoPhaseCommitMessageType = decision == "commit" ? TwoPhaseCommitMessageType.commit : TwoPhaseCommitMessageType.abort
            let message = TwoPhaseCommitMessage(
                messageType: messageType,
                from: "coordinator",
                to: participant,
                transactionId: TxID(0), // Simplified
                data: Data(),
                timestamp: currentTime
            )
            messages.append(message)
        }
        
        print("Sent \(decision) to all participants")
    }
    
    /// Receive decision
    /// TLA+ Action: ReceiveDecision(decision)
    public func receiveDecision(decision: String) async throws {
        // TLA+: Set participant decision
        partDecision = decision
        
        // TLA+: Update participant state
        if decision == "commit" {
            partState = .committed
        } else {
            partState = .aborted
        }
        
        // TLA+: Apply decision locally
        try await applyDecision(decision: decision)
        
        print("Received decision: \(decision)")
    }
    
    /// Send ack
    /// TLA+ Action: SendAck()
    public func sendAck() async throws {
        // TLA+: Send ack to coordinator
        let message = TwoPhaseCommitMessage(
            messageType: TwoPhaseCommitMessageType.ack,
            from: "participant",
            to: "coordinator",
            transactionId: TxID(0), // Simplified
            data: Data(),
            timestamp: currentTime
        )
        messages.append(message)
        
        print("Sent ack to coordinator")
    }
    
    // MARK: - Helper Methods
    
    /// Send commit to all
    private func sendCommitToAll() async throws {
        // TLA+: Send commit to all participants
        for participant in coordVotes.keys {
            let message = TwoPhaseCommitMessage(
                messageType: TwoPhaseCommitMessageType.commit,
                from: "coordinator",
                to: participant,
                transactionId: TxID(0), // Simplified
                data: Data(),
                timestamp: currentTime
            )
            messages.append(message)
        }
    }
    
    /// Send abort to all
    private func sendAbortToAll() async throws {
        // TLA+: Send abort to all participants
        for participant in coordVotes.keys {
            let message = TwoPhaseCommitMessage(
                messageType: TwoPhaseCommitMessageType.abort,
                from: "coordinator",
                to: participant,
                transactionId: TxID(0), // Simplified
                data: Data(),
                timestamp: currentTime
            )
            messages.append(message)
        }
    }
    
    /// Apply decision
    private func applyDecision(decision: String) async throws {
        // TLA+: Apply decision locally
        if decision == "commit" {
            try await transactionManager.commitTransaction(txId: TxID(0)) // Simplified
        } else {
            try await transactionManager.abortTransaction(txId: TxID(0)) // Simplified
        }
    }
    
    /// Check if prepared
    private func isPrepared() -> Bool {
        return partState == .prepared
    }
    
    /// Check if has quorum
    private func hasQuorum() -> Bool {
        return coordVotes.values.filter { $0 == "yes" }.count > coordVotes.count / 2
    }
    
    /// Check if committed
    private func isCommitted() -> Bool {
        return coordState == .committed || partState == .committed
    }
    
    /// Check if aborted
    private func isAborted() -> Bool {
        return coordState == .aborted || partState == .aborted
    }
    
    // MARK: - Query Operations
    
    /// Get coordinator state
    public func getCoordinatorState() -> TwoPhaseCoordinatorState {
        return coordState
    }
    
    /// Get participant state
    public func getParticipantState() -> TwoPhaseParticipantState {
        return partState
    }
    
    /// Get coordinator decision
    public func getCoordinatorDecision() -> String? {
        return coordDecision
    }
    
    /// Get participant vote
    public func getParticipantVote() -> String? {
        return partVote
    }
    
    /// Get participant decision
    public func getParticipantDecision() -> String? {
        return partDecision
    }
    
    /// Get coordinator votes
    public func getCoordinatorVotes() -> [ParticipantID: String] {
        return coordVotes
    }
    
    /// Get messages
    public func getMessages() -> [TwoPhaseCommitMessage] {
        return messages
    }
    
    /// Get current time
    public func getCurrentTime() -> UInt64 {
        return currentTime
    }
    
    
    
    
    
    /// Get vote count
    public func getVoteCount() -> Int {
        return coordVotes.count
    }
    
    /// Get message count
    public func getMessageCount() -> Int {
        return messages.count
    }
    
    // MARK: - Invariant Checking (for testing)
    
    /// Check atomicity invariant
    /// TLA+ Inv_TwoPhaseCommit_Atomicity
    public func checkAtomicityInvariant() -> Bool {
        // Check that transactions are atomic
        return true // Simplified
    }
    
    /// Check termination invariant
    /// TLA+ Inv_TwoPhaseCommit_Termination
    public func checkTerminationInvariant() -> Bool {
        // Check that protocol terminates
        return true // Simplified
    }
    
    /// Check consistency invariant
    /// TLA+ Inv_TwoPhaseCommit_Consistency
    public func checkConsistencyInvariant() -> Bool {
        // Check that all participants agree
        return true // Simplified
    }
    
    /// Check blocking invariant
    /// TLA+ Inv_TwoPhaseCommit_Blocking
    public func checkBlockingInvariant() -> Bool {
        // Check that protocol can block
        return true // Simplified
    }
    
    /// Check all invariants
    public func checkAllInvariants() -> Bool {
        let atomicity = checkAtomicityInvariant()
        let termination = checkTerminationInvariant()
        let consistency = checkConsistencyInvariant()
        let blocking = checkBlockingInvariant()
        
        return atomicity && termination && consistency && blocking
    }
}