/*
 * TwoPhaseCommit.swift
 * ColibrìDB - Two-Phase Commit Protocol Implementation
 *
 * Based on TLA+ specification: TwoPhaseCommit.tla
 *
 * This module implements the classic two-phase commit protocol for
 * distributed transaction coordination:
 * - Coordinator and participant roles
 * - Prepare and commit phases
 * - Vote collection and decision
 * - Timeout and failure handling
 * - Blocking behavior
 * - Recovery from failures
 * - Atomicity guarantees
 *
 * References:
 * [1] Gray, J. (1978). "Notes on Data Base Operating Systems"
 *     In: Operating Systems: An Advanced Course, Springer-Verlag.
 * [2] Bernstein, P. A., Hadzilacos, V., & Goodman, N. (1987).
 *     "Concurrency Control and Recovery in Database Systems"
 * [3] Lampson, B., & Sturgis, H. (1976).
 *     "Crash Recovery in a Distributed Data Storage System"
 * [4] Skeen, D. (1981). "Nonblocking Commit Protocols"
 *     Proceedings of ACM SIGMOD.
 *
 * Author: ColibrìDB Team
 * Date: 2025-10-19
 */

import Foundation

// MARK: - States

// CoordinatorState is defined in Transaction/TransactionManager.swift

/// Participant states (Gray 1978, Section 3.4.2)
public enum ParticipantState: String, Codable, Sendable {
    case idle           // No active transaction
    case working        // Executing transaction operations
    case prepared       // Voted YES, waiting for decision
    case committed      // Transaction committed
    case aborted        // Transaction aborted
}

// MARK: - Messages

/// Distributed transaction message types (Gray 1978)
public enum MessageType: String, Codable, Sendable {
    case prepare        // Coordinator -> Participant: prepare to commit
    case voteYes        // Participant -> Coordinator: prepared successfully
    case voteNo         // Participant -> Coordinator: cannot commit
    case commit         // Coordinator -> Participant: commit decision
    case abort          // Coordinator -> Participant: abort decision
    case ack            // Participant -> Coordinator: acknowledgment
}

/// Message structure
public struct TwoPhaseMessage: Codable {
    public let type: MessageType
    public let from: String         // Coordinator or participant ID
    public let to: String           // Coordinator or participant ID
    public let transactionId: String
    public let timestamp: Date
    
    public init(type: MessageType, from: String, to: String, transactionId: String) {
        self.type = type
        self.from = from
        self.to = to
        self.transactionId = transactionId
        self.timestamp = Date()
    }
}

// MARK: - Decision

/// Transaction decision
public enum Decision: String, Codable, Sendable {
    case none
    case commit
    case abort
}

/// Vote from participant
public enum Vote: String, Codable {
    case none
    case yes
    case no
}

// MARK: - Coordinator

/// Two-phase commit coordinator
public actor TwoPhaseCoordinator {
    
    public let coordinatorId: String
    private var participantIds: Set<String>
    
    // State per transaction
    private var states: [String: CoordinatorState] = [:]
    private var votes: [String: Set<ParticipantVote>] = [:]
    private var decisions: [String: Decision] = [:]
    private var timeouts: [String: Int] = [:]
    
    // Persistent log (survives crashes)
    private var log: [String: [String]] = [:]
    
    // Network
    private var outgoingMessages: [TwoPhaseMessage] = []
    
    // Failure state
    private var isFailed: Bool = false
    
    // Configuration
    private let maxTimeout: Int
    
    public init(coordinatorId: String, participantIds: Set<String>, maxTimeout: Int = 30) {
        self.coordinatorId = coordinatorId
        self.participantIds = participantIds
        self.maxTimeout = maxTimeout
    }
    
    // MARK: - Public API
    
    /// Start a new transaction
    public func startTransaction(transactionId: String) throws {
        guard !isFailed else {
            throw TwoPhaseError.coordinatorFailed
        }
        
        guard states[transactionId] == nil || states[transactionId] == .idle else {
            throw TwoPhaseError.transactionAlreadyActive
        }
        
        // Update state
        states[transactionId] = .preparing
        votes[transactionId] = []
        decisions[transactionId] = Decision.none
        timeouts[transactionId] = maxTimeout
        
        // Log start
        appendLog(transactionId: transactionId, entry: "START")
        
        // Broadcast PREPARE to all participants
        for participantId in participantIds {
            let msg = TwoPhaseMessage(type: .prepare, from: coordinatorId,
                                    to: participantId, transactionId: transactionId)
            outgoingMessages.append(msg)
        }
    }
    
    /// Collect vote from participant
    public func collectVote(message: TwoPhaseMessage) throws {
        guard !isFailed else {
            throw TwoPhaseError.coordinatorFailed
        }
        
        let txnId = message.transactionId
        
        guard states[txnId] == .preparing else {
            throw TwoPhaseError.invalidState(current: states[txnId] ?? .idle, expected: .preparing)
        }
        
        guard message.type == .voteYes || message.type == .voteNo else {
            throw TwoPhaseError.invalidMessageType
        }
        
        let vote = message.type == .voteYes ? Vote.yes : Vote.no
        let participantVote = ParticipantVote(participantId: message.from, vote: vote)
        
        votes[txnId, default: []].insert(participantVote)
        
        // Check if all votes received
        if allVotesReceived(transactionId: txnId) {
            try makeDecision(transactionId: txnId)
        }
    }
    
    /// Make commit/abort decision
    private func makeDecision(transactionId: String) throws {
        guard states[transactionId] == .preparing else {
            throw TwoPhaseError.invalidState(current: states[transactionId] ?? .idle, expected: .preparing)
        }
        
        guard allVotesReceived(transactionId: transactionId) else {
            throw TwoPhaseError.notAllVotesReceived
        }
        
        // Decision: COMMIT if all YES, else ABORT
        let decision: Decision = allVotesYes(transactionId: transactionId) ? .commit : .abort
        let newState: CoordinatorState = decision == .commit ? .committing : .aborting
        let msgType: MessageType = decision == .commit ? .commit : .abort
        
        // Update state and log decision (force to disk!)
        decisions[transactionId] = decision
        states[transactionId] = newState
        appendLog(transactionId: transactionId, entry: decision.rawValue.uppercased())
        
        // Broadcast decision to all participants
        for participantId in participantIds {
            let msg = TwoPhaseMessage(type: msgType, from: coordinatorId,
                                    to: participantId, transactionId: transactionId)
            outgoingMessages.append(msg)
        }
    }
    
    /// Receive acknowledgment from participant
    public func receiveAck(message: TwoPhaseMessage) throws {
        guard !isFailed else {
            throw TwoPhaseError.coordinatorFailed
        }
        
        let txnId = message.transactionId
        
        guard states[txnId] == .committing || states[txnId] == .aborting else {
            throw TwoPhaseError.invalidState(current: states[txnId] ?? .idle, expected: .committing)
        }
        
        guard message.type == .ack else {
            throw TwoPhaseError.invalidMessageType
        }
        
        // Could track which participants acknowledged
        // For simplicity, we just proceed
    }
    
    /// Finish transaction (all acks received)
    public func finishTransaction(transactionId: String) throws {
        guard !isFailed else {
            throw TwoPhaseError.coordinatorFailed
        }
        
        guard states[transactionId] == .committing || states[transactionId] == .aborting else {
            throw TwoPhaseError.invalidState(current: states[transactionId] ?? .idle, expected: .committing)
        }
        
        let finalState: CoordinatorState = states[transactionId] == .committing ? .committed : .aborted
        states[transactionId] = finalState
        appendLog(transactionId: transactionId, entry: "COMPLETE")
    }
    
    /// Handle timeout
    public func handleTimeout(transactionId: String) throws {
        guard !isFailed else {
            throw TwoPhaseError.coordinatorFailed
        }
        
        guard states[transactionId] == .preparing else {
            return // Timeout only relevant in preparing phase
        }
        
        guard let timeout = timeouts[transactionId], timeout == 0 else {
            return
        }
        
        guard decisions[transactionId] == Decision.none else {
            return // Decision already made
        }
        
        // Timeout: abort transaction
        decisions[transactionId] = .abort
        states[transactionId] = .aborting
        appendLog(transactionId: transactionId, entry: "ABORT")
        
        // Broadcast ABORT to all participants
        for participantId in participantIds {
            let msg = TwoPhaseMessage(type: .abort, from: coordinatorId,
                                    to: participantId, transactionId: transactionId)
            outgoingMessages.append(msg)
        }
    }
    
    /// Decrement timeout
    public func decrementTimeout(transactionId: String) {
        if let timeout = timeouts[transactionId], timeout > 0 {
            timeouts[transactionId] = timeout - 1
        }
    }
    
    /// Fail coordinator
    public func fail() {
        isFailed = true
    }
    
    /// Recover coordinator
    public func recover(transactionId: String) throws {
        isFailed = false
        
        guard let logEntries = log[transactionId], !logEntries.isEmpty else {
            // No log entry: transaction not started
            return
        }
        
        // Determine state from log
        if logEntries.contains("COMMIT") || logEntries.contains("ABORT") {
            // Decision was made: resend decision
            let decision = logEntries.contains("COMMIT") ? Decision.commit : Decision.abort
            let msgType: MessageType = decision == .commit ? .commit : .abort
            
            for participantId in participantIds {
                let msg = TwoPhaseMessage(type: msgType, from: coordinatorId,
                                        to: participantId, transactionId: transactionId)
                outgoingMessages.append(msg)
            }
        } else {
            // No decision yet: abort
            decisions[transactionId] = .abort
            states[transactionId] = .aborting
            appendLog(transactionId: transactionId, entry: "ABORT")
            
            for participantId in participantIds {
                let msg = TwoPhaseMessage(type: .abort, from: coordinatorId,
                                        to: participantId, transactionId: transactionId)
                outgoingMessages.append(msg)
            }
        }
    }
    
    // MARK: - Query Methods
    
    public func getState(transactionId: String) -> CoordinatorState? {
        return states[transactionId]
    }
    
    public func getDecision(transactionId: String) -> Decision? {
        return decisions[transactionId]
    }
    
    public func getOutgoingMessages() -> [TwoPhaseMessage] {
        return outgoingMessages
    }
    
    public func clearOutgoingMessages() {
        outgoingMessages.removeAll()
    }
    
    // MARK: - Helper Methods
    
    private func allVotesReceived(transactionId: String) -> Bool {
        guard let receivedVotes = votes[transactionId] else { return false }
        let votedParticipants = Set(receivedVotes.map { $0.participantId })
        return votedParticipants == participantIds
    }
    
    private func allVotesYes(transactionId: String) -> Bool {
        guard let receivedVotes = votes[transactionId] else { return false }
        return receivedVotes.allSatisfy { $0.vote == .yes }
    }
    
    private func appendLog(transactionId: String, entry: String) {
        log[transactionId, default: []].append(entry)
    }
}

// MARK: - Participant

/// Two-phase commit participant
public actor TwoPhaseParticipant {
    
    public let participantId: String
    
    // State per transaction
    private var states: [String: ParticipantState] = [:]
    private var votesCast: [String: Vote] = [:]
    private var timeouts: [String: Int] = [:]
    
    // Persistent log
    private var log: [String: [String]] = [:]
    
    // Network
    private var outgoingMessages: [TwoPhaseMessage] = []
    
    // Failure state
    private var isFailed: Bool = false
    
    // Configuration
    private let maxTimeout: Int
    
    // Callback to determine if can prepare
    private let canPrepareCallback: (String) async -> Bool
    
    public init(participantId: String, maxTimeout: Int = 30,
                canPrepareCallback: @escaping (String) async -> Bool = { _ in true }) {
        self.participantId = participantId
        self.maxTimeout = maxTimeout
        self.canPrepareCallback = canPrepareCallback
    }
    
    // MARK: - Public API
    
    /// Receive PREPARE and vote
    public func receivePrepare(message: TwoPhaseMessage, coordinatorId: String) async throws {
        guard !isFailed else {
            throw TwoPhaseError.participantFailed
        }
        
        guard message.type == .prepare else {
            throw TwoPhaseError.invalidMessageType
        }
        
        let txnId = message.transactionId
        
        guard states[txnId] == nil || states[txnId] == .idle || states[txnId] == .working else {
            throw TwoPhaseError.invalidParticipantState(current: states[txnId] ?? .idle, expected: .idle)
        }
        
        // Determine vote
        let canPrepare = await canPrepareCallback(txnId)
        let vote: Vote = canPrepare ? .yes : .no
        
        if vote == .yes {
            // Vote YES: write PREPARED to log (force to disk!)
            states[txnId] = .prepared
            votesCast[txnId] = .yes
            timeouts[txnId] = maxTimeout
            appendLog(transactionId: txnId, entry: "PREPARED")
            
            // Send VOTE_YES to coordinator
            let msg = TwoPhaseMessage(type: .voteYes, from: participantId,
                                    to: coordinatorId, transactionId: txnId)
            outgoingMessages.append(msg)
        } else {
            // Vote NO: abort locally
            states[txnId] = .aborted
            votesCast[txnId] = .no
            appendLog(transactionId: txnId, entry: "ABORTED")
            
            // Send VOTE_NO to coordinator
            let msg = TwoPhaseMessage(type: .voteNo, from: participantId,
                                    to: coordinatorId, transactionId: txnId)
            outgoingMessages.append(msg)
        }
    }
    
    /// Execute decision from coordinator
    public func executeDecision(message: TwoPhaseMessage, coordinatorId: String) throws {
        guard !isFailed else {
            throw TwoPhaseError.participantFailed
        }
        
        guard message.type == .commit || message.type == .abort else {
            throw TwoPhaseError.invalidMessageType
        }
        
        let txnId = message.transactionId
        
        guard states[txnId] == .prepared || states[txnId] == .working else {
            throw TwoPhaseError.invalidParticipantState(current: states[txnId] ?? .idle, expected: .prepared)
        }
        
        let decision = message.type == .commit ? Decision.commit : Decision.abort
        let newState: ParticipantState = decision == .commit ? .committed : .aborted
        
        // Update state and log
        states[txnId] = newState
        appendLog(transactionId: txnId, entry: decision.rawValue.uppercased())
        
        // Send acknowledgment
        let ackMsg = TwoPhaseMessage(type: .ack, from: participantId,
                                    to: coordinatorId, transactionId: txnId)
        outgoingMessages.append(ackMsg)
    }
    
    /// Handle timeout (blocking!)
    public func handleTimeout(transactionId: String) {
        // Participant is blocked if in PREPARED state and timeout occurs
        // Cannot make unilateral decision - must wait for coordinator
        // In practice, would contact other participants or wait for recovery
        guard states[transactionId] == .prepared else {
            return
        }
        
        guard let timeout = timeouts[transactionId], timeout == 0 else {
            return
        }
        
        // Blocked! This is the fundamental limitation of 2PC
        // Would need 3PC or coordinator recovery to resolve
    }
    
    /// Decrement timeout
    public func decrementTimeout(transactionId: String) {
        if let timeout = timeouts[transactionId], timeout > 0 {
            timeouts[transactionId] = timeout - 1
        }
    }
    
    /// Fail participant
    public func fail() {
        isFailed = true
    }
    
    /// Recover participant
    public func recover() {
        isFailed = false
        // Read log and resume from last known state
    }
    
    // MARK: - Query Methods
    
    public func getState(transactionId: String) -> ParticipantState? {
        return states[transactionId]
    }
    
    public func getVote(transactionId: String) -> Vote? {
        return votesCast[transactionId]
    }
    
    public func getOutgoingMessages() -> [TwoPhaseMessage] {
        return outgoingMessages
    }
    
    public func clearOutgoingMessages() {
        outgoingMessages.removeAll()
    }
    
    // MARK: - Helper Methods
    
    private func appendLog(transactionId: String, entry: String) {
        log[transactionId, default: []].append(entry)
    }
}

// MARK: - Supporting Types

/// Participant vote
public struct ParticipantVote: Hashable, Codable {
    public let participantId: String
    public let vote: Vote
    
    public init(participantId: String, vote: Vote) {
        self.participantId = participantId
        self.vote = vote
    }
}

// MARK: - Errors

public enum TwoPhaseError: Error, LocalizedError {
    case coordinatorFailed
    case participantFailed
    case transactionAlreadyActive
    case invalidState(current: CoordinatorState, expected: CoordinatorState)
    case invalidParticipantState(current: ParticipantState, expected: ParticipantState)
    case invalidMessageType
    case notAllVotesReceived
    case timeout
    
    public var errorDescription: String? {
        switch self {
        case .coordinatorFailed:
            return "Coordinator has failed"
        case .participantFailed:
            return "Participant has failed"
        case .transactionAlreadyActive:
            return "Transaction is already active"
        case .invalidState(let current, let expected):
            return "Invalid state: current=\(current), expected=\(expected)"
        case .invalidParticipantState(let current, let expected):
            return "Invalid participant state: current=\(current), expected=\(expected)"
        case .invalidMessageType:
            return "Invalid message type"
        case .notAllVotesReceived:
            return "Not all votes have been received"
        case .timeout:
            return "Transaction timeout"
        }
    }
}

// MARK: - Network Simulator

/// Simple network simulator for testing
public actor TwoPhaseNetwork {
    
    private var messages: [TwoPhaseMessage] = []
    
    public init() {}
    
    public func send(message: TwoPhaseMessage) {
        messages.append(message)
    }
    
    public func receive(for recipient: String) -> [TwoPhaseMessage] {
        let received = messages.filter { $0.to == recipient }
        messages.removeAll { $0.to == recipient }
        return received
    }
    
    public func getAllMessages() -> [TwoPhaseMessage] {
        return messages
    }
    
    public func clear() {
        messages.removeAll()
    }
}

/*
 * IMPLEMENTATION NOTES:
 *
 * This implementation follows the TwoPhaseCommit.tla specification:
 *
 * 1. Two Phases:
 *    - Phase 1 (Prepare): Coordinator asks participants to prepare
 *    - Phase 2 (Commit/Abort): Coordinator sends decision
 *
 * 2. Roles:
 *    - Coordinator: Manages protocol, collects votes, makes decision
 *    - Participants: Execute transaction, vote, execute decision
 *
 * 3. States:
 *    - Coordinator: IDLE -> PREPARING -> COMMITTING/ABORTING -> COMMITTED/ABORTED
 *    - Participant: IDLE -> WORKING -> PREPARED -> COMMITTED/ABORTED
 *
 * 4. Messages:
 *    - PREPARE: Coordinator -> Participant
 *    - VOTE_YES/VOTE_NO: Participant -> Coordinator
 *    - COMMIT/ABORT: Coordinator -> Participant
 *    - ACK: Participant -> Coordinator
 *
 * 5. Persistent Log:
 *    - Coordinator logs: START, COMMIT/ABORT, COMPLETE
 *    - Participant logs: PREPARED, COMMITTED/ABORTED
 *    - Logs survive crashes for recovery
 *
 * 6. Safety Properties (verified by TLA+):
 *    - Atomicity: All participants reach same outcome
 *    - Consistency: Coordinator and participants agree
 *    - Validity: If all vote YES and no failures, transaction commits
 *    - No unilateral commit: Participants don't commit without coordinator decision
 *
 * 7. Limitations:
 *    - BLOCKING: If coordinator fails after participants prepare, system blocks
 *    - This is fundamental to 2PC (proven in literature)
 *    - Solution: Use 3PC or consensus protocols (Paxos, Raft)
 *
 * Academic References:
 * - Gray (1978): Original 2PC specification
 * - Bernstein et al. (1987): Formal analysis and correctness proofs
 * - Lampson & Sturgis (1976): Early distributed commit protocol
 * - Skeen (1981): Non-blocking alternatives (3PC)
 */

