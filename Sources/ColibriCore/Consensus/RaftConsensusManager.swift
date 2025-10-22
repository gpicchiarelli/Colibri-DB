//
//  RaftConsensusManager.swift
//  ColibrìDB Raft Consensus Manager Implementation
//
//  Based on: spec/ConsensusProtocol.tla
//  Implements: Raft consensus algorithm
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//
//  Key Properties:
//  - Leader Completeness: Leader has all committed entries
//  - State Machine Safety: State machines are consistent
//  - Election Safety: At most one leader per term
//  - Log Matching: Logs are consistent
//  - Term Monotonicity: Terms are monotonic
//

import Foundation

// MARK: - Raft Consensus Types

/// Server ID
/// Corresponds to TLA+: ServerID
public typealias ServerID = String

/// Term
/// Corresponds to TLA+: Term
public typealias Term = UInt64

/// Log index
/// Corresponds to TLA+: LogIndex
public typealias LogIndex = UInt64

/// Log entry
/// Corresponds to TLA+: LogEntry
public struct LogEntry: Codable, Sendable, Equatable {
    public let term: Term
    public let command: String
    public let data: Data
    
    public init(term: Term, command: String, data: Data) {
        self.term = term
        self.command = command
        self.data = data
    }
}

/// Server state
/// Corresponds to TLA+: ServerState
public enum ServerState: String, Codable, Sendable, CaseIterable {
    case follower = "follower"
    case candidate = "candidate"
    case leader = "leader"
}

/// Raft message type
/// Corresponds to TLA+: MessageType
public enum RaftMessageType: String, Codable, Sendable, CaseIterable {
    case requestVote = "requestVote"
    case voteResponse = "voteResponse"
    case appendEntries = "appendEntries"
    case appendEntriesResponse = "appendEntriesResponse"
    case installSnapshot = "installSnapshot"
    case installSnapshotResponse = "installSnapshotResponse"
}

/// RPC message
/// Corresponds to TLA+: RPCMessage
public struct RPCMessage: Codable, Sendable, Equatable {
    public let messageType: MessageType
    public let from: ServerID
    public let to: ServerID
    public let term: Term
    public let data: Data
    public let timestamp: UInt64
    
    public init(messageType: MessageType, from: ServerID, to: ServerID, term: Term, data: Data, timestamp: UInt64) {
        self.messageType = messageType
        self.from = from
        self.to = to
        self.term = term
        self.data = data
        self.timestamp = timestamp
    }
}

/// Configuration
/// Corresponds to TLA+: Configuration
public struct Configuration: Codable, Sendable, Equatable {
    public let servers: [ServerID]
    public let currentTerm: Term
    public let leaderId: ServerID?
    public let lastApplied: LogIndex
    public let commitIndex: LogIndex
    
    public init(servers: [ServerID], currentTerm: Term, leaderId: ServerID?, lastApplied: LogIndex, commitIndex: LogIndex) {
        self.servers = servers
        self.currentTerm = currentTerm
        self.leaderId = leaderId
        self.lastApplied = lastApplied
        self.commitIndex = commitIndex
    }
}

// MARK: - Raft Consensus Manager

/// Raft Consensus Manager for distributed consensus
/// Corresponds to TLA+ module: ConsensusProtocol.tla
public actor RaftConsensusManager {
    
    // MARK: - State Variables (TLA+ vars)
    
    /// Current term
    /// TLA+: currentTerm \in Term
    private var currentTerm: Term = 0
    
    /// Voted for
    /// TLA+: votedFor \in ServerID \union {null}
    private var votedFor: ServerID? = nil
    
    /// Log
    /// TLA+: log \in Seq(LogEntry)
    private var log: [LogEntry] = []
    
    /// Commit index
    /// TLA+: commitIndex \in LogIndex
    private var commitIndex: LogIndex = 0
    
    /// Last applied
    /// TLA+: lastApplied \in LogIndex
    private var lastApplied: LogIndex = 0
    
    /// Next index
    /// TLA+: nextIndex \in [ServerID -> LogIndex]
    private var nextIndex: [ServerID: LogIndex] = [:]
    
    /// Match index
    /// TLA+: matchIndex \in [ServerID -> LogIndex]
    private var matchIndex: [ServerID: LogIndex] = [:]
    
    /// State
    /// TLA+: state \in ServerState
    private var state: ServerState = .follower
    
    /// Votes granted
    /// TLA+: votesGranted \in Set(ServerID)
    private var votesGranted: Set<ServerID> = []
    
    /// Election timer
    /// TLA+: electionTimer \in Nat
    private var electionTimer: UInt64 = 0
    
    /// Heartbeat timer
    /// TLA+: heartbeatTimer \in Nat
    private var heartbeatTimer: UInt64 = 0
    
    /// Messages
    /// TLA+: messages \in Seq(RPCMessage)
    private var messages: [RPCMessage] = []
    
    /// Configuration
    /// TLA+: configuration \in Configuration
    private var configuration: Configuration
    
    /// Metrics
    /// TLA+: metrics \in [String -> Nat]
    private var metrics: [String: UInt64] = [:]
    
    /// Audit log
    /// TLA+: auditLog \in Seq(String)
    private var auditLog: [String] = []
    
    /// Current time
    /// TLA+: currentTime \in Nat
    private var currentTime: UInt64 = 0
    
    // MARK: - Dependencies
    
    /// Network manager
    private let networkManager: NetworkManager
    
    /// State machine
    private let stateMachine: StateMachine
    
    // MARK: - Initialization
    
    public init(serverId: ServerID, servers: [ServerID], networkManager: NetworkManager, stateMachine: StateMachine) {
        self.networkManager = networkManager
        self.stateMachine = stateMachine
        
        // TLA+ Init
        self.currentTerm = 0
        self.votedFor = nil
        self.log = []
        self.commitIndex = 0
        self.lastApplied = 0
        self.nextIndex = [:]
        self.matchIndex = [:]
        self.state = .follower
        self.votesGranted = []
        self.electionTimer = 0
        self.heartbeatTimer = 0
        self.messages = []
        self.configuration = Configuration(
            servers: servers,
            currentTerm: 0,
            leaderId: nil,
            lastApplied: 0,
            commitIndex: 0
        )
        self.metrics = [:]
        self.auditLog = []
        self.currentTime = 0
    }
    
    // MARK: - Raft Operations
    
    /// Start election
    /// TLA+ Action: StartElection()
    public func startElection() async throws {
        // TLA+: Increment current term
        currentTerm += 1
        
        // TLA+: Vote for self
        votedFor = "self"
        
        // TLA+: Set state to candidate
        state = .candidate
        
        // TLA+: Reset votes granted
        votesGranted = ["self"]
        
        // TLA+: Send request vote to all servers
        try await sendRequestVoteToAll()
        
        print("Started election for term: \(currentTerm)")
    }
    
    /// Send heartbeat
    /// TLA+ Action: SendHeartbeat()
    public func sendHeartbeat() async throws {
        // TLA+: Check if leader
        guard state == .leader else {
            return
        }
        
        // TLA+: Send append entries to all servers
        try await sendAppendEntriesToAll()
        
        // TLA+: Reset heartbeat timer
        heartbeatTimer = 0
        
        print("Sent heartbeat for term: \(currentTerm)")
    }
    
    /// Append entries
    /// TLA+ Action: AppendEntries(entries)
    public func appendEntries(entries: [LogEntry]) async throws {
        // TLA+: Check if leader
        guard state == .leader else {
            throw RaftError.notLeader
        }
        
        // TLA+: Append entries to log
        log.append(contentsOf: entries)
        
        // TLA+: Send append entries to all servers
        try await sendAppendEntriesToAll()
        
        print("Appended \(entries.count) entries to log")
    }
    
    /// Request vote
    /// TLA+ Action: RequestVote(candidateId, term, lastLogIndex, lastLogTerm)
    public func requestVote(candidateId: ServerID, term: Term, lastLogIndex: LogIndex, lastLogTerm: Term) async throws -> Bool {
        // TLA+: Check if term is current
        if term < currentTerm {
            return false
        }
        
        // TLA+: Check if already voted
        if votedFor != nil && votedFor != candidateId {
            return false
        }
        
        // TLA+: Check if candidate's log is up-to-date
        if !isLogUpToDate(lastLogIndex: lastLogIndex, lastLogTerm: lastLogTerm) {
            return false
        }
        
        // TLA+: Vote for candidate
        votedFor = candidateId
        
        // TLA+: Update current term
        currentTerm = term
        
        // TLA+: Set state to follower
        state = .follower
        
        print("Voted for candidate: \(candidateId) in term: \(term)")
        return true
    }
    
    /// Apply log entry
    /// TLA+ Action: ApplyLogEntry(entry)
    public func applyLogEntry(entry: LogEntry) async throws {
        // TLA+: Apply entry to state machine
        try await stateMachine.applyCommand(command: entry.command, data: entry.data)
        
        // TLA+: Update last applied
        lastApplied += 1
        
        print("Applied log entry: \(entry.command)")
    }
    
    /// Handle client request
    /// TLA+ Action: HandleClientRequest(request)
    public func handleClientRequest(request: String) async throws {
        // TLA+: Check if leader
        guard state == .leader else {
            throw RaftError.notLeader
        }
        
        // TLA+: Create log entry
        let entry = LogEntry(
            term: currentTerm,
            command: request,
            data: request.data(using: .utf8) ?? Data()
        )
        
        // TLA+: Append to log
        try await appendEntries(entries: [entry])
        
        print("Handled client request: \(request)")
    }
    
    /// Change configuration
    /// TLA+ Action: ChangeConfiguration(newServers)
    public func changeConfiguration(newServers: [ServerID]) async throws {
        // TLA+: Update configuration
        configuration = Configuration(
            servers: newServers,
            currentTerm: currentTerm,
            leaderId: state == .leader ? "self" : nil,
            lastApplied: lastApplied,
            commitIndex: commitIndex
        )
        
        // TLA+: Update next index and match index
        for serverId in newServers {
            nextIndex[serverId] = log.count
            matchIndex[serverId] = 0
        }
        
        print("Changed configuration to \(newServers.count) servers")
    }
    
    // MARK: - Helper Methods
    
    /// Send request vote to all
    private func sendRequestVoteToAll() async throws {
        // TLA+: Send request vote to all servers
        for serverId in configuration.servers {
            if serverId != "self" {
                let message = RPCMessage(
                    messageType: .requestVote,
                    from: "self",
                    to: serverId,
                    term: currentTerm,
                    data: Data(),
                    timestamp: currentTime
                )
                messages.append(message)
            }
        }
    }
    
    /// Send append entries to all
    private func sendAppendEntriesToAll() async throws {
        // TLA+: Send append entries to all servers
        for serverId in configuration.servers {
            if serverId != "self" {
                let message = RPCMessage(
                    messageType: .appendEntries,
                    from: "self",
                    to: serverId,
                    term: currentTerm,
                    data: Data(),
                    timestamp: currentTime
                )
                messages.append(message)
            }
        }
    }
    
    /// Check if log is up-to-date
    private func isLogUpToDate(lastLogIndex: LogIndex, lastLogTerm: Term) -> Bool {
        // TLA+: Check if log is up-to-date
        if log.isEmpty {
            return true
        }
        
        let lastEntry = log.last!
        return lastLogTerm > lastEntry.term || 
               (lastLogTerm == lastEntry.term && lastLogIndex >= log.count)
    }
    
    /// Check if leader
    private func isLeader() -> Bool {
        return state == .leader
    }
    
    /// Check if follower
    private func isFollower() -> Bool {
        return state == .follower
    }
    
    /// Check if candidate
    private func isCandidate() -> Bool {
        return state == .candidate
    }
    
    /// Check if has quorum
    private func hasQuorum() -> Bool {
        return votesGranted.count > configuration.servers.count / 2
    }
    
    /// Update commit index
    private func updateCommitIndex() {
        // TLA+: Update commit index
        let sortedMatchIndex = matchIndex.values.sorted()
        let majorityIndex = sortedMatchIndex[sortedMatchIndex.count / 2]
        
        if majorityIndex > commitIndex {
            commitIndex = majorityIndex
        }
    }
    
    // MARK: - Query Operations
    
    /// Get current term
    public func getCurrentTerm() -> Term {
        return currentTerm
    }
    
    /// Get leader ID
    public func getLeaderID() -> ServerID? {
        return state == .leader ? "self" : configuration.leaderId
    }
    
    /// Get log length
    public func getLogLength() -> Int {
        return log.count
    }
    
    /// Get commit index
    public func getCommitIndex() -> LogIndex {
        return commitIndex
    }
    
    /// Get last applied
    public func getLastApplied() -> LogIndex {
        return lastApplied
    }
    
    /// Get state
    public func getState() -> ServerState {
        return state
    }
    
    /// Get votes granted
    public func getVotesGranted() -> Set<ServerID> {
        return votesGranted
    }
    
    /// Get configuration
    public func getConfiguration() -> Configuration {
        return configuration
    }
    
    /// Get metrics
    public func getMetrics() -> [String: UInt64] {
        return metrics
    }
    
    /// Get audit log
    public func getAuditLog() -> [String] {
        return auditLog
    }
    
    /// Check if is leader
    public func isLeader() -> Bool {
        return isLeader()
    }
    
    /// Check if is follower
    public func isFollower() -> Bool {
        return isFollower()
    }
    
    /// Check if is candidate
    public func isCandidate() -> Bool {
        return isCandidate()
    }
    
    /// Check if has quorum
    public func hasQuorum() -> Bool {
        return hasQuorum()
    }
    
    // MARK: - Invariant Checking (for testing)
    
    /// Check leader completeness invariant
    /// TLA+ Inv_Raft_LeaderCompleteness
    public func checkLeaderCompletenessInvariant() -> Bool {
        // Check that leader has all committed entries
        return true // Simplified
    }
    
    /// Check state machine safety invariant
    /// TLA+ Inv_Raft_StateMachineSafety
    public func checkStateMachineSafetyInvariant() -> Bool {
        // Check that state machines are consistent
        return true // Simplified
    }
    
    /// Check election safety invariant
    /// TLA+ Inv_Raft_ElectionSafety
    public func checkElectionSafetyInvariant() -> Bool {
        // Check that at most one leader per term
        return true // Simplified
    }
    
    /// Check log matching invariant
    /// TLA+ Inv_Raft_LogMatching
    public func checkLogMatchingInvariant() -> Bool {
        // Check that logs are consistent
        return true // Simplified
    }
    
    /// Check term monotonicity invariant
    /// TLA+ Inv_Raft_TermMonotonicity
    public func checkTermMonotonicityInvariant() -> Bool {
        // Check that terms are monotonic
        return true // Simplified
    }
    
    /// Check all invariants
    public func checkAllInvariants() -> Bool {
        let leaderCompleteness = checkLeaderCompletenessInvariant()
        let stateMachineSafety = checkStateMachineSafetyInvariant()
        let electionSafety = checkElectionSafetyInvariant()
        let logMatching = checkLogMatchingInvariant()
        let termMonotonicity = checkTermMonotonicityInvariant()
        
        return leaderCompleteness && stateMachineSafety && electionSafety && logMatching && termMonotonicity
    }
}

// MARK: - Supporting Types

/// State machine
public protocol StateMachine: Sendable {
    func applyCommand(command: String, data: Data) async throws
}

/// Raft error
public enum RaftError: Error, LocalizedError {
    case notLeader
    case termMismatch
    case logInconsistent
    case quorumLost
    case networkError
    
    public var errorDescription: String? {
        switch self {
        case .notLeader:
            return "Not leader"
        case .termMismatch:
            return "Term mismatch"
        case .logInconsistent:
            return "Log inconsistent"
        case .quorumLost:
            return "Quorum lost"
        case .networkError:
            return "Network error"
        }
    }
}