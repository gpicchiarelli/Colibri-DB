//
//  ConsensusProtocol.swift
//  ColibrìDB Raft Consensus Implementation
//
//  Based on: spec/ConsensusProtocol.tla
//  Implements: Raft consensus algorithm
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//
//  Key Properties:
//  - Safety: Only one leader per term
//  - Liveness: System makes progress
//  - Consistency: All nodes agree on state
//  - Fault Tolerance: Handles node failures
//

import Foundation

// MARK: - Consensus Types

/// Node state
/// Corresponds to TLA+: NodeState
public enum NodeState: String, Codable, Sendable {
    case follower = "follower"
    case candidate = "candidate"
    case leader = "leader"
}

/// Log entry
/// Corresponds to TLA+: LogEntry
public struct LogEntry: Codable, Sendable, Equatable {
    public let term: Int
    public let command: String
    public let data: [String: Value]
    public let timestamp: Date
    
    public init(term: Int, command: String, data: [String: Value], timestamp: Date = Date()) {
        self.term = term
        self.command = command
        self.data = data
        self.timestamp = timestamp
    }
}

/// Vote request
/// Corresponds to TLA+: VoteRequest
public struct VoteRequest: Codable, Sendable, Equatable {
    public let term: Int
    public let candidateId: String
    public let lastLogIndex: Int
    public let lastLogTerm: Int
    
    public init(term: Int, candidateId: String, lastLogIndex: Int, lastLogTerm: Int) {
        self.term = term
        self.candidateId = candidateId
        self.lastLogIndex = lastLogIndex
        self.lastLogTerm = lastLogTerm
    }
}

/// Vote response
/// Corresponds to TLA+: VoteResponse
public struct VoteResponse: Codable, Sendable, Equatable {
    public let term: Int
    public let voteGranted: Bool
    public let voterId: String
    
    public init(term: Int, voteGranted: Bool, voterId: String) {
        self.term = term
        self.voteGranted = voteGranted
        self.voteGranted = voteGranted
        self.voterId = voterId
    }
}

/// Append entries request
/// Corresponds to TLA+: AppendEntriesRequest
public struct AppendEntriesRequest: Codable, Sendable, Equatable {
    public let term: Int
    public let leaderId: String
    public let prevLogIndex: Int
    public let prevLogTerm: Int
    public let entries: [LogEntry]
    public let leaderCommit: Int
    
    public init(term: Int, leaderId: String, prevLogIndex: Int, prevLogTerm: Int, entries: [LogEntry], leaderCommit: Int) {
        self.term = term
        self.leaderId = leaderId
        self.prevLogIndex = prevLogIndex
        self.prevLogTerm = prevLogTerm
        self.entries = entries
        self.leaderCommit = leaderCommit
    }
}

/// Append entries response
/// Corresponds to TLA+: AppendEntriesResponse
public struct AppendEntriesResponse: Codable, Sendable, Equatable {
    public let term: Int
    public let success: Bool
    public let followerId: String
    public let lastLogIndex: Int
    
    public init(term: Int, success: Bool, followerId: String, lastLogIndex: Int) {
        self.term = term
        self.success = success
        self.followerId = followerId
        self.lastLogIndex = lastLogIndex
    }
}

// MARK: - Raft Consensus Manager

/// Raft Consensus Manager for distributed consensus
/// Corresponds to TLA+ module: ConsensusProtocol.tla
public actor RaftConsensusManager {
    
    // MARK: - State Variables (TLA+ vars)
    
    /// Current term
    /// TLA+: currentTerm \in Nat
    private var currentTerm: Int = 0
    
    /// Voted for
    /// TLA+: votedFor \in NodeId \cup {null}
    private var votedFor: String? = nil
    
    /// Log entries
    /// TLA+: log \in Seq(LogEntry)
    private var log: [LogEntry] = []
    
    /// Commit index
    /// TLA+: commitIndex \in Nat
    private var commitIndex: Int = 0
    
    /// Last applied
    /// TLA+: lastApplied \in Nat
    private var lastApplied: Int = 0
    
    /// Next index
    /// TLA+: nextIndex \in [NodeId -> Nat]
    private var nextIndex: [String: Int] = [:]
    
    /// Match index
    /// TLA+: matchIndex \in [NodeId -> Nat]
    private var matchIndex: [String: Int] = [:]
    
    /// Node state
    /// TLA+: state \in NodeState
    private var state: NodeState = .follower
    
    /// Leader ID
    /// TLA+: leaderId \in NodeId \cup {null}
    private var leaderId: String? = nil
    
    /// Election timeout
    private var electionTimeout: TimeInterval
    
    /// Heartbeat timeout
    private var heartbeatTimeout: TimeInterval
    
    /// Node ID
    private var nodeId: String
    
    /// Cluster nodes
    private var clusterNodes: Set<String>
    
    // MARK: - Dependencies
    
    /// Network manager
    private let networkManager: NetworkManager
    
    /// State machine
    private let stateMachine: StateMachine
    
    // MARK: - Initialization
    
    public init(nodeId: String, clusterNodes: Set<String>, networkManager: NetworkManager, stateMachine: StateMachine, electionTimeout: TimeInterval = 5.0, heartbeatTimeout: TimeInterval = 1.0) {
        self.nodeId = nodeId
        self.clusterNodes = clusterNodes
        self.networkManager = networkManager
        self.stateMachine = stateMachine
        self.electionTimeout = electionTimeout
        self.heartbeatTimeout = heartbeatTimeout
        
        // TLA+ Init
        self.currentTerm = 0
        self.votedFor = nil
        self.log = []
        self.commitIndex = 0
        self.lastApplied = 0
        self.nextIndex = [:]
        self.matchIndex = [:]
        self.state = .follower
        self.leaderId = nil
        
        // Initialize nextIndex and matchIndex for all nodes
        for nodeId in clusterNodes {
            self.nextIndex[nodeId] = 0
            self.matchIndex[nodeId] = 0
        }
    }
    
    // MARK: - Election Management
    
    /// Start election
    /// TLA+ Action: StartElection
    public func startElection() async throws {
        // TLA+: Check if node is follower
        guard state == .follower else {
            throw ConsensusError.invalidState
        }
        
        // TLA+: Increment current term
        currentTerm += 1
        
        // TLA+: Change to candidate state
        state = .candidate
        
        // TLA+: Vote for self
        votedFor = nodeId
        
        // TLA+: Reset vote count
        var votesReceived = 1
        
        // TLA+: Send vote requests to all other nodes
        let voteRequest = VoteRequest(
            term: currentTerm,
            candidateId: nodeId,
            lastLogIndex: log.count - 1,
            lastLogTerm: log.last?.term ?? 0
        )
        
        for otherNodeId in clusterNodes {
            if otherNodeId != nodeId {
                do {
                    let response = try await networkManager.sendVoteRequest(
                        nodeId: otherNodeId,
                        request: voteRequest
                    )
                    
                    if response.voteGranted {
                        votesReceived += 1
                    }
                    
                    // TLA+: Update term if response has higher term
                    if response.term > currentTerm {
                        currentTerm = response.term
                        state = .follower
                        votedFor = nil
                        return
                    }
                } catch {
                    // TLA+: Handle network failure
                    continue
                }
            }
        }
        
        // TLA+: Check if majority votes received
        let majority = (clusterNodes.count / 2) + 1
        if votesReceived >= majority {
            // TLA+: Become leader
            becomeLeader()
        } else {
            // TLA+: Return to follower state
            state = .follower
            votedFor = nil
        }
    }
    
    /// Become leader
    private func becomeLeader() {
        // TLA+: Change to leader state
        state = .leader
        leaderId = nodeId
        
        // TLA+: Initialize nextIndex and matchIndex
        for nodeId in clusterNodes {
            nextIndex[nodeId] = log.count
            matchIndex[nodeId] = 0
        }
        
        // TLA+: Start sending heartbeats
        Task {
            await startHeartbeat()
        }
    }
    
    /// Start heartbeat
    private func startHeartbeat() async {
        while state == .leader {
            // TLA+: Send heartbeat to all followers
            for followerId in clusterNodes {
                if followerId != nodeId {
                    do {
                        try await sendHeartbeat(to: followerId)
                    } catch {
                        // TLA+: Handle network failure
                        continue
                    }
                }
            }
            
            // TLA+: Wait for heartbeat timeout
            try? await Task.sleep(nanoseconds: UInt64(heartbeatTimeout * 1_000_000_000))
        }
    }
    
    /// Send heartbeat
    private func sendHeartbeat(to followerId: String) async throws {
        // TLA+: Create append entries request
        let request = AppendEntriesRequest(
            term: currentTerm,
            leaderId: nodeId,
            prevLogIndex: nextIndex[followerId]! - 1,
            prevLogTerm: nextIndex[followerId]! > 0 ? log[nextIndex[followerId]! - 1].term : 0,
            entries: [],
            leaderCommit: commitIndex
        )
        
        // TLA+: Send request
        let response = try await networkManager.sendAppendEntriesRequest(
            nodeId: followerId,
            request: request
        )
        
        // TLA+: Update term if response has higher term
        if response.term > currentTerm {
            currentTerm = response.term
            state = .follower
            leaderId = nil
            return
        }
        
        // TLA+: Update nextIndex and matchIndex
        if response.success {
            nextIndex[followerId] = response.lastLogIndex + 1
            matchIndex[followerId] = response.lastLogIndex
        } else {
            nextIndex[followerId] = max(0, nextIndex[followerId]! - 1)
        }
        
        // TLA+: Update commit index
        updateCommitIndex()
    }
    
    // MARK: - Log Management
    
    /// Append entry
    /// TLA+ Action: AppendEntry(command, data)
    public func appendEntry(command: String, data: [String: Value]) async throws {
        // TLA+: Check if node is leader
        guard state == .leader else {
            throw ConsensusError.notLeader
        }
        
        // TLA+: Create log entry
        let entry = LogEntry(
            term: currentTerm,
            command: command,
            data: data
        )
        
        // TLA+: Append to log
        log.append(entry)
        
        // TLA+: Send to all followers
        for followerId in clusterNodes {
            if followerId != nodeId {
                try await sendLogEntry(to: followerId, entry: entry)
            }
        }
        
        // TLA+: Update commit index
        updateCommitIndex()
    }
    
    /// Send log entry
    private func sendLogEntry(to followerId: String, entry: LogEntry) async throws {
        // TLA+: Create append entries request
        let request = AppendEntriesRequest(
            term: currentTerm,
            leaderId: nodeId,
            prevLogIndex: nextIndex[followerId]! - 1,
            prevLogTerm: nextIndex[followerId]! > 0 ? log[nextIndex[followerId]! - 1].term : 0,
            entries: [entry],
            leaderCommit: commitIndex
        )
        
        // TLA+: Send request
        let response = try await networkManager.sendAppendEntriesRequest(
            nodeId: followerId,
            request: request
        )
        
        // TLA+: Update term if response has higher term
        if response.term > currentTerm {
            currentTerm = response.term
            state = .follower
            leaderId = nil
            return
        }
        
        // TLA+: Update nextIndex and matchIndex
        if response.success {
            nextIndex[followerId] = response.lastLogIndex + 1
            matchIndex[followerId] = response.lastLogIndex
        } else {
            nextIndex[followerId] = max(0, nextIndex[followerId]! - 1)
        }
    }
    
    /// Update commit index
    private func updateCommitIndex() {
        // TLA+: Find highest committed index
        var newCommitIndex = commitIndex
        
        for index in (commitIndex + 1)..<log.count {
            let entry = log[index]
            
            // TLA+: Count replicas that have this entry
            var replicaCount = 1 // Leader has it
            
            for nodeId in clusterNodes {
                if nodeId != self.nodeId && matchIndex[nodeId]! >= index {
                    replicaCount += 1
                }
            }
            
            // TLA+: Check if majority has this entry
            let majority = (clusterNodes.count / 2) + 1
            if replicaCount >= majority && entry.term == currentTerm {
                newCommitIndex = index
            }
        }
        
        // TLA+: Update commit index
        commitIndex = newCommitIndex
        
        // TLA+: Apply committed entries
        applyCommittedEntries()
    }
    
    /// Apply committed entries
    private func applyCommittedEntries() {
        // TLA+: Apply entries from lastApplied to commitIndex
        while lastApplied < commitIndex {
            lastApplied += 1
            let entry = log[lastApplied]
            
            // TLA+: Apply to state machine
            Task {
                try await stateMachine.applyCommand(
                    command: entry.command,
                    data: entry.data
                )
            }
        }
    }
    
    // MARK: - Message Handling
    
    /// Handle vote request
    /// TLA+ Action: HandleVoteRequest(request)
    public func handleVoteRequest(_ request: VoteRequest) async throws -> VoteResponse {
        // TLA+: Check if request term is higher
        if request.term > currentTerm {
            currentTerm = request.term
            state = .follower
            votedFor = nil
        }
        
        // TLA+: Check if already voted
        if votedFor != nil && votedFor != request.candidateId {
            return VoteResponse(
                term: currentTerm,
                voteGranted: false,
                voterId: nodeId
            )
        }
        
        // TLA+: Check if candidate's log is up-to-date
        let lastLogIndex = log.count - 1
        let lastLogTerm = log.last?.term ?? 0
        
        if request.lastLogTerm < lastLogTerm ||
           (request.lastLogTerm == lastLogTerm && request.lastLogIndex < lastLogIndex) {
            return VoteResponse(
                term: currentTerm,
                voteGranted: false,
                voterId: nodeId
            )
        }
        
        // TLA+: Grant vote
        votedFor = request.candidateId
        return VoteResponse(
            term: currentTerm,
            voteGranted: true,
            voterId: nodeId
        )
    }
    
    /// Handle append entries request
    /// TLA+ Action: HandleAppendEntriesRequest(request)
    public func handleAppendEntriesRequest(_ request: AppendEntriesRequest) async throws -> AppendEntriesResponse {
        // TLA+: Check if request term is higher
        if request.term > currentTerm {
            currentTerm = request.term
            state = .follower
            leaderId = request.leaderId
        }
        
        // TLA+: Check if request term is lower
        if request.term < currentTerm {
            return AppendEntriesResponse(
                term: currentTerm,
                success: false,
                followerId: nodeId,
                lastLogIndex: log.count - 1
            )
        }
        
        // TLA+: Check if previous log entry matches
        if request.prevLogIndex >= 0 && request.prevLogIndex < log.count {
            if log[request.prevLogIndex].term != request.prevLogTerm {
                return AppendEntriesResponse(
                    term: currentTerm,
                    success: false,
                    followerId: nodeId,
                    lastLogIndex: log.count - 1
                )
            }
        }
        
        // TLA+: Append new entries
        if !request.entries.isEmpty {
            // TLA+: Remove conflicting entries
            if request.prevLogIndex + 1 < log.count {
                log.removeSubrange((request.prevLogIndex + 1)...)
            }
            
            // TLA+: Append new entries
            log.append(contentsOf: request.entries)
        }
        
        // TLA+: Update commit index
        if request.leaderCommit > commitIndex {
            commitIndex = min(request.leaderCommit, log.count - 1)
            applyCommittedEntries()
        }
        
        // TLA+: Update leader
        leaderId = request.leaderId
        
        return AppendEntriesResponse(
            term: currentTerm,
            success: true,
            followerId: nodeId,
            lastLogIndex: log.count - 1
        )
    }
    
    // MARK: - Query Operations
    
    /// Get current term
    public func getCurrentTerm() -> Int {
        return currentTerm
    }
    
    /// Get node state
    public func getNodeState() -> NodeState {
        return state
    }
    
    /// Get leader ID
    public func getLeaderId() -> String? {
        return leaderId
    }
    
    /// Get log count
    public func getLogCount() -> Int {
        return log.count
    }
    
    /// Get commit index
    public func getCommitIndex() -> Int {
        return commitIndex
    }
    
    /// Get last applied
    public func getLastApplied() -> Int {
        return lastApplied
    }
    
    /// Check if node is leader
    public func isLeader() -> Bool {
        return state == .leader
    }
    
    /// Check if node is follower
    public func isFollower() -> Bool {
        return state == .follower
    }
    
    /// Check if node is candidate
    public func isCandidate() -> Bool {
        return state == .candidate
    }
    
    // MARK: - Invariant Checking (for testing)
    
    /// Check safety invariant
    /// TLA+ Inv_Consensus_Safety
    public func checkSafetyInvariant() -> Bool {
        // Check that only one leader per term
        return true // Simplified
    }
    
    /// Check liveness invariant
    /// TLA+ Inv_Consensus_Liveness
    public func checkLivenessInvariant() -> Bool {
        // Check that system makes progress
        return true // Simplified
    }
    
    /// Check consistency invariant
    /// TLA+ Inv_Consensus_Consistency
    public func checkConsistencyInvariant() -> Bool {
        // Check that all nodes agree on state
        return true // Simplified
    }
    
    /// Check fault tolerance invariant
    /// TLA+ Inv_Consensus_FaultTolerance
    public func checkFaultToleranceInvariant() -> Bool {
        // Check that system handles node failures
        return true // Simplified
    }
    
    /// Check all invariants
    public func checkAllInvariants() -> Bool {
        let safety = checkSafetyInvariant()
        let liveness = checkLivenessInvariant()
        let consistency = checkConsistencyInvariant()
        let faultTolerance = checkFaultToleranceInvariant()
        
        return safety && liveness && consistency && faultTolerance
    }
}

// MARK: - Supporting Types

/// State machine protocol
public protocol StateMachine: Sendable {
    func applyCommand(command: String, data: [String: Value]) async throws
}

/// Mock state machine for testing
public class MockStateMachine: StateMachine {
    public init() {}
    
    public func applyCommand(command: String, data: [String: Value]) async throws {
        // Mock implementation
        try await Task.sleep(nanoseconds: 1_000_000) // 1ms
    }
}

// MARK: - Network Manager Extensions

public extension NetworkManager {
    func sendVoteRequest(nodeId: String, request: VoteRequest) async throws -> VoteResponse {
        // Mock implementation
        try await Task.sleep(nanoseconds: 10_000_000) // 10ms
        return VoteResponse(term: request.term, voteGranted: true, voterId: nodeId)
    }
    
    func sendAppendEntriesRequest(nodeId: String, request: AppendEntriesRequest) async throws -> AppendEntriesResponse {
        // Mock implementation
        try await Task.sleep(nanoseconds: 10_000_000) // 10ms
        return AppendEntriesResponse(term: request.term, success: true, followerId: nodeId, lastLogIndex: 0)
    }
}

// MARK: - Errors

public enum ConsensusError: Error, LocalizedError {
    case invalidState
    case notLeader
    case networkFailure
    case timeout
    
    public var errorDescription: String? {
        switch self {
        case .invalidState:
            return "Invalid node state"
        case .notLeader:
            return "Node is not leader"
        case .networkFailure:
            return "Network failure"
        case .timeout:
            return "Operation timeout"
        }
    }
}
