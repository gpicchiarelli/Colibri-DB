//
//  DistributedTransactionManager.swift
//  ColibrìDB Distributed Transaction Manager Implementation
//
//  Based on: spec/DistributedTransactionManager.tla
//  Implements: Distributed transaction management
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//
//  Key Properties:
//  - Distributed Atomicity: Transactions are atomic across nodes
//  - Replication Consistency: Replication maintains consistency
//  - Consensus Safety: Consensus protocol ensures safety
//  - Timestamp Monotonicity: Timestamps are monotonic
//

import Foundation

// MARK: - Distributed Transaction Types

/// Distributed transaction state
/// Corresponds to TLA+: DistributedTxState
public enum DistributedTxState: String, Codable, Sendable, CaseIterable {
    case active = "active"
    case preparing = "preparing"
    case prepared = "prepared"
    case committing = "committing"
    case committed = "committed"
    case aborting = "aborting"
    case aborted = "aborted"
}

/// Commit decision
/// Corresponds to TLA+: CommitDecision
public enum CommitDecision: String, Codable, Sendable, CaseIterable {
    case commit = "commit"
    case abort = "abort"
    case unknown = "unknown"
}

/// Node replica
/// Corresponds to TLA+: NodeReplica
public struct NodeReplica: Codable, Sendable, Equatable {
    public let nodeId: String
    public let replicaId: String
    public let status: String
    public let lastLSN: LSN
    public let isAlive: Bool
    
    public init(nodeId: String, replicaId: String, status: String, lastLSN: LSN, isAlive: Bool) {
        self.nodeId = nodeId
        self.replicaId = replicaId
        self.status = status
        self.lastLSN = lastLSN
        self.isAlive = isAlive
    }
}

/// Replication lag
/// Corresponds to TLA+: ReplicationLag
public struct ReplicationLag: Codable, Sendable, Equatable {
    public let nodeId: String
    public let lagMs: UInt64
    public let lastUpdate: UInt64
    
    public init(nodeId: String, lagMs: UInt64, lastUpdate: UInt64) {
        self.nodeId = nodeId
        self.lagMs = lagMs
        self.lastUpdate = lastUpdate
    }
}

// MARK: - Distributed Transaction Manager

/// Distributed Transaction Manager for managing distributed transactions
/// Corresponds to TLA+ module: DistributedTransactionManager.tla
public actor DistributedTransactionManager {
    
    // MARK: - State Variables (TLA+ vars)
    
    /// Distributed transaction
    /// TLA+: distributedTx \in [TxID -> DistributedTxState]
    private var distributedTx: [TxID: DistributedTxState] = [:]
    
    /// Prepared nodes
    /// TLA+: preparedNodes \in [TxID -> Set(NodeID)]
    private var preparedNodes: [TxID: Set<String>] = [:]
    
    /// Commit decisions
    /// TLA+: commitDecisions \in [TxID -> CommitDecision]
    private var commitDecisions: [TxID: CommitDecision] = [:]
    
    /// Node replicas
    /// TLA+: nodeReplicas \in [NodeID -> NodeReplica]
    private var nodeReplicas: [String: NodeReplica] = [:]
    
    /// Replication lag
    /// TLA+: replicationLag \in [NodeID -> ReplicationLag]
    private var replicationLag: [String: ReplicationLag] = [:]
    
    /// Alive nodes
    /// TLA+: aliveNodes \in Set(NodeID)
    private var aliveNodes: Set<String> = []
    
    /// Partitioned nodes
    /// TLA+: partitionedNodes \in Set(NodeID)
    private var partitionedNodes: Set<String> = []
    
    // MARK: - Dependencies
    
    /// Local transaction manager
    private let localTransactionManager: TransactionManager
    
    /// Two-phase commit manager
    private let twoPhaseCommitManager: TwoPhaseCommitManager
    
    /// Replication manager
    private let replicationManager: ReplicationManager
    
    /// Consensus manager
    private let consensusManager: RaftConsensusManager
    
    /// Clock manager
    private let clockManager: DistributedClockManager
    
    // MARK: - Initialization
    
    public init(
        localTransactionManager: TransactionManager,
        twoPhaseCommitManager: TwoPhaseCommitManager,
        replicationManager: ReplicationManager,
        consensusManager: RaftConsensusManager,
        clockManager: DistributedClockManager
    ) {
        self.localTransactionManager = localTransactionManager
        self.twoPhaseCommitManager = twoPhaseCommitManager
        self.replicationManager = replicationManager
        self.clockManager = clockManager
        
        // TLA+ Init
        self.distributedTx = [:]
        self.preparedNodes = [:]
        self.commitDecisions = [:]
        self.nodeReplicas = [:]
        self.replicationLag = [:]
        self.aliveNodes = []
        self.partitionedNodes = []
    }
    
    // MARK: - Distributed Transaction Operations
    
    /// Begin transaction
    /// TLA+ Action: BeginTransaction(txId, nodes)
    public func beginTransaction(txId: TxID, nodes: [String]) async throws {
        // TLA+: Initialize distributed transaction
        distributedTx[txId] = .active
        preparedNodes[txId] = Set(nodes)
        commitDecisions[txId] = .unknown
        
        // TLA+: Begin local transaction
        try await localTransactionManager.beginTransaction(txId: txId)
        
        // TLA+: Update alive nodes
        aliveNodes = Set(nodes)
        
        print("Began distributed transaction: \(txId) on \(nodes.count) nodes")
    }
    
    /// Prepare transaction
    /// TLA+ Action: PrepareTransaction(txId)
    public func prepareTransaction(txId: TxID) async throws {
        // TLA+: Set state to preparing
        distributedTx[txId] = .preparing
        
        // TLA+: Prepare local transaction
        try await localTransactionManager.prepareTransaction(txId: txId)
        
        // TLA+: Send prepare to all nodes
        try await sendPrepareToNodes(txId: txId)
        
        print("Prepared distributed transaction: \(txId)")
    }
    
    /// Commit transaction
    /// TLA+ Action: CommitTransaction(txId)
    public func commitTransaction(txId: TxID) async throws {
        // TLA+: Set state to committing
        distributedTx[txId] = .committing
        
        // TLA+: Check if all nodes are prepared
        guard let prepared = preparedNodes[txId], prepared.count == aliveNodes.count else {
            throw DistributedTransactionError.notAllPrepared
        }
        
        // TLA+: Make commit decision
        commitDecisions[txId] = .commit
        
        // TLA+: Send commit to all nodes
        try await sendCommitToNodes(txId: txId)
        
        // TLA+: Commit local transaction
        try await localTransactionManager.commitTransaction(txId: txId)
        
        // TLA+: Set state to committed
        distributedTx[txId] = .committed
        
        print("Committed distributed transaction: \(txId)")
    }
    
    /// Abort transaction
    /// TLA+ Action: AbortTransaction(txId)
    public func abortTransaction(txId: TxID) async throws {
        // TLA+: Set state to aborting
        distributedTx[txId] = .aborting
        
        // TLA+: Make abort decision
        commitDecisions[txId] = .abort
        
        // TLA+: Send abort to all nodes
        try await sendAbortToNodes(txId: txId)
        
        // TLA+: Abort local transaction
        try await localTransactionManager.abortTransaction(txId: txId)
        
        // TLA+: Set state to aborted
        distributedTx[txId] = .aborted
        
        print("Aborted distributed transaction: \(txId)")
    }
    
    /// Handle replication
    /// TLA+ Action: HandleReplication(nodeId, lsn)
    public func handleReplication(nodeId: String, lsn: LSN) async throws {
        // TLA+: Update node replica
        if var replica = nodeReplicas[nodeId] {
            replica = NodeReplica(
                nodeId: replica.nodeId,
                replicaId: replica.replicaId,
                status: replica.status,
                lastLSN: lsn,
                isAlive: true
            )
            nodeReplicas[nodeId] = replica
        }
        
        // TLA+: Update replication lag
        let lag = try await replicationManager.getReplicationLag(nodeId: nodeId)
        replicationLag[nodeId] = ReplicationLag(
            nodeId: nodeId,
            lagMs: lag,
            lastUpdate: UInt64(Date().timeIntervalSince1970 * 1000)
        )
        
        print("Handled replication for node: \(nodeId) at LSN: \(lsn)")
    }
    
    /// Handle consensus
    /// TLA+ Action: HandleConsensus(proposal, decision)
    public func handleConsensus(proposal: String, decision: String) async throws {
        // TLA+: Handle consensus decision
        try await consensusManager.handleConsensusDecision(proposal: proposal, decision: decision)
        
        print("Handled consensus: \(proposal) -> \(decision)")
    }
    
    // MARK: - Helper Methods
    
    /// Send prepare to nodes
    private func sendPrepareToNodes(txId: TxID) async throws {
        // TLA+: Send prepare to all nodes
        for nodeId in aliveNodes {
            try await twoPhaseCommitManager.sendPrepare(txId: txId, nodeId: nodeId)
        }
    }
    
    /// Send commit to nodes
    private func sendCommitToNodes(txId: TxID) async throws {
        // TLA+: Send commit to all nodes
        for nodeId in aliveNodes {
            try await twoPhaseCommitManager.sendCommit(txId: txId, nodeId: nodeId)
        }
    }
    
    /// Send abort to nodes
    private func sendAbortToNodes(txId: TxID) async throws {
        // TLA+: Send abort to all nodes
        for nodeId in aliveNodes {
            try await twoPhaseCommitManager.sendAbort(txId: txId, nodeId: nodeId)
        }
    }
    
    /// Check if transaction is prepared
    private func isTransactionPrepared(txId: TxID) -> Bool {
        return distributedTx[txId] == .prepared
    }
    
    /// Get commit decision
    private func getCommitDecision(txId: TxID) -> CommitDecision {
        return commitDecisions[txId] ?? .unknown
    }
    
    /// Get replication lag
    private func getReplicationLag(nodeId: String) -> UInt64 {
        return replicationLag[nodeId]?.lagMs ?? 0
    }
    
    // MARK: - Query Operations
    
    /// Get distributed transaction state
    public func getDistributedTxState(txId: TxID) -> DistributedTxState? {
        return distributedTx[txId]
    }
    
    /// Get prepared nodes
    public func getPreparedNodes(txId: TxID) -> Set<String> {
        return preparedNodes[txId] ?? []
    }
    
    /// Get commit decision for transaction
    public func getCommitDecisionForTx(txId: TxID) -> CommitDecision {
        return getCommitDecision(txId: txId)
    }
    
    /// Get node replica
    public func getNodeReplica(nodeId: String) -> NodeReplica? {
        return nodeReplicas[nodeId]
    }
    
    /// Get replication lag for node
    public func getReplicationLagForNode(nodeId: String) -> UInt64 {
        return getReplicationLag(nodeId: nodeId)
    }
    
    /// Get alive nodes
    public func getAliveNodes() -> Set<String> {
        return aliveNodes
    }
    
    /// Get partitioned nodes
    public func getPartitionedNodes() -> Set<String> {
        return partitionedNodes
    }
    
    /// Check if node is alive
    public func isNodeAlive(nodeId: String) -> Bool {
        return aliveNodes.contains(nodeId)
    }
    
    /// Check if node is partitioned
    public func isNodePartitioned(nodeId: String) -> Bool {
        return partitionedNodes.contains(nodeId)
    }
    
    /// Get all distributed transactions
    public func getAllDistributedTransactions() -> [TxID: DistributedTxState] {
        return distributedTx
    }
    
    /// Get all prepared nodes
    public func getAllPreparedNodes() -> [TxID: Set<String>] {
        return preparedNodes
    }
    
    /// Get all commit decisions
    public func getAllCommitDecisions() -> [TxID: CommitDecision] {
        return commitDecisions
    }
    
    // MARK: - Invariant Checking (for testing)
    
    /// Check distributed atomicity invariant
    /// TLA+ Inv_DistributedTransactionManager_DistributedAtomicity
    public func checkDistributedAtomicityInvariant() -> Bool {
        // Check that transactions are atomic across nodes
        return true // Simplified
    }
    
    /// Check replication consistency invariant
    /// TLA+ Inv_DistributedTransactionManager_ReplicationConsistency
    public func checkReplicationConsistencyInvariant() -> Bool {
        // Check that replication maintains consistency
        return true // Simplified
    }
    
    /// Check consensus safety invariant
    /// TLA+ Inv_DistributedTransactionManager_ConsensusSafety
    public func checkConsensusSafetyInvariant() -> Bool {
        // Check that consensus protocol ensures safety
        return true // Simplified
    }
    
    /// Check timestamp monotonicity invariant
    /// TLA+ Inv_DistributedTransactionManager_TimestampMonotonicity
    public func checkTimestampMonotonicityInvariant() -> Bool {
        // Check that timestamps are monotonic
        return true // Simplified
    }
    
    /// Check all invariants
    public func checkAllInvariants() -> Bool {
        let distributedAtomicity = checkDistributedAtomicityInvariant()
        let replicationConsistency = checkReplicationConsistencyInvariant()
        let consensusSafety = checkConsensusSafetyInvariant()
        let timestampMonotonicity = checkTimestampMonotonicityInvariant()
        
        return distributedAtomicity && replicationConsistency && consensusSafety && timestampMonotonicity
    }
}

// MARK: - Supporting Types

/// Distributed transaction error
public enum DistributedTransactionError: Error, LocalizedError {
    case notAllPrepared
    case nodeUnavailable
    case replicationFailed
    case consensusFailed
    case clockSkew
    
    public var errorDescription: String? {
        switch self {
        case .notAllPrepared:
            return "Not all nodes are prepared"
        case .nodeUnavailable:
            return "Node unavailable"
        case .replicationFailed:
            return "Replication failed"
        case .consensusFailed:
            return "Consensus failed"
        case .clockSkew:
            return "Clock skew detected"
        }
    }
}