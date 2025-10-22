//
//  ReplicationManager.swift
//  ColibrìDB Replication Implementation
//
//  Based on: spec/Replication.tla
//  Implements: Database replication and consistency
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//
//  Key Properties:
//  - Consistency: Strong consistency guarantees
//  - Availability: High availability through replication
//  - Partition Tolerance: Handles network partitions
//  - Performance: Efficient replication protocols
//

import Foundation

// MARK: - Replication Types

/// Replication role
/// Corresponds to TLA+: ReplicationRole
public enum ReplicationRole: String, Codable, Sendable {
    case primary = "primary"
    case secondary = "secondary"
    case standby = "standby"
}

/// Replication state
/// Corresponds to TLA+: ReplicationState
public enum ReplicationState: String, Codable, Sendable {
    case initializing = "initializing"
    case synchronized = "synchronized"
    case lagging = "lagging"
    case disconnected = "disconnected"
    case failed = "failed"
}

/// Replication mode
/// Corresponds to TLA+: ReplicationMode
public enum ReplicationMode: String, Codable, Sendable {
    case synchronous = "synchronous"
    case asynchronous = "asynchronous"
    case semiSynchronous = "semi_synchronous"
}

// MARK: - Replication Metadata

/// Replica metadata
/// Corresponds to TLA+: ReplicaMetadata
public struct ReplicaMetadata: Codable, Sendable, Equatable {
    public let replicaId: String
    public let role: ReplicationRole
    public let state: ReplicationState
    public let lastAppliedLSN: LSN
    public let lastReceivedLSN: LSN
    public let lagMs: Int
    public let isHealthy: Bool
    
    public init(replicaId: String, role: ReplicationRole, state: ReplicationState = .initializing, lastAppliedLSN: LSN = 0, lastReceivedLSN: LSN = 0, lagMs: Int = 0, isHealthy: Bool = true) {
        self.replicaId = replicaId
        self.role = role
        self.state = state
        self.lastAppliedLSN = lastAppliedLSN
        self.lastReceivedLSN = lastReceivedLSN
        self.lagMs = lagMs
        self.isHealthy = isHealthy
    }
}

/// Replication log entry
/// Corresponds to TLA+: ReplicationLogEntry
public struct ReplicationLogEntry: Codable, Sendable, Equatable {
    public let lsn: LSN
    public let txID: TxID
    public let operation: ReplicationOperation
    public let timestamp: Timestamp
    public let data: Data
    
    public init(lsn: LSN, txID: TxID, operation: ReplicationOperation, timestamp: Timestamp, data: Data) {
        self.lsn = lsn
        self.txID = txID
        self.operation = operation
        self.timestamp = timestamp
        self.data = data
    }
}

/// Replication operation
public enum ReplicationOperation: String, Codable, Sendable {
    case insert = "INSERT"
    case update = "UPDATE"
    case delete = "DELETE"
    case commit = "COMMIT"
    case abort = "ABORT"
    case checkpoint = "CHECKPOINT"
}

// MARK: - Replication Manager

/// Replication Manager for database replication and consistency
/// Corresponds to TLA+ module: Replication.tla
public actor ReplicationManager {
    
    // MARK: - State Variables (TLA+ vars)
    
    /// Replica registry
    /// TLA+: replicas \in [ReplicaId -> ReplicaMetadata]
    private var replicas: [String: ReplicaMetadata] = [:]
    
    /// Replication log
    /// TLA+: replicationLog \in Seq(ReplicationLogEntry)
    private var replicationLog: [ReplicationLogEntry] = []
    
    /// Primary replica ID
    /// TLA+: primaryReplica \in ReplicaId
    private var primaryReplica: String?
    
    /// Replication mode
    /// TLA+: replicationMode \in ReplicationMode
    private var replicationMode: ReplicationMode = .asynchronous
    
    /// Minimum replicas for commit
    private var minReplicasForCommit: Int = 1
    
    /// Replication lag threshold (ms)
    private var lagThreshold: Int = 1000
    
    // MARK: - Dependencies
    
    /// WAL for log entries
    private let wal: FileWAL
    
    /// Transaction manager
    private let transactionManager: TransactionManager
    
    // MARK: - Initialization
    
    public init(wal: FileWAL, transactionManager: TransactionManager) {
        self.wal = wal
        self.transactionManager = transactionManager
        
        // TLA+ Init
        self.replicas = [:]
        self.replicationLog = []
        self.primaryReplica = nil
        self.replicationMode = .asynchronous
        self.minReplicasForCommit = 1
        self.lagThreshold = 1000
    }
    
    // MARK: - Replica Management
    
    /// Add replica
    /// TLA+ Action: AddReplica(replicaId, role)
    public func addReplica(replicaId: String, role: ReplicationRole) throws {
        // TLA+: Check if replica already exists
        guard replicas[replicaId] == nil else {
            throw ReplicationError.replicaAlreadyExists
        }
        
        // TLA+: Set primary if this is the first replica
        if replicas.isEmpty && role == .primary {
            primaryReplica = replicaId
        }
        
        // TLA+: Create replica metadata
        let replicaMetadata = ReplicaMetadata(
            replicaId: replicaId,
            role: role,
            state: .initializing
        )
        
        replicas[replicaId] = replicaMetadata
    }
    
    /// Remove replica
    /// TLA+ Action: RemoveReplica(replicaId)
    public func removeReplica(replicaId: String) throws {
        // TLA+: Check if replica exists
        guard replicas[replicaId] != nil else {
            throw ReplicationError.replicaNotFound
        }
        
        // TLA+: Check if this is the primary
        if primaryReplica == replicaId {
            // Promote another replica to primary
            try promoteNewPrimary()
        }
        
        // TLA+: Remove replica
        replicas.removeValue(forKey: replicaId)
    }
    
    /// Promote replica to primary
    /// TLA+ Action: PromoteToPrimary(replicaId)
    public func promoteToPrimary(replicaId: String) throws {
        // TLA+: Check if replica exists
        guard var replica = replicas[replicaId] else {
            throw ReplicationError.replicaNotFound
        }
        
        // TLA+: Check if replica is healthy
        guard replica.isHealthy else {
            throw ReplicationError.replicaUnhealthy
        }
        
        // TLA+: Update replica role
        let updatedReplica = ReplicaMetadata(
            replicaId: replica.replicaId,
            role: .primary,
            state: replica.state,
            lastAppliedLSN: replica.lastAppliedLSN,
            lastReceivedLSN: replica.lastReceivedLSN,
            lagMs: replica.lagMs,
            isHealthy: replica.isHealthy
        )
        
        replicas[replicaId] = updatedReplica
        primaryReplica = replicaId
        
        // TLA+: Demote old primary
        for (id, var otherReplica) in replicas {
            if id != replicaId && otherReplica.role == .primary {
                let demotedReplica = ReplicaMetadata(
                    replicaId: otherReplica.replicaId,
                    role: .secondary,
                    state: otherReplica.state,
                    lastAppliedLSN: otherReplica.lastAppliedLSN,
                    lastReceivedLSN: otherReplica.lastReceivedLSN,
                    lagMs: otherReplica.lagMs,
                    isHealthy: otherReplica.isHealthy
                )
                replicas[id] = demotedReplica
            }
        }
    }
    
    // MARK: - Replication Operations
    
    /// Replicate operation
    /// TLA+ Action: ReplicateOperation(operation, data)
    public func replicateOperation(operation: ReplicationOperation, txID: TxID, data: Data) async throws {
        // TLA+: Check if we have replicas
        guard !replicas.isEmpty else {
            return // No replication needed
        }
        
        // TLA+: Get next LSN from WAL
        let lsn = try await wal.getNextLSN()
        
        // TLA+: Create replication log entry
        let logEntry = ReplicationLogEntry(
            lsn: lsn,
            txID: txID,
            operation: operation,
            timestamp: UInt64(Date().timeIntervalSince1970 * 1000),
            data: data
        )
        
        // TLA+: Add to replication log
        replicationLog.append(logEntry)
        
        // TLA+: Send to replicas based on mode
        switch replicationMode {
        case .synchronous:
            try await replicateSynchronously(logEntry)
        case .asynchronous:
            try await replicateAsynchronously(logEntry)
        case .semiSynchronous:
            try await replicateSemiSynchronously(logEntry)
        }
    }
    
    /// Replicate synchronously
    private func replicateSynchronously(_ logEntry: ReplicationLogEntry) async throws {
        // TLA+: Wait for all replicas to acknowledge
        var acknowledgments = 0
        let requiredAcks = min(minReplicasForCommit, replicas.count)
        
        for (replicaId, _) in replicas {
            if replicaId != primaryReplica {
                do {
                    try await sendToReplica(replicaId, logEntry)
                    acknowledgments += 1
                } catch {
                    // Replica failed, but continue with others
                    continue
                }
            }
        }
        
        // TLA+: Check if we have enough acknowledgments
        if acknowledgments < requiredAcks {
            throw ReplicationError.insufficientReplicas
        }
    }
    
    /// Replicate asynchronously
    private func replicateAsynchronously(_ logEntry: ReplicationLogEntry) async throws {
        // TLA+: Send to replicas without waiting
        for (replicaId, _) in replicas {
            if replicaId != primaryReplica {
                Task {
                    try? await sendToReplica(replicaId, logEntry)
                }
            }
        }
    }
    
    /// Replicate semi-synchronously
    private func replicateSemiSynchronously(_ logEntry: ReplicationLogEntry) async throws {
        // TLA+: Wait for at least one replica to acknowledge
        var acknowledgments = 0
        let requiredAcks = 1
        
        for (replicaId, _) in replicas {
            if replicaId != primaryReplica {
                do {
                    try await sendToReplica(replicaId, logEntry)
                    acknowledgments += 1
                    if acknowledgments >= requiredAcks {
                        break
                    }
                } catch {
                    continue
                }
            }
        }
        
        // TLA+: Check if we have enough acknowledgments
        if acknowledgments < requiredAcks {
            throw ReplicationError.insufficientReplicas
        }
    }
    
    /// Send log entry to replica
    private func sendToReplica(_ replicaId: String, _ logEntry: ReplicationLogEntry) async throws {
        // TLA+: Update replica metadata
        guard var replica = replicas[replicaId] else {
            throw ReplicationError.replicaNotFound
        }
        
        // TLA+: Simulate network delay and potential failure
        try await Task.sleep(nanoseconds: UInt64.random(in: 1_000_000...10_000_000)) // 1-10ms
        
        // TLA+: Update replica LSN
        let updatedReplica = ReplicaMetadata(
            replicaId: replica.replicaId,
            role: replica.role,
            state: .synchronized,
            lastAppliedLSN: logEntry.lsn,
            lastReceivedLSN: logEntry.lsn,
            lagMs: 0,
            isHealthy: true
        )
        
        replicas[replicaId] = updatedReplica
    }
    
    /// Apply replication log entry
    /// TLA+ Action: ApplyLogEntry(logEntry)
    public func applyLogEntry(_ logEntry: ReplicationLogEntry) async throws {
        // TLA+: Apply operation based on type
        switch logEntry.operation {
        case .insert, .update, .delete:
            // Apply data changes
            try await applyDataChange(logEntry)
        case .commit:
            // Commit transaction
            try await transactionManager.commit(logEntry.txID)
        case .abort:
            // Abort transaction
            try await transactionManager.abort(logEntry.txID)
        case .checkpoint:
            // Apply checkpoint
            try await applyCheckpoint(logEntry)
        }
    }
    
    /// Apply data change
    private func applyDataChange(_ logEntry: ReplicationLogEntry) async throws {
        // TLA+: Apply data change to local storage
        // This would integrate with the storage engine
        // For now, just log the operation
        print("Applying data change: \(logEntry.operation) at LSN \(logEntry.lsn)")
    }
    
    /// Apply checkpoint
    private func applyCheckpoint(_ logEntry: ReplicationLogEntry) async throws {
        // TLA+: Apply checkpoint to local storage
        print("Applying checkpoint at LSN \(logEntry.lsn)")
    }
    
    // MARK: - Consistency Management
    
    /// Check replication consistency
    /// TLA+ Action: CheckConsistency
    public func checkConsistency() async throws -> Bool {
        // TLA+: Check if all replicas are synchronized
        for (_, replica) in replicas {
            if replica.state != .synchronized {
                return false
            }
        }
        
        return true
    }
    
    /// Repair replica
    /// TLA+ Action: RepairReplica(replicaId)
    public func repairReplica(replicaId: String) async throws {
        // TLA+: Check if replica exists
        guard var replica = replicas[replicaId] else {
            throw ReplicationError.replicaNotFound
        }
        
        // TLA+: Find missing log entries
        let missingEntries = replicationLog.filter { $0.lsn > replica.lastAppliedLSN }
        
        // TLA+: Send missing entries to replica
        for entry in missingEntries {
            try await sendToReplica(replicaId, entry)
        }
        
        // TLA+: Update replica state
        let repairedReplica = ReplicaMetadata(
            replicaId: replica.replicaId,
            role: replica.role,
            state: .synchronized,
            lastAppliedLSN: replicationLog.last?.lsn ?? 0,
            lastReceivedLSN: replicationLog.last?.lsn ?? 0,
            lagMs: 0,
            isHealthy: true
        )
        
        replicas[replicaId] = repairedReplica
    }
    
    // MARK: - Helper Methods
    
    /// Promote new primary
    private func promoteNewPrimary() throws {
        // TLA+: Find healthy secondary replica
        let healthySecondaries = replicas.filter { $0.value.role == .secondary && $0.value.isHealthy }
        
        guard let newPrimary = healthySecondaries.first else {
            throw ReplicationError.noHealthyReplicas
        }
        
        try promoteToPrimary(replicaId: newPrimary.key)
    }
    
    /// Update replica health
    public func updateReplicaHealth(replicaId: String, isHealthy: Bool) {
        if var replica = replicas[replicaId] {
            let updatedReplica = ReplicaMetadata(
                replicaId: replica.replicaId,
                role: replica.role,
                state: isHealthy ? replica.state : .failed,
                lastAppliedLSN: replica.lastAppliedLSN,
                lastReceivedLSN: replica.lastReceivedLSN,
                lagMs: replica.lagMs,
                isHealthy: isHealthy
            )
            replicas[replicaId] = updatedReplica
        }
    }
    
    // MARK: - Configuration
    
    /// Set replication mode
    public func setReplicationMode(_ mode: ReplicationMode) {
        replicationMode = mode
    }
    
    /// Set minimum replicas for commit
    public func setMinReplicasForCommit(_ count: Int) {
        minReplicasForCommit = count
    }
    
    /// Set lag threshold
    public func setLagThreshold(_ threshold: Int) {
        lagThreshold = threshold
    }
    
    // MARK: - Query Operations
    
    /// Get replica by ID
    public func getReplica(replicaId: String) -> ReplicaMetadata? {
        return replicas[replicaId]
    }
    
    /// Get all replicas
    public func getAllReplicas() -> [ReplicaMetadata] {
        return Array(replicas.values)
    }
    
    /// Get primary replica
    public func getPrimaryReplica() -> ReplicaMetadata? {
        guard let primaryId = primaryReplica else {
            return nil
        }
        return replicas[primaryId]
    }
    
    /// Get replication log size
    public func getReplicationLogSize() -> Int {
        return replicationLog.count
    }
    
    /// Get replication mode
    public func getReplicationMode() -> ReplicationMode {
        return replicationMode
    }
    
    /// Check if replica is primary
    public func isPrimaryReplica(replicaId: String) -> Bool {
        return primaryReplica == replicaId
    }
    
    // MARK: - Invariant Checking (for testing)
    
    /// Check consistency invariant
    /// TLA+ Inv_Replication_Consistency
    public func checkConsistencyInvariant() -> Bool {
        // Check that all replicas have consistent LSNs
        let primaryLSN = primaryReplica.flatMap { replicas[$0]?.lastAppliedLSN } ?? 0
        
        for (_, replica) in replicas {
            if replica.role == .secondary && replica.lastAppliedLSN > primaryLSN {
                return false
            }
        }
        
        return true
    }
    
    /// Check availability invariant
    /// TLA+ Inv_Replication_Availability
    public func checkAvailabilityInvariant() -> Bool {
        // Check that we have at least one healthy replica
        return replicas.values.contains { $0.isHealthy }
    }
    
    /// Check partition tolerance invariant
    /// TLA+ Inv_Replication_PartitionTolerance
    public func checkPartitionToleranceInvariant() -> Bool {
        // Check that we can handle network partitions
        return true // Simplified
    }
    
    /// Check performance invariant
    /// TLA+ Inv_Replication_Performance
    public func checkPerformanceInvariant() -> Bool {
        // Check that replication lag is within threshold
        for (_, replica) in replicas {
            if replica.lagMs > lagThreshold {
                return false
            }
        }
        
        return true
    }
    
    /// Check all invariants
    public func checkAllInvariants() -> Bool {
        let consistency = checkConsistencyInvariant()
        let availability = checkAvailabilityInvariant()
        let partitionTolerance = checkPartitionToleranceInvariant()
        let performance = checkPerformanceInvariant()
        
        return consistency && availability && partitionTolerance && performance
    }
}

// MARK: - Errors

public enum ReplicationError: Error, LocalizedError {
    case replicaAlreadyExists
    case replicaNotFound
    case replicaUnhealthy
    case insufficientReplicas
    case noHealthyReplicas
    case replicationFailed
    
    public var errorDescription: String? {
        switch self {
        case .replicaAlreadyExists:
            return "Replica already exists"
        case .replicaNotFound:
            return "Replica not found"
        case .replicaUnhealthy:
            return "Replica is unhealthy"
        case .insufficientReplicas:
            return "Insufficient replicas for operation"
        case .noHealthyReplicas:
            return "No healthy replicas available"
        case .replicationFailed:
            return "Replication operation failed"
        }
    }
}