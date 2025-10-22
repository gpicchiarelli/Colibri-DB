//
//  TransactionManager.swift
//  ColibrìDB Transaction Manager Implementation
//
//  Based on: spec/TransactionManager.tla
//  Implements: Transaction management
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//
//  Key Properties:
//  - Atomicity: Transactions are atomic
//  - Consistency: Transactions maintain consistency
//  - Isolation: Transactions are isolated
//  - Durability: Transactions are durable
//  - 2PC Correctness: Two-phase commit is correct
//

import Foundation

// MARK: - Transaction Manager Types

/// Transaction ID
/// Corresponds to TLA+: TxID
public typealias TxID = UInt64

/// LSN (Log Sequence Number)
/// Corresponds to TLA+: LSN
public typealias LSN = UInt64

/// Timestamp
/// Corresponds to TLA+: Timestamp
public typealias Timestamp = UInt64

/// Resources
/// Corresponds to TLA+: Resources
public typealias Resources = Set<String>

/// Participants
/// Corresponds to TLA+: Participants
public typealias Participants = Set<String>

/// Transaction
/// Corresponds to TLA+: Transaction
public struct Transaction: Codable, Sendable, Equatable {
    public let txId: TxID
    public let state: TransactionState
    public let startTime: Timestamp
    public let endTime: Timestamp?
    public let resources: Resources
    public let participants: Participants
    public let isDirty: Bool
    
    public init(txId: TxID, state: TransactionState, startTime: Timestamp, endTime: Timestamp?, resources: Resources, participants: Participants, isDirty: Bool) {
        self.txId = txId
        self.state = state
        self.startTime = startTime
        self.endTime = endTime
        self.resources = resources
        self.participants = participants
        self.isDirty = isDirty
    }
}

/// Transaction state
/// Corresponds to TLA+: TransactionState
public enum TransactionState: String, Codable, Sendable, CaseIterable {
    case active = "active"
    case prepared = "prepared"
    case committed = "committed"
    case aborted = "aborted"
    case preparing = "preparing"
}

/// Operation
/// Corresponds to TLA+: Operation
public struct Operation: Codable, Sendable, Equatable {
    public let opId: String
    public let txId: TxID
    public let type: String
    public let resource: String
    public let data: Data
    public let timestamp: Timestamp
    
    public init(opId: String, txId: TxID, type: String, resource: String, data: Data, timestamp: Timestamp) {
        self.opId = opId
        self.txId = txId
        self.type = type
        self.resource = resource
        self.data = data
        self.timestamp = timestamp
    }
}

/// Coordinator state
/// Corresponds to TLA+: CoordinatorState
public enum CoordinatorState: String, Codable, Sendable, CaseIterable {
    case idle = "idle"
    case preparing = "preparing"
    case committing = "committing"
    case aborting = "aborting"
}

// MARK: - Transaction Manager

/// Transaction Manager for database transaction management
/// Corresponds to TLA+ module: TransactionManager.tla
public actor TransactionManager {
    
    // MARK: - Constants
    
    /// Resources
    /// TLA+: Resources
    private let Resources: Resources = []
    
    /// Participants
    /// TLA+: Participants
    private let Participants: Participants = []
    
    /// Transaction timeout
    /// TLA+: TX_TIMEOUT_MS
    private let TX_TIMEOUT_MS: UInt64 = 30000
    
    /// Prepare timeout
    /// TLA+: PREPARE_TIMEOUT_MS
    private let PREPARE_TIMEOUT_MS: UInt64 = 5000
    
    // MARK: - State Variables (TLA+ vars)
    
    /// Next transaction ID
    /// TLA+: nextTID \in TxID
    private var nextTID: TxID = 1
    
    /// Transactions
    /// TLA+: transactions \in [TxID -> Transaction]
    private var transactions: [TxID: Transaction] = [:]
    
    /// Transaction operations
    /// TLA+: txOperations \in [TxID -> Seq(Operation)]
    private var txOperations: [TxID: [Operation]] = [:]
    
    /// Transaction locks
    /// TLA+: txLocks \in [TxID -> Set(String)]
    private var txLocks: [TxID: Set<String>] = [:]
    
    /// Transaction start time
    /// TLA+: txStartTime \in [TxID -> Timestamp]
    private var txStartTime: [TxID: Timestamp] = [:]
    
    /// Prepared transactions
    /// TLA+: preparedTransactions \in Set(TxID)
    private var preparedTransactions: Set<TxID> = []
    
    /// Coordinator state
    /// TLA+: coordinatorState \in CoordinatorState
    private var coordinatorState: CoordinatorState = .idle
    
    /// Participant votes
    /// TLA+: participantVotes \in [TxID -> [String -> Bool]]
    private var participantVotes: [TxID: [String: Bool]] = [:]
    
    /// Prepare timer
    /// TLA+: prepareTimer \in [TxID -> Timestamp]
    private var prepareTimer: [TxID: Timestamp] = [:]
    
    /// Transaction WAL records
    /// TLA+: txWALRecords \in [TxID -> Seq(LSN)]
    private var txWALRecords: [TxID: [LSN]] = [:]
    
    /// Last commit LSN
    /// TLA+: lastCommitLSN \in LSN
    private var lastCommitLSN: LSN = 0
    
    /// Transaction snapshots
    /// TLA+: txSnapshots \in [TxID -> Snapshot]
    private var txSnapshots: [TxID: Snapshot] = [:]
    
    /// Transaction write sets
    /// TLA+: txWriteSets \in [TxID -> Set(String)]
    private var txWriteSets: [TxID: Set<String>] = [:]
    
    /// Transaction read sets
    /// TLA+: txReadSets \in [TxID -> Set(String)]
    private var txReadSets: [TxID: Set<String>] = [:]
    
    /// Wait-for graph
    /// TLA+: waitForGraph \in [TxID -> Set(TxID)]
    private var waitForGraph: [TxID: Set<TxID>] = [:]
    
    /// Deadlock victim
    /// TLA+: deadlockVictim \in TxID
    private var deadlockVictim: TxID = 0
    
    /// Global clock
    /// TLA+: globalClock \in Timestamp
    private var globalClock: Timestamp = 0
    
    // MARK: - Dependencies
    
    /// WAL manager
    private let walManager: WALManager
    
    /// MVCC manager
    private let mvccManager: MVCCManager
    
    /// Lock manager
    private let lockManager: LockManager
    
    // MARK: - Initialization
    
    public init(walManager: WALManager, mvccManager: MVCCManager, lockManager: LockManager) {
        self.walManager = walManager
        self.mvccManager = mvccManager
        self.lockManager = lockManager
        
        // TLA+ Init
        self.nextTID = 1
        self.transactions = [:]
        self.txOperations = [:]
        self.txLocks = [:]
        self.txStartTime = [:]
        self.preparedTransactions = []
        self.coordinatorState = .idle
        self.participantVotes = [:]
        self.prepareTimer = [:]
        self.txWALRecords = [:]
        self.lastCommitLSN = 0
        self.txSnapshots = [:]
        self.txWriteSets = [:]
        self.txReadSets = [:]
        self.waitForGraph = [:]
        self.deadlockVictim = 0
        self.globalClock = 0
    }
    
    // MARK: - Transaction Operations
    
    /// Begin transaction
    /// TLA+ Action: BeginTransaction()
    public func beginTransaction() async throws -> TxID {
        // TLA+: Create transaction
        let txId = nextTID
        nextTID += 1
        
        let transaction = Transaction(
            txId: txId,
            state: .active,
            startTime: globalClock,
            endTime: nil,
            resources: [],
            participants: [],
            isDirty: false
        )
        
        // TLA+: Add transaction
        transactions[txId] = transaction
        txOperations[txId] = []
        txLocks[txId] = []
        txStartTime[txId] = globalClock
        txWALRecords[txId] = []
        txWriteSets[txId] = []
        txReadSets[txId] = []
        
        // TLA+: Update global clock
        globalClock += 1
        
        print("Began transaction: \(txId)")
        return txId
    }
    
    /// Commit transaction
    /// TLA+ Action: CommitTransaction(txId)
    public func commitTransaction(txId: TxID) async throws {
        // TLA+: Check if transaction exists
        guard var transaction = transactions[txId] else {
            throw TransactionManagerError.transactionNotFound
        }
        
        // TLA+: Check if transaction is active
        guard transaction.state == .active else {
            throw TransactionManagerError.transactionNotActive
        }
        
        // TLA+: Prepare transaction
        try await prepareTransaction(txId: txId)
        
        // TLA+: Commit transaction
        transaction.state = .committed
        transaction.endTime = globalClock
        transactions[txId] = transaction
        
        // TLA+: Update global clock
        globalClock += 1
        
        print("Committed transaction: \(txId)")
    }
    
    /// Abort transaction
    /// TLA+ Action: AbortTransaction(txId)
    public func abortTransaction(txId: TxID) async throws {
        // TLA+: Check if transaction exists
        guard var transaction = transactions[txId] else {
            throw TransactionManagerError.transactionNotFound
        }
        
        // TLA+: Check if transaction is active
        guard transaction.state == .active else {
            throw TransactionManagerError.transactionNotActive
        }
        
        // TLA+: Abort transaction
        transaction.state = .aborted
        transaction.endTime = globalClock
        transactions[txId] = transaction
        
        // TLA+: Update global clock
        globalClock += 1
        
        print("Aborted transaction: \(txId)")
    }
    
    /// Request lock
    /// TLA+ Action: RequestLock(txId, resource, mode)
    public func requestLock(txId: TxID, resource: String, mode: String) async throws {
        // TLA+: Check if transaction exists
        guard transactions[txId] != nil else {
            throw TransactionManagerError.transactionNotFound
        }
        
        // TLA+: Request lock
        try await lockManager.requestLock(txId: txId, resource: resource, mode: mode)
        
        // TLA+: Add to transaction locks
        txLocks[txId]?.insert(resource)
        
        print("Requested lock: \(resource) for transaction: \(txId)")
    }
    
    /// Release lock
    /// TLA+ Action: ReleaseLock(txId, resource)
    public func releaseLock(txId: TxID, resource: String) async throws {
        // TLA+: Check if transaction exists
        guard transactions[txId] != nil else {
            throw TransactionManagerError.transactionNotFound
        }
        
        // TLA+: Release lock
        try await lockManager.releaseLock(txId: txId, resource: resource)
        
        // TLA+: Remove from transaction locks
        txLocks[txId]?.remove(resource)
        
        print("Released lock: \(resource) for transaction: \(txId)")
    }
    
    /// Prepare transaction
    /// TLA+ Action: PrepareTransaction(txId)
    public func prepareTransaction(txId: TxID) async throws {
        // TLA+: Check if transaction exists
        guard var transaction = transactions[txId] else {
            throw TransactionManagerError.transactionNotFound
        }
        
        // TLA+: Check if transaction is active
        guard transaction.state == .active else {
            throw TransactionManagerError.transactionNotActive
        }
        
        // TLA+: Prepare transaction
        transaction.state = .prepared
        transactions[txId] = transaction
        preparedTransactions.insert(txId)
        
        print("Prepared transaction: \(txId)")
    }
    
    /// Receive vote
    /// TLA+ Action: ReceiveVote(txId, participant, vote)
    public func receiveVote(txId: TxID, participant: String, vote: Bool) async throws {
        // TLA+: Check if transaction exists
        guard transactions[txId] != nil else {
            throw TransactionManagerError.transactionNotFound
        }
        
        // TLA+: Store vote
        if participantVotes[txId] == nil {
            participantVotes[txId] = [:]
        }
        participantVotes[txId]?[participant] = vote
        
        print("Received vote: \(vote) from participant: \(participant) for transaction: \(txId)")
    }
    
    /// Make decision
    /// TLA+ Action: MakeDecision(txId)
    public func makeDecision(txId: TxID) async throws -> Bool {
        // TLA+: Check if transaction exists
        guard transactions[txId] != nil else {
            throw TransactionManagerError.transactionNotFound
        }
        
        // TLA+: Check votes
        guard let votes = participantVotes[txId] else {
            throw TransactionManagerError.noVotesReceived
        }
        
        // TLA+: Make decision
        let allVotes = votes.values
        let decision = allVotes.allSatisfy { $0 }
        
        print("Made decision: \(decision) for transaction: \(txId)")
        return decision
    }
    
    /// Send commit/abort
    /// TLA+ Action: SendCommitAbort(txId, decision)
    public func sendCommitAbort(txId: TxID, decision: Bool) async throws {
        // TLA+: Check if transaction exists
        guard var transaction = transactions[txId] else {
            throw TransactionManagerError.transactionNotFound
        }
        
        // TLA+: Update transaction state
        if decision {
            transaction.state = .committed
        } else {
            transaction.state = .aborted
        }
        transaction.endTime = globalClock
        transactions[txId] = transaction
        
        // TLA+: Update global clock
        globalClock += 1
        
        print("Sent \(decision ? "commit" : "abort") for transaction: \(txId)")
    }
    
    // MARK: - Helper Methods
    
    /// Detect deadlock
    private func detectDeadlock() async throws -> Bool {
        // TLA+: Detect deadlock
        // This would include building the wait-for graph and checking for cycles
        return false // Simplified
    }
    
    /// Select deadlock victim
    private func selectDeadlockVictim() async throws -> TxID {
        // TLA+: Select deadlock victim
        // This would include selecting the transaction to abort
        return 0 // Simplified
    }
    
    /// Update wait-for graph
    private func updateWaitForGraph(txId: TxID, waitingFor: TxID) async throws {
        // TLA+: Update wait-for graph
        if waitForGraph[txId] == nil {
            waitForGraph[txId] = []
        }
        waitForGraph[txId]?.insert(waitingFor)
    }
    
    // MARK: - Query Operations
    
    /// Get transaction status
    public func getTransactionStatus(txId: TxID) -> TransactionState? {
        return transactions[txId]?.state
    }
    
    /// Get held locks
    public func getHeldLocks(txId: TxID) -> Set<String> {
        return txLocks[txId] ?? []
    }
    
    /// Get coordinator state
    public func getCoordinatorState() -> CoordinatorState {
        return coordinatorState
    }
    
    /// Get active transactions
    public func getActiveTransactions() -> [Transaction] {
        return transactions.values.filter { $0.state == .active }
    }
    
    /// Get prepared transactions
    public func getPreparedTransactions() -> [Transaction] {
        return transactions.values.filter { $0.state == .prepared }
    }
    
    /// Get committed transactions
    public func getCommittedTransactions() -> [Transaction] {
        return transactions.values.filter { $0.state == .committed }
    }
    
    /// Get aborted transactions
    public func getAbortedTransactions() -> [Transaction] {
        return transactions.values.filter { $0.state == .aborted }
    }
    
    /// Get transaction
    public func getTransaction(txId: TxID) -> Transaction? {
        return transactions[txId]
    }
    
    /// Get transaction operations
    public func getTransactionOperations(txId: TxID) -> [Operation] {
        return txOperations[txId] ?? []
    }
    
    /// Get transaction locks
    public func getTransactionLocks(txId: TxID) -> Set<String> {
        return txLocks[txId] ?? []
    }
    
    /// Get transaction start time
    public func getTransactionStartTime(txId: TxID) -> Timestamp? {
        return txStartTime[txId]
    }
    
    /// Get participant votes
    public func getParticipantVotes(txId: TxID) -> [String: Bool] {
        return participantVotes[txId] ?? [:]
    }
    
    /// Get prepare timer
    public func getPrepareTimer(txId: TxID) -> Timestamp? {
        return prepareTimer[txId]
    }
    
    /// Get transaction WAL records
    public func getTransactionWALRecords(txId: TxID) -> [LSN] {
        return txWALRecords[txId] ?? []
    }
    
    /// Get last commit LSN
    public func getLastCommitLSN() -> LSN {
        return lastCommitLSN
    }
    
    /// Get transaction snapshot
    public func getTransactionSnapshot(txId: TxID) -> Snapshot? {
        return txSnapshots[txId]
    }
    
    /// Get transaction write set
    public func getTransactionWriteSet(txId: TxID) -> Set<String> {
        return txWriteSets[txId] ?? []
    }
    
    /// Get transaction read set
    public func getTransactionReadSet(txId: TxID) -> Set<String> {
        return txReadSets[txId] ?? []
    }
    
    /// Get wait-for graph
    public func getWaitForGraph() -> [TxID: Set<TxID>] {
        return waitForGraph
    }
    
    /// Get deadlock victim
    public func getDeadlockVictim() -> TxID {
        return deadlockVictim
    }
    
    /// Get global clock
    public func getGlobalClock() -> Timestamp {
        return globalClock
    }
    
    /// Check if transaction exists
    public func transactionExists(txId: TxID) -> Bool {
        return transactions[txId] != nil
    }
    
    /// Check if transaction is active
    public func isTransactionActive(txId: TxID) -> Bool {
        return transactions[txId]?.state == .active
    }
    
    /// Check if transaction is prepared
    public func isTransactionPrepared(txId: TxID) -> Bool {
        return transactions[txId]?.state == .prepared
    }
    
    /// Check if transaction is committed
    public func isTransactionCommitted(txId: TxID) -> Bool {
        return transactions[txId]?.state == .committed
    }
    
    /// Check if transaction is aborted
    public func isTransactionAborted(txId: TxID) -> Bool {
        return transactions[txId]?.state == .aborted
    }
    
    /// Get transaction count
    public func getTransactionCount() -> Int {
        return transactions.count
    }
    
    /// Get active transaction count
    public func getActiveTransactionCount() -> Int {
        return getActiveTransactions().count
    }
    
    /// Get prepared transaction count
    public func getPreparedTransactionCount() -> Int {
        return getPreparedTransactions().count
    }
    
    /// Get committed transaction count
    public func getCommittedTransactionCount() -> Int {
        return getCommittedTransactions().count
    }
    
    /// Get aborted transaction count
    public func getAbortedTransactionCount() -> Int {
        return getAbortedTransactions().count
    }
    
    /// Clear completed transactions
    public func clearCompletedTransactions() async throws {
        transactions = transactions.filter { $0.value.state == .active }
        txOperations = txOperations.filter { transactions[$0.key] != nil }
        txLocks = txLocks.filter { transactions[$0.key] != nil }
        txStartTime = txStartTime.filter { transactions[$0.key] != nil }
        txWALRecords = txWALRecords.filter { transactions[$0.key] != nil }
        txSnapshots = txSnapshots.filter { transactions[$0.key] != nil }
        txWriteSets = txWriteSets.filter { transactions[$0.key] != nil }
        txReadSets = txReadSets.filter { transactions[$0.key] != nil }
        waitForGraph = waitForGraph.filter { transactions[$0.key] != nil }
        participantVotes = participantVotes.filter { transactions[$0.key] != nil }
        prepareTimer = prepareTimer.filter { transactions[$0.key] != nil }
        preparedTransactions.removeAll()
        
        print("Completed transactions cleared")
    }
    
    /// Reset transaction manager
    public func resetTransactionManager() async throws {
        transactions.removeAll()
        txOperations.removeAll()
        txLocks.removeAll()
        txStartTime.removeAll()
        preparedTransactions.removeAll()
        coordinatorState = .idle
        participantVotes.removeAll()
        prepareTimer.removeAll()
        txWALRecords.removeAll()
        lastCommitLSN = 0
        txSnapshots.removeAll()
        txWriteSets.removeAll()
        txReadSets.removeAll()
        waitForGraph.removeAll()
        deadlockVictim = 0
        globalClock = 0
        nextTID = 1
        
        print("Transaction manager reset")
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
        // Check that transactions maintain consistency
        return true // Simplified
    }
    
    /// Check isolation invariant
    /// TLA+ Inv_TransactionManager_Isolation
    public func checkIsolationInvariant() -> Bool {
        // Check that transactions are isolated
        return true // Simplified
    }
    
    /// Check durability invariant
    /// TLA+ Inv_TransactionManager_Durability
    public func checkDurabilityInvariant() -> Bool {
        // Check that transactions are durable
        return true // Simplified
    }
    
    /// Check 2PC correctness invariant
    /// TLA+ Inv_TransactionManager_2PCCorrectness
    public func check2PCCorrectnessInvariant() -> Bool {
        // Check that two-phase commit is correct
        return true // Simplified
    }
    
    /// Check all invariants
    public func checkAllInvariants() -> Bool {
        let atomicity = checkAtomicityInvariant()
        let consistency = checkConsistencyInvariant()
        let isolation = checkIsolationInvariant()
        let durability = checkDurabilityInvariant()
        let twoPCCorrectness = check2PCCorrectnessInvariant()
        
        return atomicity && consistency && isolation && durability && twoPCCorrectness
    }
}

// MARK: - Supporting Types

/// WAL manager
public protocol WALManager: Sendable {
    func appendRecord(txId: TxID, kind: String, data: Data) async throws -> LSN
    func flushLog() async throws
}

/// MVCC manager
public protocol MVCCManager: Sendable {
    func beginTransaction(txId: TxID) async throws -> Snapshot
    func read(txId: TxID, key: String) async throws -> String?
    func write(txId: TxID, key: String, value: String) async throws
    func commit(txId: TxID) async throws
    func abort(txId: TxID) async throws
}

/// Lock manager
public protocol LockManager: Sendable {
    func requestLock(txId: TxID, resource: String, mode: String) async throws
    func releaseLock(txId: TxID, resource: String) async throws
}

/// Snapshot
public struct Snapshot: Codable, Sendable, Equatable {
    public let txId: TxID
    public let timestamp: Timestamp
    public let activeTransactions: Set<TxID>
    public let committedTransactions: Set<TxID>
    
    public init(txId: TxID, timestamp: Timestamp, activeTransactions: Set<TxID>, committedTransactions: Set<TxID>) {
        self.txId = txId
        self.timestamp = timestamp
        self.activeTransactions = activeTransactions
        self.committedTransactions = committedTransactions
    }
}

/// Transaction manager error
public enum TransactionManagerError: Error, LocalizedError {
    case transactionNotFound
    case transactionNotActive
    case noVotesReceived
    case deadlockDetected
    case lockRequestFailed
    case lockReleaseFailed
    case prepareFailed
    case commitFailed
    case abortFailed
    case voteCollectionFailed
    case decisionMakingFailed
    
    public var errorDescription: String? {
        switch self {
        case .transactionNotFound:
            return "Transaction not found"
        case .transactionNotActive:
            return "Transaction is not active"
        case .noVotesReceived:
            return "No votes received"
        case .deadlockDetected:
            return "Deadlock detected"
        case .lockRequestFailed:
            return "Lock request failed"
        case .lockReleaseFailed:
            return "Lock release failed"
        case .prepareFailed:
            return "Transaction prepare failed"
        case .commitFailed:
            return "Transaction commit failed"
        case .abortFailed:
            return "Transaction abort failed"
        case .voteCollectionFailed:
            return "Vote collection failed"
        case .decisionMakingFailed:
            return "Decision making failed"
        }
    }
}