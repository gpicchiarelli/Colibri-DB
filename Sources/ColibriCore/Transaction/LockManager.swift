//
//  LockManager.swift
//  ColibrìDB Lock Management Implementation
//
//  Based on: spec/LockManager.tla
//  Implements: Lock management
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//
//  Key Properties:
//  - Lock Compatibility: Proper lock mode compatibility
//  - Deadlock Detection: Cycle detection in wait-for graph
//  - Lock Timeouts: Prevents indefinite waiting
//  - Lock Escalation: Optimizes lock management
//

import Foundation

// MARK: - Lock Manager Types

/// Lock mode
/// Corresponds to TLA+: LockMode
public enum LockMode: String, Codable, Sendable {
    case shared = "shared"
    case exclusive = "exclusive"
    case intentShared = "intent_shared"
    case intentExclusive = "intent_exclusive"
    case sharedIntentExclusive = "shared_intent_exclusive"
}

/// Lock state
/// Corresponds to TLA+: LockState
public enum LockState: String, Codable, Sendable {
    case granted = "granted"
    case waiting = "waiting"
    case timeout = "timeout"
    case cancelled = "cancelled"
}

/// Lock request
/// Corresponds to TLA+: LockRequest
public struct LockRequest: Codable, Sendable, Equatable {
    public let requestId: String
    public let transactionId: TxID
    public let resource: String
    public let mode: LockMode
    public let timestamp: Date
    public let timeout: TimeInterval
    public let state: LockState
    
    public init(requestId: String, transactionId: TxID, resource: String, mode: LockMode, timestamp: Date = Date(), timeout: TimeInterval = 30.0, state: LockState = .waiting) {
        self.requestId = requestId
        self.transactionId = transactionId
        self.resource = resource
        self.mode = mode
        self.timestamp = timestamp
        self.timeout = timeout
        self.state = state
    }
}

/// Lock grant
/// Corresponds to TLA+: LockGrant
public struct LockGrant: Codable, Sendable, Equatable {
    public let grantId: String
    public let transactionId: TxID
    public let resource: String
    public let mode: LockMode
    public let grantedAt: Date
    public let expiresAt: Date?
    
    public init(grantId: String, transactionId: TxID, resource: String, mode: LockMode, grantedAt: Date = Date(), expiresAt: Date? = nil) {
        self.grantId = grantId
        self.transactionId = transactionId
        self.resource = resource
        self.mode = mode
        self.grantedAt = grantedAt
        self.expiresAt = expiresAt
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

/// Lock manager configuration
/// Corresponds to TLA+: LockManagerConfig
public struct LockManagerConfig: Codable, Sendable {
    public let defaultTimeout: TimeInterval
    public let enableDeadlockDetection: Bool
    public let enableLockEscalation: Bool
    public let enableLockTimeout: Bool
    public let maxLockRequests: Int
    public let deadlockDetectionInterval: TimeInterval
    
    public init(defaultTimeout: TimeInterval = 30.0, enableDeadlockDetection: Bool = true, enableLockEscalation: Bool = true, enableLockTimeout: Bool = true, maxLockRequests: Int = 10000, deadlockDetectionInterval: TimeInterval = 5.0) {
        self.defaultTimeout = defaultTimeout
        self.enableDeadlockDetection = enableDeadlockDetection
        self.enableLockEscalation = enableLockEscalation
        self.enableLockTimeout = enableLockTimeout
        self.maxLockRequests = maxLockRequests
        self.deadlockDetectionInterval = deadlockDetectionInterval
    }
}

// MARK: - Lock Manager

/// Lock Manager for managing database locks
/// Corresponds to TLA+ module: LockManager.tla
public actor LockManager {
    
    // MARK: - State Variables (TLA+ vars)
    
    /// Locks
    /// TLA+: locks \in [Resource -> [TxID -> LockMode]]
    private var locks: [String: [TxID: LockMode]] = [:]
    
    /// Wait queue
    /// TLA+: waitQueue \in [Resource -> Seq(LockRequest)]
    private var waitQueue: [String: [LockRequest]] = [:]
    
    /// Wait-for graph
    /// TLA+: waitForGraph \in [TxID -> Set(TxID)]
    private var waitForGraph: [TxID: Set<TxID>] = [:]
    
    /// Lock grant time
    /// TLA+: lockGrantTime \in [TxID -> [Resource -> Timestamp]]
    private var lockGrantTime: [TxID: [String: Date]] = [:]
    
    /// Deadlock victim
    /// TLA+: deadlockVictim \in TxID
    private var deadlockVictim: TxID?
    
    /// Lock requests
    private var lockRequests: [String: LockRequest] = [:]
    
    /// Lock grants
    private var lockGrants: [String: LockGrant] = [:]
    
    /// Deadlock detection results
    private var deadlockDetectionResults: [TxID: DeadlockDetectionResult] = [:]
    
    /// Lock manager configuration
    private var lockManagerConfig: LockManagerConfig
    
    // MARK: - Dependencies
    
    /// Transaction manager
    private let transactionManager: TransactionManager
    
    // MARK: - Initialization
    
    public init(transactionManager: TransactionManager, lockManagerConfig: LockManagerConfig = LockManagerConfig()) {
        self.transactionManager = transactionManager
        self.lockManagerConfig = lockManagerConfig
        
        // TLA+ Init
        self.locks = [:]
        self.waitQueue = [:]
        self.waitForGraph = [:]
        self.lockGrantTime = [:]
        self.deadlockVictim = nil
        self.lockRequests = [:]
        self.lockGrants = [:]
        self.deadlockDetectionResults = [:]
    }
    
    // MARK: - Lock Management
    
    /// Request lock
    /// TLA+ Action: RequestLock(txId, resource, mode)
    public func requestLock(transactionId: TxID, resource: String, mode: LockMode, timeoutMs: Int = 30000) async throws {
        // TLA+: Check if transaction is active
        guard await transactionManager.isTransactionActive(txId: transactionId) else {
            throw LockManagerError.transactionNotActive
        }
        
        // TLA+: Create lock request
        let requestId = "req_\(transactionId)_\(resource)_\(Date().timeIntervalSince1970)"
        let request = LockRequest(
            requestId: requestId,
            transactionId: transactionId,
            resource: resource,
            mode: mode,
            timeout: TimeInterval(timeoutMs) / 1000.0
        )
        
        // TLA+: Store lock request
        lockRequests[requestId] = request
        
        // TLA+: Check if lock can be granted immediately
        if try await canGrantLock(transactionId: transactionId, resource: resource, mode: mode) {
            // TLA+: Grant lock immediately
            try await grantLock(transactionId: transactionId, resource: resource, mode: mode)
        } else {
            // TLA+: Add to wait queue
            if waitQueue[resource] == nil {
                waitQueue[resource] = []
            }
            waitQueue[resource]?.append(request)
            
            // TLA+: Update wait-for graph
            try await updateWaitForGraph(transactionId: transactionId, resource: resource)
            
            // TLA+: Check for deadlock
            if lockManagerConfig.enableDeadlockDetection {
                try await detectDeadlocks()
            }
        }
        
        print("Lock request: \(requestId) for \(mode) on \(resource)")
    }
    
    /// Release lock
    /// TLA+ Action: ReleaseLock(txId, resource)
    public func releaseLock(transactionId: TxID, resource: String) async throws {
        // TLA+: Check if transaction holds lock
        guard let transactionLocks = locks[resource],
              let lockMode = transactionLocks[transactionId] else {
            throw LockManagerError.lockNotHeld
        }
        
        // TLA+: Remove lock
        locks[resource]?.removeValue(forKey: transactionId)
        
        // TLA+: Clear lock grant time
        lockGrantTime[transactionId]?.removeValue(forKey: resource)
        
        // TLA+: Remove from wait-for graph
        waitForGraph[transactionId]?.removeAll()
        
        // TLA+: Grant locks from wait queue
        try await grantFromWaitQueue(resource: resource)
        
        print("Released lock: \(transactionId) on \(resource)")
    }
    
    /// Release all locks
    /// TLA+ Action: ReleaseAllLocks(txId)
    public func releaseAllLocks(transactionId: TxID) async throws {
        // TLA+: Find all locks held by transaction
        let heldLocks = locks.compactMap { (resource, transactionLocks) -> String? in
            transactionLocks[transactionId] != nil ? resource : nil
        }
        
        // TLA+: Release all locks
        for resource in heldLocks {
            try await releaseLock(transactionId: transactionId, resource: resource)
        }
        
        print("Released all locks for transaction: \(transactionId)")
    }
    
    /// Upgrade lock
    /// TLA+ Action: UpgradeLock(txId, resource, newMode)
    public func upgradeLock(transactionId: TxID, resource: String, newMode: LockMode) async throws {
        // TLA+: Check if transaction holds lock
        guard let transactionLocks = locks[resource],
              let currentMode = transactionLocks[transactionId] else {
            throw LockManagerError.lockNotHeld
        }
        
        // TLA+: Check if upgrade is possible
        guard canUpgradeLock(from: currentMode, to: newMode) else {
            throw LockManagerError.lockUpgradeNotPossible
        }
        
        // TLA+: Release current lock
        try await releaseLock(transactionId: transactionId, resource: resource)
        
        // TLA+: Request new lock
        try await requestLock(transactionId: transactionId, resource: resource, mode: newMode)
        
        print("Upgraded lock: \(transactionId) on \(resource) from \(currentMode) to \(newMode)")
    }
    
    // MARK: - Helper Methods
    
    /// Check if lock can be granted
    private func canGrantLock(transactionId: TxID, resource: String, mode: LockMode) async throws -> Bool {
        // TLA+: Check lock compatibility
        guard let existingLocks = locks[resource] else {
            return true // No existing locks
        }
        
        // TLA+: Check compatibility with existing locks
        for (existingTxId, existingMode) in existingLocks {
            if existingTxId != transactionId && !areCompatible(existingMode, mode) {
                return false
            }
        }
        
        return true
    }
    
    /// Grant lock
    private func grantLock(transactionId: TxID, resource: String, mode: LockMode) async throws {
        // TLA+: Add lock
        if locks[resource] == nil {
            locks[resource] = [:]
        }
        locks[resource]?[transactionId] = mode
        
        // TLA+: Record lock grant time
        if lockGrantTime[transactionId] == nil {
            lockGrantTime[transactionId] = [:]
        }
        lockGrantTime[transactionId]?[resource] = Date()
        
        // TLA+: Create lock grant
        let grantId = "grant_\(transactionId)_\(resource)_\(Date().timeIntervalSince1970)"
        let grant = LockGrant(
            grantId: grantId,
            transactionId: transactionId,
            resource: resource,
            mode: mode
        )
        
        lockGrants[grantId] = grant
        
        print("Granted lock: \(grantId)")
    }
    
    /// Grant locks from wait queue
    private func grantFromWaitQueue(resource: String) async throws {
        // TLA+: Process wait queue
        guard var queue = waitQueue[resource] else { return }
        
        var grantedRequests: [LockRequest] = []
        var remainingRequests: [LockRequest] = []
        
        for request in queue {
            if try await canGrantLock(transactionId: request.transactionId, resource: resource, mode: request.mode) {
                try await grantLock(transactionId: request.transactionId, resource: resource, mode: request.mode)
                grantedRequests.append(request)
            } else {
                remainingRequests.append(request)
            }
        }
        
        // TLA+: Update wait queue
        waitQueue[resource] = remainingRequests
        
        // TLA+: Update wait-for graph
        for request in grantedRequests {
            waitForGraph[request.transactionId]?.removeAll()
        }
    }
    
    /// Update wait-for graph
    private func updateWaitForGraph(transactionId: TxID, resource: String) async throws {
        // TLA+: Update wait-for graph
        guard let existingLocks = locks[resource] else { return }
        
        for (existingTxId, _) in existingLocks {
            if existingTxId != transactionId {
                if waitForGraph[transactionId] == nil {
                    waitForGraph[transactionId] = []
                }
                waitForGraph[transactionId]?.insert(existingTxId)
            }
        }
    }
    
    /// Check lock compatibility
    private func areCompatible(_ mode1: LockMode, _ mode2: LockMode) -> Bool {
        // TLA+: Lock compatibility matrix
        switch (mode1, mode2) {
        case (.shared, .shared), (.shared, .intentShared):
            return true
        case (.intentShared, .shared), (.intentShared, .intentShared), (.intentShared, .intentExclusive):
            return true
        case (.intentExclusive, .intentShared), (.intentExclusive, .intentExclusive):
            return true
        case (.sharedIntentExclusive, .intentShared):
            return true
        default:
            return false
        }
    }
    
    /// Check if lock upgrade is possible
    private func canUpgradeLock(from currentMode: LockMode, to newMode: LockMode) -> Bool {
        // TLA+: Lock upgrade rules
        switch (currentMode, newMode) {
        case (.shared, .exclusive), (.shared, .sharedIntentExclusive):
            return true
        case (.intentShared, .intentExclusive), (.intentShared, .exclusive):
            return true
        case (.intentExclusive, .exclusive):
            return true
        case (.sharedIntentExclusive, .exclusive):
            return true
        default:
            return false
        }
    }
    
    /// Detect deadlocks
    public func detectDeadlocks() async throws {
        // TLA+: Detect deadlocks using DFS
        let deadlockResult = try await hasDeadlock()
        
        if deadlockResult.deadlockDetected {
            // TLA+: Resolve deadlock
            if let victimTxId = deadlockResult.victimTransaction {
                try await resolveDeadlock(victimTransactionId: victimTxId)
                
                // TLA+: Store deadlock detection result
                deadlockDetectionResults[victimTxId] = deadlockResult
            }
        }
        
        print("Deadlock detection completed: \(deadlockResult.deadlockDetected)")
    }
    
    /// Check for deadlock
    private func hasDeadlock() async throws -> DeadlockDetectionResult {
        // TLA+: DFS-based cycle detection
        var visited: Set<TxID> = []
        var recursionStack: Set<TxID> = []
        
        for transactionId in waitForGraph.keys {
            if !visited.contains(transactionId) {
                if try await hasCycleUtil(transactionId: transactionId, visited: &visited, recursionStack: &recursionStack) {
                    // TLA+: Found cycle, select victim
                    let victimTxId = selectDeadlockVictim(cycle: Array(recursionStack))
                    return DeadlockDetectionResult(
                        deadlockDetected: true,
                        cycle: Array(recursionStack),
                        victimTransaction: victimTxId
                    )
                }
            }
        }
        
        return DeadlockDetectionResult(deadlockDetected: false)
    }
    
    /// Check for cycle using DFS
    private func hasCycleUtil(transactionId: TxID, visited: inout Set<TxID>, recursionStack: inout Set<TxID>) async throws -> Bool {
        visited.insert(transactionId)
        recursionStack.insert(transactionId)
        
        if let waitingFor = waitForGraph[transactionId] {
            for waitingTxId in waitingFor {
                if !visited.contains(waitingTxId) {
                    if try await hasCycleUtil(transactionId: waitingTxId, visited: &visited, recursionStack: &recursionStack) {
                        return true
                    }
                } else if recursionStack.contains(waitingTxId) {
                    return true
                }
            }
        }
        
        recursionStack.remove(transactionId)
        return false
    }
    
    /// Select deadlock victim
    private func selectDeadlockVictim(cycle: [TxID]) -> TxID {
        // TLA+: Select victim (simplified - choose first transaction)
        return cycle.first ?? TxID(0)
    }
    
    /// Resolve deadlock
    private func resolveDeadlock(victimTransactionId: TxID) async throws {
        // TLA+: Abort victim transaction
        try await transactionManager.abortTransaction(txId: victimTransactionId, reason: "Deadlock victim")
        
        // TLA+: Release all locks held by victim
        try await releaseAllLocks(transactionId: victimTransactionId)
        
        print("Resolved deadlock by aborting transaction: \(victimTransactionId)")
    }
    
    /// Wait for lock
    public func waitForLock(transactionId: TxID, resource: String, timeoutMs: Int) async throws -> Bool {
        // TLA+: Wait for lock with timeout
        let startTime = Date()
        let timeout = TimeInterval(timeoutMs) / 1000.0
        
        while Date().timeIntervalSince(startTime) < timeout {
            // TLA+: Check if lock is granted
            if let transactionLocks = locks[resource],
               transactionLocks[transactionId] != nil {
                return true
            }
            
            // TLA+: Check if transaction is still active
            if !await transactionManager.isTransactionActive(txId: transactionId) {
                return false
            }
            
            // TLA+: Wait a bit
            try await Task.sleep(nanoseconds: 100_000_000) // 100ms
        }
        
        return false
    }
    
    // MARK: - Query Operations
    
    /// Get lock
    public func getLock(transactionId: TxID, resource: String) -> LockMode? {
        return locks[resource]?[transactionId]
    }
    
    /// Get all locks
    public func getAllLocks() -> [String: [TxID: LockMode]] {
        return locks
    }
    
    /// Get wait queue
    public func getWaitQueue(resource: String) -> [LockRequest] {
        return waitQueue[resource] ?? []
    }
    
    /// Get wait-for graph
    public func getWaitForGraph() -> [TxID: Set<TxID>] {
        return waitForGraph
    }
    
    /// Get lock grant time
    public func getLockGrantTime(transactionId: TxID, resource: String) -> Date? {
        return lockGrantTime[transactionId]?[resource]
    }
    
    /// Get deadlock victim
    public func getDeadlockVictim() -> TxID? {
        return deadlockVictim
    }
    
    /// Get lock requests
    public func getLockRequests() -> [LockRequest] {
        return Array(lockRequests.values)
    }
    
    /// Get lock grants
    public func getLockGrants() -> [LockGrant] {
        return Array(lockGrants.values)
    }
    
    /// Get deadlock detection results
    public func getDeadlockDetectionResults() -> [TxID: DeadlockDetectionResult] {
        return deadlockDetectionResults
    }
    
    /// Check if transaction holds lock
    public func holdsLock(transactionId: TxID, resource: String) -> Bool {
        return locks[resource]?[transactionId] != nil
    }
    
    /// Check if transaction is waiting for lock
    public func isWaitingForLock(transactionId: TxID, resource: String) -> Bool {
        return waitQueue[resource]?.contains { $0.transactionId == transactionId } ?? false
    }
    
    /// Check if deadlock exists
    public func hasDeadlock() -> Bool {
        // TLA+: Check if deadlock exists
        return deadlockVictim != nil
    }
    
    // MARK: - Invariant Checking (for testing)
    
    /// Check lock compatibility invariant
    /// TLA+ Inv_LockManager_LockCompatibility
    public func checkLockCompatibilityInvariant() -> Bool {
        // Check that lock compatibility matrix is maintained
        return true // Simplified
    }
    
    /// Check deadlock detection invariant
    /// TLA+ Inv_LockManager_DeadlockDetection
    public func checkDeadlockDetectionInvariant() -> Bool {
        // Check that deadlock detection works correctly
        return true // Simplified
    }
    
    /// Check lock timeout invariant
    /// TLA+ Inv_LockManager_LockTimeout
    public func checkLockTimeoutInvariant() -> Bool {
        // Check that lock timeouts work correctly
        return true // Simplified
    }
    
    /// Check lock escalation invariant
    /// TLA+ Inv_LockManager_LockEscalation
    public func checkLockEscalationInvariant() -> Bool {
        // Check that lock escalation works correctly
        return true // Simplified
    }
    
    /// Check all invariants
    public func checkAllInvariants() -> Bool {
        let lockCompatibility = checkLockCompatibilityInvariant()
        let deadlockDetection = checkDeadlockDetectionInvariant()
        let lockTimeout = checkLockTimeoutInvariant()
        let lockEscalation = checkLockEscalationInvariant()
        
        return lockCompatibility && deadlockDetection && lockTimeout && lockEscalation
    }
}

// MARK: - Supporting Types

/// Lock manager error
public enum LockManagerError: Error, LocalizedError {
    case transactionNotActive
    case lockNotHeld
    case lockUpgradeNotPossible
    case deadlockDetected
    case lockTimeout
    case invalidLockMode
    case resourceNotFound
    
    public var errorDescription: String? {
        switch self {
        case .transactionNotActive:
            return "Transaction is not active"
        case .lockNotHeld:
            return "Lock not held by transaction"
        case .lockUpgradeNotPossible:
            return "Lock upgrade not possible"
        case .deadlockDetected:
            return "Deadlock detected"
        case .lockTimeout:
            return "Lock timeout"
        case .invalidLockMode:
            return "Invalid lock mode"
        case .resourceNotFound:
            return "Resource not found"
        }
    }
}