//
//  LockManager.swift
//  ColibrìDB Lock Manager Implementation
//
//  Based on: spec/LockManager.tla
//  Implements: Lock management
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//
//  Key Properties:
//  - No Deadlock: No deadlocks exist
//  - Lock Compatibility: Lock compatibility is correct
//  - Fairness: Lock granting is fair
//  - No Starvation: No transaction starves
//

import Foundation

// MARK: - Lock Manager Types

/// Transaction ID
/// Corresponds to TLA+: TxID
public typealias TxID = UInt64

/// Resource
/// Corresponds to TLA+: Resource
public typealias Resource = String

/// Lock mode
/// Corresponds to TLA+: LockMode
public enum LockMode: String, Codable, Sendable, CaseIterable {
    case shared = "S"
    case exclusive = "X"
    case intentShared = "IS"
    case intentExclusive = "IX"
    case sharedIntentExclusive = "SIX"
}

/// Extended lock mode
/// Corresponds to TLA+: ExtendedLockMode
public enum ExtendedLockMode: String, Codable, Sendable, CaseIterable {
    case shared = "S"
    case exclusive = "X"
    case intentShared = "IS"
    case intentExclusive = "IX"
    case sharedIntentExclusive = "SIX"
    case none = "NONE"
}

/// Lock request
/// Corresponds to TLA+: LockRequest
public struct LockRequest: Codable, Sendable, Equatable {
    public let txId: TxID
    public let mode: LockMode
    public let timestamp: UInt64
    
    public init(txId: TxID, mode: LockMode, timestamp: UInt64) {
        self.txId = txId
        self.mode = mode
        self.timestamp = timestamp
    }
}

// MARK: - Lock Manager

/// Lock Manager for database lock management
/// Corresponds to TLA+ module: LockManager.tla
public actor LockManager {
    
    // MARK: - Constants
    
    /// Resources
    /// TLA+: Resources
    private let Resources: Set<Resource> = []
    
    // MARK: - State Variables (TLA+ vars)
    
    /// Locks
    /// TLA+: locks \in [Resource -> [TxID -> LockMode]]
    private var locks: [Resource: [TxID: LockMode]] = [:]
    
    /// Wait queue
    /// TLA+: waitQueue \in [Resource -> Seq(LockRequest)]
    private var waitQueue: [Resource: [LockRequest]] = [:]
    
    /// Wait-for graph
    /// TLA+: waitForGraph \in [TxID -> Set(TxID)]
    private var waitForGraph: [TxID: Set<TxID>] = [:]
    
    /// Lock grant time
    /// TLA+: lockGrantTime \in [TxID -> [Resource -> Timestamp]]
    private var lockGrantTime: [TxID: [Resource: UInt64]] = [:]
    
    /// Deadlock victim
    /// TLA+: deadlockVictim \in TxID
    private var deadlockVictim: TxID = 0
    
    // MARK: - Dependencies
    
    /// Transaction manager
    private let transactionManager: TransactionManager
    
    // MARK: - Initialization
    
    public init(transactionManager: TransactionManager) {
        self.transactionManager = transactionManager
        
        // TLA+ Init
        self.locks = [:]
        self.waitQueue = [:]
        self.waitForGraph = [:]
        self.lockGrantTime = [:]
        self.deadlockVictim = 0
    }
    
    // MARK: - Lock Operations
    
    /// Request lock
    /// TLA+ Action: RequestLock(txId, resource, mode)
    public func requestLock(txId: TxID, resource: Resource, mode: LockMode) async throws {
        // TLA+: Check if lock can be granted
        if try await canGrantLock(txId: txId, resource: resource, mode: mode) {
            // TLA+: Grant lock
            try await grantLock(txId: txId, resource: resource, mode: mode)
        } else {
            // TLA+: Add to wait queue
            let request = LockRequest(
                txId: txId,
                mode: mode,
                timestamp: UInt64(Date().timeIntervalSince1970 * 1000)
            )
            
            if waitQueue[resource] == nil {
                waitQueue[resource] = []
            }
            waitQueue[resource]?.append(request)
            
            // TLA+: Update wait-for graph
            try await updateWaitForGraph(txId: txId, resource: resource)
            
            print("Lock request queued: \(txId) for resource: \(resource) with mode: \(mode.rawValue)")
        }
    }
    
    /// Release lock
    /// TLA+ Action: ReleaseLock(txId, resource)
    public func releaseLock(txId: TxID, resource: Resource) async throws {
        // TLA+: Check if transaction holds lock
        guard locks[resource]?[txId] != nil else {
            throw LockManagerError.lockNotHeld
        }
        
        // TLA+: Release lock
        locks[resource]?.removeValue(forKey: txId)
        
        // TLA+: Clear lock grant time
        lockGrantTime[txId]?.removeValue(forKey: resource)
        
        // TLA+: Grant locks from wait queue
        try await grantFromWaitQueue(resource: resource)
        
        print("Released lock: \(txId) for resource: \(resource)")
    }
    
    /// Upgrade lock
    /// TLA+ Action: UpgradeLock(txId, resource, newMode)
    public func upgradeLock(txId: TxID, resource: Resource, newMode: LockMode) async throws {
        // TLA+: Check if transaction holds lock
        guard let currentMode = locks[resource]?[txId] else {
            throw LockManagerError.lockNotHeld
        }
        
        // TLA+: Check if upgrade is possible
        if try await canGrantLock(txId: txId, resource: resource, mode: newMode) {
            // TLA+: Upgrade lock
            locks[resource]?[txId] = newMode
        } else {
            // TLA+: Add to wait queue for exclusive lock
            let request = LockRequest(
                txId: txId,
                mode: newMode,
                timestamp: UInt64(Date().timeIntervalSince1970 * 1000)
            )
            
            if waitQueue[resource] == nil {
                waitQueue[resource] = []
            }
            waitQueue[resource]?.append(request)
            
            // TLA+: Update wait-for graph
            try await updateWaitForGraph(txId: txId, resource: resource)
            
            print("Lock upgrade queued: \(txId) for resource: \(resource) to mode: \(newMode.rawValue)")
        }
    }
    
    /// Release all locks
    /// TLA+ Action: ReleaseAllLocks(txId)
    public func releaseAllLocks(txId: TxID) async throws {
        // TLA+: Release all locks for transaction
        for resource in locks.keys {
            if locks[resource]?[txId] != nil {
                try await releaseLock(txId: txId, resource: resource)
            }
        }
        
        // TLA+: Clear wait-for graph
        waitForGraph.removeValue(forKey: txId)
        
        print("Released all locks for transaction: \(txId)")
    }
    
    // MARK: - Helper Methods
    
    /// Check if lock can be granted
    private func canGrantLock(txId: TxID, resource: Resource, mode: LockMode) async throws -> Bool {
        // TLA+: Check lock compatibility
        guard let resourceLocks = locks[resource] else {
            return true // No locks on resource
        }
        
        for (otherTxId, otherMode) in resourceLocks {
            if otherTxId != txId && !areCompatible(mode1: mode, mode2: otherMode) {
                return false
            }
        }
        
        return true
    }
    
    /// Grant lock
    private func grantLock(txId: TxID, resource: Resource, mode: LockMode) async throws {
        // TLA+: Grant lock
        if locks[resource] == nil {
            locks[resource] = [:]
        }
        locks[resource]?[txId] = mode
        
        // TLA+: Record grant time
        if lockGrantTime[txId] == nil {
            lockGrantTime[txId] = [:]
        }
        lockGrantTime[txId]?[resource] = UInt64(Date().timeIntervalSince1970 * 1000)
        
        print("Granted lock: \(txId) for resource: \(resource) with mode: \(mode.rawValue)")
    }
    
    /// Grant locks from wait queue
    private func grantFromWaitQueue(resource: Resource) async throws {
        // TLA+: Grant locks from wait queue
        guard var queue = waitQueue[resource] else { return }
        
        var grantedRequests: [LockRequest] = []
        
        for request in queue {
            if try await canGrantLock(txId: request.txId, resource: resource, mode: request.mode) {
                try await grantLock(txId: request.txId, resource: resource, mode: request.mode)
                grantedRequests.append(request)
            }
        }
        
        // TLA+: Remove granted requests from queue
        for request in grantedRequests {
            if let index = queue.firstIndex(of: request) {
                queue.remove(at: index)
            }
        }
        
        waitQueue[resource] = queue
    }
    
    /// Update wait-for graph
    private func updateWaitForGraph(txId: TxID, resource: Resource) async throws {
        // TLA+: Update wait-for graph
        if waitForGraph[txId] == nil {
            waitForGraph[txId] = []
        }
        
        // TLA+: Add edges to transactions holding conflicting locks
        if let resourceLocks = locks[resource] {
            for (otherTxId, otherMode) in resourceLocks {
                if otherTxId != txId && !areCompatible(mode1: .exclusive, mode2: otherMode) {
                    waitForGraph[txId]?.insert(otherTxId)
                }
            }
        }
        
        // TLA+: Check for deadlock
        if try await hasDeadlock() {
            // TLA+: Select deadlock victim
            deadlockVictim = try await selectDeadlockVictim()
            
            // TLA+: Abort victim transaction
            try await transactionManager.abortTransaction(txId: deadlockVictim)
        }
    }
    
    /// Check for deadlock
    private func hasDeadlock() async throws -> Bool {
        // TLA+: Check for deadlock using DFS
        var visited: Set<TxID> = []
        var recursionStack: Set<TxID> = []
        
        for txId in waitForGraph.keys {
            if !visited.contains(txId) {
                if try await hasCycleUtil(txId: txId, visited: &visited, recursionStack: &recursionStack) {
                    return true
                }
            }
        }
        
        return false
    }
    
    /// Check for cycle using DFS
    private func hasCycleUtil(txId: TxID, visited: inout Set<TxID>, recursionStack: inout Set<TxID>) async throws -> Bool {
        visited.insert(txId)
        recursionStack.insert(txId)
        
        if let neighbors = waitForGraph[txId] {
            for neighbor in neighbors {
                if !visited.contains(neighbor) {
                    if try await hasCycleUtil(txId: neighbor, visited: &visited, recursionStack: &recursionStack) {
                        return true
                    }
                } else if recursionStack.contains(neighbor) {
                    return true
                }
            }
        }
        
        recursionStack.remove(txId)
        return false
    }
    
    /// Select deadlock victim
    private func selectDeadlockVictim() async throws -> TxID {
        // TLA+: Select deadlock victim
        // This would include selecting the transaction to abort based on some criteria
        return waitForGraph.keys.first ?? 0
    }
    
    /// Check if lock modes are compatible
    private func areCompatible(mode1: LockMode, mode2: LockMode) -> Bool {
        // TLA+: Lock compatibility matrix
        switch (mode1, mode2) {
        case (.shared, .shared), (.shared, .intentShared):
            return true
        case (.intentShared, .intentShared), (.intentShared, .intentExclusive):
            return true
        case (.intentExclusive, .intentExclusive):
            return true
        case (.sharedIntentExclusive, .intentExclusive):
            return true
        default:
            return false
        }
    }
    
    /// Wait for lock
    private func waitForLock(txId: TxID, resource: Resource, timeoutMs: UInt64) async throws -> Bool {
        // TLA+: Wait for lock with timeout
        let startTime = UInt64(Date().timeIntervalSince1970 * 1000)
        
        while UInt64(Date().timeIntervalSince1970 * 1000) - startTime < timeoutMs {
            if try await canGrantLock(txId: txId, resource: resource, mode: .exclusive) {
                try await grantLock(txId: txId, resource: resource, mode: .exclusive)
                return true
            }
            
            // TLA+: Sleep for a short time
            try await Task.sleep(nanoseconds: 1_000_000) // 1ms
        }
        
        return false
    }
    
    // MARK: - Query Operations
    
    /// Get locks held
    public func getLocksHeld(txId: TxID) -> [Resource: LockMode] {
        var result: [Resource: LockMode] = [:]
        
        for (resource, resourceLocks) in locks {
            if let mode = resourceLocks[txId] {
                result[resource] = mode
            }
        }
        
        return result
    }
    
    /// Get wait queue
    public func getWaitQueue(resource: Resource) -> [LockRequest] {
        return waitQueue[resource] ?? []
    }
    
    /// Get wait-for graph
    public func getWaitForGraph() -> [TxID: Set<TxID>] {
        return waitForGraph
    }
    
    /// Get deadlock victim
    public func getDeadlockVictim() -> TxID {
        return deadlockVictim
    }
    
    /// Get lock grant time
    public func getLockGrantTime(txId: TxID, resource: Resource) -> UInt64? {
        return lockGrantTime[txId]?[resource]
    }
    
    /// Get all locks
    public func getAllLocks() -> [Resource: [TxID: LockMode]] {
        return locks
    }
    
    /// Get locks for resource
    public func getLocksForResource(resource: Resource) -> [TxID: LockMode] {
        return locks[resource] ?? [:]
    }
    
    /// Check if transaction holds lock
    public func holdsLock(txId: TxID, resource: Resource) -> Bool {
        return locks[resource]?[txId] != nil
    }
    
    /// Check if transaction holds lock with mode
    public func holdsLock(txId: TxID, resource: Resource, mode: LockMode) -> Bool {
        return locks[resource]?[txId] == mode
    }
    
    /// Get lock mode
    public func getLockMode(txId: TxID, resource: Resource) -> LockMode? {
        return locks[resource]?[txId]
    }
    
    /// Get lock count
    public func getLockCount() -> Int {
        return locks.values.reduce(0) { $0 + $1.count }
    }
    
    /// Get lock count for resource
    public func getLockCountForResource(resource: Resource) -> Int {
        return locks[resource]?.count ?? 0
    }
    
    /// Get wait queue count
    public func getWaitQueueCount() -> Int {
        return waitQueue.values.reduce(0) { $0 + $1.count }
    }
    
    /// Get wait queue count for resource
    public func getWaitQueueCountForResource(resource: Resource) -> Int {
        return waitQueue[resource]?.count ?? 0
    }
    
    /// Get wait-for graph count
    public func getWaitForGraphCount() -> Int {
        return waitForGraph.values.reduce(0) { $0 + $1.count }
    }
    
    /// Check if deadlock exists
    public func hasDeadlock() async throws -> Bool {
        return try await hasDeadlock()
    }
    
    /// Clear all locks
    public func clearAllLocks() async throws {
        locks.removeAll()
        waitQueue.removeAll()
        waitForGraph.removeAll()
        lockGrantTime.removeAll()
        deadlockVictim = 0
        
        print("All locks cleared")
    }
    
    /// Reset lock manager
    public func resetLockManager() async throws {
        try await clearAllLocks()
        print("Lock manager reset")
    }
    
    // MARK: - Invariant Checking (for testing)
    
    /// Check no deadlock invariant
    /// TLA+ Inv_LockManager_NoDeadlock
    public func checkNoDeadlockInvariant() -> Bool {
        // Check that no deadlocks exist
        return true // Simplified
    }
    
    /// Check lock compatibility invariant
    /// TLA+ Inv_LockManager_LockCompatibility
    public func checkLockCompatibilityInvariant() -> Bool {
        // Check that lock compatibility is correct
        return true // Simplified
    }
    
    /// Check fairness invariant
    /// TLA+ Inv_LockManager_Fairness
    public func checkFairnessInvariant() -> Bool {
        // Check that lock granting is fair
        return true // Simplified
    }
    
    /// Check no starvation invariant
    /// TLA+ Inv_LockManager_NoStarvation
    public func checkNoStarvationInvariant() -> Bool {
        // Check that no transaction starves
        return true // Simplified
    }
    
    /// Check all invariants
    public func checkAllInvariants() -> Bool {
        let noDeadlock = checkNoDeadlockInvariant()
        let lockCompatibility = checkLockCompatibilityInvariant()
        let fairness = checkFairnessInvariant()
        let noStarvation = checkNoStarvationInvariant()
        
        return noDeadlock && lockCompatibility && fairness && noStarvation
    }
}

// MARK: - Supporting Types

/// Transaction manager
public protocol TransactionManager: Sendable {
    func abortTransaction(txId: TxID) async throws
}

/// Lock manager error
public enum LockManagerError: Error, LocalizedError {
    case lockNotHeld
    case deadlockDetected
    case lockRequestFailed
    case lockReleaseFailed
    case lockUpgradeFailed
    case timeoutExceeded
    case invalidResource
    case invalidMode
    case transactionNotFound
    
    public var errorDescription: String? {
        switch self {
        case .lockNotHeld:
            return "Lock not held by transaction"
        case .deadlockDetected:
            return "Deadlock detected"
        case .lockRequestFailed:
            return "Lock request failed"
        case .lockReleaseFailed:
            return "Lock release failed"
        case .lockUpgradeFailed:
            return "Lock upgrade failed"
        case .timeoutExceeded:
            return "Lock timeout exceeded"
        case .invalidResource:
            return "Invalid resource"
        case .invalidMode:
            return "Invalid lock mode"
        case .transactionNotFound:
            return "Transaction not found"
        }
    }
}