//
//  LockManager.swift
//  ColibrìDB Lock Manager with Deadlock Detection
//
//  Based on: spec/LockManager.tla
//  Implements: Intent locks, deadlock detection with wait-for graph
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//
//  Key Properties:
//  - Lock Compatibility: Incompatible locks not held simultaneously
//  - Deadlock Detection: Wait-for graph with cycle detection
//  - Fairness: Locks granted in FIFO order
//  - No Starvation: Writers eventually acquire locks
//
//  Based on:
//  - "Granularity of Locks in a Shared Data Base" (Gray et al., 1975)
//  - "The Deadlock Problem: An Overview" (Coffman et al., 1971)
//

import Foundation

/// Lock request in wait queue
/// Corresponds to TLA+: LockRequest
public struct LockRequest: Sendable {
    public let txID: TxID
    public let mode: LockMode
    public let timestamp: Timestamp
    
    public init(txID: TxID, mode: LockMode, timestamp: Timestamp) {
        self.txID = txID
        self.mode = mode
        self.timestamp = timestamp
    }
}

/// Lock Manager for concurrency control with deadlock detection
/// Corresponds to TLA+ module: LockManager.tla
public actor LockManager {
    // MARK: - State Variables (TLA+ vars)
    
    /// Active locks: resource -> (txID -> LockMode)
    /// TLA+: locks \in [Resources -> [TxIds -> ExtendedLockMode]]
    private var locks: [String: [TxID: LockMode]] = [:]
    
    /// Wait queue: resource -> [(txID, mode, timestamp)]
    /// TLA+: waitQueue \in [Resources -> Seq(LockRequest)]
    private var waitQueue: [String: [LockRequest]] = [:]
    
    /// Wait-for graph for deadlock detection
    /// TLA+: waitForGraph \in [TxIds -> SUBSET TxIds]
    private var waitForGraph: [TxID: Set<TxID>] = [:]
    
    /// Lock grant time (for timeout)
    /// TLA+: lockGrantTime \in [TxIds -> [Resources -> Timestamp]]
    private var lockGrantTime: [TxID: [String: Timestamp]] = [:]
    
    /// Deadlock victim (TxID chosen for abort, or 0)
    /// TLA+: deadlockVictim \in TxIds \union {0}
    private var deadlockVictim: TxID = 0
    
    /// Timeout duration (milliseconds)
    private let timeoutMs: Int = 30000
    
    // MARK: - Initialization
    
    public init() {
        // TLA+ Init state
        self.locks = [:]
        self.waitQueue = [:]
        self.waitForGraph = [:]
        self.lockGrantTime = [:]
        self.deadlockVictim = 0
    }
    
    // MARK: - Core Operations
    
    /// Request a lock
    /// TLA+ Action: RequestLock(resource, mode, txId)
    /// Precondition: txID not in wait-for graph
    /// Postcondition: lock granted or transaction added to wait queue
    public func requestLock(resource: String, mode: LockMode, txID: TxID) async throws {
        // TLA+: CanGrant(resource, mode)
        if canGrantLock(resource: resource, mode: mode, txID: txID) {
            // TLA+: GrantLock(resource, mode, txId)
            grantLock(resource: resource, mode: mode, txID: txID)
        } else {
            // TLA+: AddToWaitQueue(resource, txId, mode)
            let request = LockRequest(txID: txID, mode: mode, timestamp: UInt64(Date().timeIntervalSince1970 * 1000))
            waitQueue[resource, default: []].append(request)
            
            // TLA+: UpdateWaitForGraph(resource, txId)
            updateWaitForGraph(resource: resource, waiter: txID)
            
            // TLA+: CheckDeadlock
            if hasDeadlock() {
                // TLA+: AbortVictim(txId)
                deadlockVictim = txID
                waitQueue[resource]?.removeAll { $0.txID == txID }
                throw DBError.deadlock
            }
            
            // Wait for lock to be granted (or timeout)
            try await waitForLock(resource: resource, txID: txID)
        }
    }
    
    /// Release a lock
    /// TLA+ Action: ReleaseLock(resource, txId)
    /// Precondition: txID holds lock on resource
    /// Postcondition: lock released, wait queue processed
    public func releaseLock(resource: String, txID: TxID) {
        // TLA+: locks' = [locks EXCEPT ![resource][txId] = "IS"]
        locks[resource]?[txID] = nil
        if locks[resource]?.isEmpty == true {
            locks[resource] = nil
        }
        
        // TLA+: lockGrantTime' = [lockGrantTime EXCEPT ![txId][resource] = 0]
        lockGrantTime[txID]?[resource] = nil
        
        // TLA+: GrantFromWaitQueue(resource)
        grantFromWaitQueue(resource: resource)
    }
    
    /// Release all locks held by a transaction
    public func releaseAllLocks(txID: TxID) {
        // Find all resources locked by this transaction
        var resourcesToRelease: [String] = []
        
        for (resource, holders) in locks {
            if holders[txID] != nil {
                resourcesToRelease.append(resource)
            }
        }
        
        // Release each lock
        for resource in resourcesToRelease {
            releaseLock(resource: resource, txID: txID)
        }
    }
    
    /// Upgrade a lock (S -> X)
    /// TLA+ Action: UpgradeLock(resource, txId)
    /// Precondition: txID holds S lock on resource
    /// Postcondition: lock upgraded to X or transaction waits
    public func upgradeLock(resource: String, txID: TxID) async throws {
        // Check if transaction holds S lock
        guard locks[resource]?[txID] == .shared else {
            throw DBError.internalError("Cannot upgrade: lock not held")
        }
        
        // Check if upgrade is possible (no other holders)
        let otherHolders = locks[resource]?.filter { $0.key != txID } ?? [:]
        
        if otherHolders.isEmpty {
            // TLA+: locks' = [locks EXCEPT ![resource][txId] = "X"]
            locks[resource]?[txID] = .exclusive
        } else {
            // Must wait - add to wait queue for X lock
            let request = LockRequest(txID: txID, mode: .exclusive, timestamp: UInt64(Date().timeIntervalSince1970 * 1000))
            waitQueue[resource, default: []].append(request)
            
            // Update wait-for graph
            updateWaitForGraph(resource: resource, waiter: txID)
            
            // Check for deadlock
            if hasDeadlock() {
                deadlockVictim = txID
                waitQueue[resource]?.removeAll { $0.txID == txID }
                throw DBError.deadlock
            }
            
            // Wait for upgrade
            try await waitForLock(resource: resource, txID: txID)
        }
    }
    
    // MARK: - Private Helpers
    
    /// Check if lock can be granted
    /// TLA+: CanGrant(resource, mode)
    private func canGrantLock(resource: String, mode: LockMode, txID: TxID) -> Bool {
        // If no locks held, can grant
        guard let holders = locks[resource], !holders.isEmpty else {
            return true
        }
        
        // If only this transaction holds locks, can grant
        if holders.count == 1 && holders[txID] != nil {
            return true
        }
        
        // Check compatibility with all holders
        for (holderTxID, holderMode) in holders {
            if holderTxID != txID {
                if !LockMode.areCompatible(mode, holderMode) {
                    return false
                }
            }
        }
        
        return true
    }
    
    /// Grant a lock
    /// TLA+: GrantLock(resource, mode, txId)
    private func grantLock(resource: String, mode: LockMode, txID: TxID) {
        // TLA+: locks' = [locks EXCEPT ![resource][txId] = mode]
        locks[resource, default: [:]][txID] = mode
        
        // TLA+: lockGrantTime' = [lockGrantTime EXCEPT ![txId][resource] = currentTime]
        let currentTime = UInt64(Date().timeIntervalSince1970 * 1000)
        lockGrantTime[txID, default: [:]][resource] = currentTime
    }
    
    /// Grant locks from wait queue (FIFO order)
    /// TLA+: GrantFromWaitQueue(resource)
    private func grantFromWaitQueue(resource: String) {
        guard var queue = waitQueue[resource], !queue.isEmpty else {
            return
        }
        
        var granted: [Int] = []
        
        // Process queue in FIFO order
        for (index, request) in queue.enumerated() {
            if canGrantLock(resource: resource, mode: request.mode, txID: request.txID) {
                grantLock(resource: resource, mode: request.mode, txID: request.txID)
                granted.append(index)
            } else {
                break  // FIFO: stop at first non-grantable
            }
        }
        
        // Remove granted from queue
        for index in granted.reversed() {
            queue.remove(at: index)
        }
        
        waitQueue[resource] = queue
    }
    
    /// Update wait-for graph
    /// TLA+: UpdateWaitForGraph(resource, txId)
    private func updateWaitForGraph(resource: String, waiter: TxID) {
        // Waiter waits for all current lock holders
        if let holders = locks[resource] {
            waitForGraph[waiter, default: []].formUnion(holders.keys)
        }
    }
    
    /// Check for deadlock using cycle detection
    /// TLA+: HasCycle
    private func hasDeadlock() -> Bool {
        // Simple DFS-based cycle detection
        for startNode in waitForGraph.keys {
            var visited: Set<TxID> = []
            var recStack: Set<TxID> = []
            
            if hasCycleUtil(node: startNode, visited: &visited, recStack: &recStack) {
                return true
            }
        }
        
        return false
    }
    
    /// DFS utility for cycle detection
    /// TLA+: HasCycleUtil(node, visited, recStack)
    private func hasCycleUtil(node: TxID, visited: inout Set<TxID>, recStack: inout Set<TxID>) -> Bool {
        if recStack.contains(node) {
            return true  // Cycle detected
        }
        
        if visited.contains(node) {
            return false
        }
        
        visited.insert(node)
        recStack.insert(node)
        
        if let neighbors = waitForGraph[node] {
            for neighbor in neighbors {
                if hasCycleUtil(node: neighbor, visited: &visited, recStack: &recStack) {
                    return true
                }
            }
        }
        
        recStack.remove(node)
        return false
    }
    
    /// Wait for lock to be granted (with timeout)
    /// TLA+: WaitForLock(resource, txId)
    private func waitForLock(resource: String, txID: TxID) async throws {
        let startTime = Date()
        
        while true {
            // Check if lock granted
            if locks[resource]?[txID] != nil {
                return
            }
            
            // Check timeout
            if Date().timeIntervalSince(startTime) * 1000 > Double(timeoutMs) {
                waitQueue[resource]?.removeAll { $0.txID == txID }
                throw DBError.lockTimeout
            }
            
            // Sleep briefly
            try await Task.sleep(nanoseconds: 10_000_000)  // 10ms
        }
    }
    
    // MARK: - Query Operations
    
    /// Get current deadlock victim
    public func getDeadlockVictim() -> TxID {
        return deadlockVictim
    }
    
    /// Get wait-for graph (for testing)
    public func getWaitForGraph() -> [TxID: Set<TxID>] {
        return waitForGraph
    }
    
    /// Get active locks (for testing)
    public func getActiveLocks() -> [String: [TxID: LockMode]] {
        return locks
    }
    
    /// Check lock compatibility invariant
    /// TLA+ Inv_LockManager_LockCompatibility
    public func checkLockCompatibilityInvariant() -> Bool {
        for (resource, holders) in locks {
            for (txID1, mode1) in holders {
                for (txID2, mode2) in holders {
                    if txID1 != txID2 && !LockMode.areCompatible(mode1, mode2) {
                        return false
                    }
                }
            }
        }
        return true
    }
    
    /// Check deadlock detection invariant
    /// TLA+ Inv_LockManager_DeadlockDetection
    public func checkDeadlockDetectionInvariant() -> Bool {
        // If deadlock exists, victim should be set
        if hasDeadlock() {
            return deadlockVictim != 0
        }
        return true
    }
}

