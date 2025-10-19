//
//  LockManager.swift
//  ColibrìDB Lock Manager with Deadlock Detection
//
//  Based on: spec/LockManager.tla
//  Implements: Intent locks, deadlock detection with wait-for graph
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//

import Foundation

/// Lock Manager for concurrency control
/// Corresponds to TLA+ module: LockManager.tla
public actor LockManager {
    // MARK: - State Variables
    
    /// Active locks: resource -> (txID -> LockMode)
    private var locks: [String: [TxID: LockMode]] = [:]
    
    /// Wait queue: resource -> [(txID, mode)]
    private var waitQueue: [String: [(TxID, LockMode)]] = [:]
    
    /// Wait-for graph for deadlock detection
    private var waitForGraph: [TxID: Set<TxID>] = [:]
    
    /// Lock grant time (for timeout)
    private var lockGrantTime: [String: [TxID: Date]] = [:]
    
    /// Timeout duration (seconds)
    private let timeoutSeconds: Double = 30.0
    
    // MARK: - Core Operations
    
    /// Request a lock
    /// TLA+ Action: RequestLock(resource, mode, txId)
    public func requestLock(resource: String, mode: LockMode, txID: TxID) async throws {
        // Check if lock can be granted immediately
        if canGrantLock(resource: resource, mode: mode, txID: txID) {
            // Grant lock
            grantLock(resource: resource, mode: mode, txID: txID)
        } else {
            // Add to wait queue
            waitQueue[resource, default: []].append((txID, mode))
            
            // Update wait-for graph
            updateWaitForGraph(resource: resource, waiter: txID)
            
            // Check for deadlock
            if hasDeadlock() {
                // Abort this transaction (deadlock victim)
                waitQueue[resource]?.removeAll { $0.0 == txID }
                throw DBError.deadlock
            }
            
            // Wait for lock to be granted (or timeout)
            try await waitForLock(resource: resource, txID: txID)
        }
    }
    
    /// Release a lock
    /// TLA+ Action: ReleaseLock(resource, txId)
    public func releaseLock(resource: String, txID: TxID) {
        // Remove lock
        locks[resource]?[txID] = nil
        if locks[resource]?.isEmpty == true {
            locks[resource] = nil
        }
        
        lockGrantTime[resource]?[txID] = nil
        
        // Grant locks from wait queue (FIFO)
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
    public func upgradeLock(resource: String, txID: TxID) throws {
        // Check if transaction holds S lock
        guard locks[resource]?[txID] == .shared else {
            throw DBError.internalError("Cannot upgrade: lock not held")
        }
        
        // Check if upgrade is possible
        let otherHolders = locks[resource]?.filter { $0.key != txID } ?? [:]
        
        if otherHolders.isEmpty {
            // Can upgrade immediately
            locks[resource]?[txID] = .exclusive
        } else {
            // Must wait - potential deadlock
            throw DBError.lockTimeout
        }
    }
    
    // MARK: - Private Helpers
    
    /// Check if lock can be granted
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
    private func grantLock(resource: String, mode: LockMode, txID: TxID) {
        locks[resource, default: [:]][txID] = mode
        lockGrantTime[resource, default: [:]][txID] = Date()
    }
    
    /// Grant locks from wait queue
    private func grantFromWaitQueue(resource: String) {
        guard var queue = waitQueue[resource], !queue.isEmpty else {
            return
        }
        
        var granted: [Int] = []
        
        for (index, (txID, mode)) in queue.enumerated() {
            if canGrantLock(resource: resource, mode: mode, txID: txID) {
                grantLock(resource: resource, mode: mode, txID: txID)
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
    private func waitForLock(resource: String, txID: TxID) async throws {
        let startTime = Date()
        
        while true {
            // Check if lock granted
            if locks[resource]?[txID] != nil {
                return
            }
            
            // Check timeout
            if Date().timeIntervalSince(startTime) > timeoutSeconds {
                waitQueue[resource]?.removeAll { $0.0 == txID }
                throw DBError.lockTimeout
            }
            
            // Sleep briefly
            try await Task.sleep(nanoseconds: 10_000_000)  // 10ms
        }
    }
}

