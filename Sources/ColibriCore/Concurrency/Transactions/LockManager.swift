//
//  LockManager.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrDB — BSD 3-Clause License

// Theme: Lock guardian coordinating shared and exclusive access.

import Foundation

/// Lock manager providing shared/exclusive locks with deadlock detection and optional timeouts.
final class LockManager: LockManagerProtocol, @unchecked Sendable {
    private struct Holder {
        var mode: LockMode
        var count: Int
    }

    private final class Waiter {
        let tid: UInt64
        let mode: LockMode
        let semaphore: DispatchSemaphore

        init(tid: UInt64, mode: LockMode) {
            self.tid = tid
            self.mode = mode
            self.semaphore = DispatchSemaphore(value: 0)
        }
    }

    private struct Entry {
        var holders: [UInt64: Holder] = [:]
        var waiters: [Waiter] = []
    }

    private var table: [LockTarget: Entry] = [:]
    private var locksByTid: [UInt64: Set<LockTarget>] = [:]
    
    // 🚀 OPTIMIZATION: Lock striping to reduce contention
    private let stripeCount: Int = 64  // Power of 2 for efficient modulo
    private var stripes: [NSLock] = []
    private let globalLock = NSLock()  // For operations requiring all stripes
    private let defaultTimeout: TimeInterval

    init(defaultTimeout: TimeInterval) {
        self.defaultTimeout = defaultTimeout
        
        // 🚀 OPTIMIZATION: Initialize lock stripes for reduced contention
        self.stripes = (0..<stripeCount).map { _ in NSLock() }
        print("🚀 LockManager initialized with \(stripeCount) lock stripes for optimal performance")
    }

    // MARK: - 🚀 OPTIMIZATION: Lock Striping Helpers
    
    /// Get the stripe index for a lock target (hash-based distribution)
    private func getStripeIndex(for target: LockTarget) -> Int {
        return abs(target.hashValue) % stripeCount
    }
    
    /// Execute code with the appropriate stripe lock
    private func withStripeLock<T>(for target: LockTarget, _ block: () throws -> T) rethrows -> T {
        let stripe = stripes[getStripeIndex(for: target)]
        stripe.lock()
        defer { stripe.unlock() }
        return try block()
    }
    
    /// Execute code with multiple stripe locks (ordered to prevent deadlock)
    private func withMultipleStripeLocks<T>(for targets: [LockTarget], _ block: () throws -> T) rethrows -> T {
        let indices = Set(targets.map { getStripeIndex(for: $0) }).sorted()
        
        // Lock in ascending order to prevent deadlock
        for index in indices {
            stripes[index].lock()
        }
        
        defer {
            // Unlock in reverse order
            for index in indices.reversed() {
                stripes[index].unlock()
            }
        }
        
        return try block()
    }
    
    /// Execute code with global lock (for operations requiring all stripes)
    private func withGlobalLock<T>(_ block: () throws -> T) rethrows -> T {
        globalLock.lock()
        defer { globalLock.unlock() }
        return try block()
    }
    
    // MARK: - Locking API

    @discardableResult
    func lock(_ resource: LockTarget, mode: LockMode, tid: UInt64, timeout: TimeInterval?) throws -> LockHandle {
        let effectiveTimeout = (timeout ?? defaultTimeout)
        let waiter = Waiter(tid: tid, mode: mode)
        var enqueued = false

        // 🚀 OPTIMIZATION: Use stripe lock with optimized structure
        while true {
            // Try to acquire lock without waiting
            let acquired: LockHandle? = try withStripeLock(for: resource) {
                var entry = table[resource] ?? Entry()
                
                if canGrant(mode: mode, tid: tid, holders: entry.holders) {
                    let resolvedMode = resolveMode(current: entry.holders[tid]?.mode, requested: mode)
                    var holder = entry.holders[tid] ?? Holder(mode: resolvedMode, count: 0)
                    holder.count += 1
                    holder.mode = resolvedMode
                    entry.holders[tid] = holder
                    table[resource] = entry
                    locksByTid[tid, default: []].insert(resource)
                    return LockHandle(resource: resource, tid: tid, mode: resolvedMode)
                }

                if !enqueued {
                    entry.waiters.append(waiter)
                    table[resource] = entry
                    enqueued = true
                    if let cycle = detectDeadlock(startingFrom: tid) {
                        _ = remove(waiter: waiter, from: resource)
                        throw DBError.deadlock("\(cycle)")
                    }
                }
                
                return nil  // Need to wait
            }
            
            if let handle = acquired {
                return handle
            }
            
            // Wait outside the lock to reduce contention
            let waitResult: DispatchTimeoutResult
            if effectiveTimeout <= 0 {
                waitResult = waiter.semaphore.wait(timeout: .distantFuture)
            } else {
                waitResult = waiter.semaphore.wait(timeout: .now() + effectiveTimeout)
            }
            
            if waitResult == .timedOut {
                let removed = try withStripeLock(for: resource) {
                    return remove(waiter: waiter, from: resource)
                }
                if removed {
                    throw DBError.lockTimeout("Lock request \(mode) on \(resource) timed out")
                }
            }
            // Loop and try again
        }
    }

    func unlock(_ handle: LockHandle) {
        // 🚀 OPTIMIZATION: Use stripe lock for unlock operations
        let signals = withStripeLock(for: handle.resource) {
            let resource = handle.resource
            var signals: [Waiter] = []
            if var entry = table[resource], var holder = entry.holders[handle.tid] {
                holder.count -= 1
                if holder.count <= 0 {
                    entry.holders.removeValue(forKey: handle.tid)
                    locksByTid[handle.tid]?.remove(resource)
                    if locksByTid[handle.tid]?.isEmpty == true { locksByTid.removeValue(forKey: handle.tid) }
                } else {
                    entry.holders[handle.tid] = holder
                }
                table[resource] = entry
                signals = tryGrantWaiters(on: resource)
            }
            return signals
        }
        
        // Signal waiters outside the lock to reduce contention
        for waiter in signals { waiter.semaphore.signal() }
    }

    func unlockAll(for tid: UInt64) {
        // 🚀 OPTIMIZATION: Use multiple stripe locks for unlockAll
        let signals: [Waiter] = withGlobalLock {
            guard let resources = locksByTid.removeValue(forKey: tid) else { return [] }
            var allSignals: [Waiter] = []
            
            // Group resources by stripe to minimize lock operations
            let resourcesByStripe = Dictionary(grouping: resources) { resource in
                getStripeIndex(for: resource)
            }
            
            for (stripeIndex, stripeResources) in resourcesByStripe {
                let stripe = stripes[stripeIndex]
                stripe.lock()
                defer { stripe.unlock() }
                
                for resource in stripeResources {
                    if var entry = table[resource] {
                        entry.holders.removeValue(forKey: tid)
                        table[resource] = entry
                        allSignals.append(contentsOf: tryGrantWaiters(on: resource))
                    }
                }
            }
            
            return allSignals
        }
        
        // Signal waiters outside the locks to reduce contention
        for waiter in signals { waiter.semaphore.signal() }
    }

    // MARK: - Helpers

    private func canGrant(mode: LockMode, tid: UInt64, holders: [UInt64: Holder]) -> Bool {
        let otherHolders = holders.filter { $0.key != tid }
        if otherHolders.isEmpty {
            return true
        }
        switch mode {
        case .shared:
            for (_, holder) in otherHolders where holder.mode == .exclusive { return false }
            return true
        case .exclusive:
            return false
        }
    }

    private func resolveMode(current: LockMode?, requested: LockMode) -> LockMode {
        guard let current = current else { return requested }
        if current == .exclusive || requested == .exclusive { return .exclusive }
        return .shared
    }

    private func tryGrantWaiters(on resource: LockTarget) -> [Waiter] {
        guard var entry = table[resource] else { return [] }
        var granted: [Waiter] = []
        var index = 0
        while index < entry.waiters.count {
            let waiter = entry.waiters[index]
            if canGrant(mode: waiter.mode, tid: waiter.tid, holders: entry.holders) {
                entry.waiters.remove(at: index)
                var holder = entry.holders[waiter.tid] ?? Holder(mode: waiter.mode, count: 0)
                holder.count += 1
                holder.mode = resolveMode(current: holder.mode, requested: waiter.mode)
                entry.holders[waiter.tid] = holder
                locksByTid[waiter.tid, default: []].insert(resource)
                granted.append(waiter)
                if waiter.mode == .exclusive { break }
                continue
            }
            if waiter.mode == .exclusive {
                break // next waiters cannot be granted while exclusive is blocked
            }
            index += 1
        }
        if entry.holders.isEmpty && entry.waiters.isEmpty {
            table.removeValue(forKey: resource)
        } else {
            table[resource] = entry
        }
        return granted
    }

    private func remove(waiter: Waiter, from resource: LockTarget) -> Bool {
        guard var entry = table[resource] else { return false }
        var removed = false
        entry.waiters.removeAll { existing in
            if existing === waiter {
                removed = true; return true
            }
            return false
        }
        if entry.holders.isEmpty && entry.waiters.isEmpty {
            table.removeValue(forKey: resource)
        } else {
            table[resource] = entry
        }
        return removed
    }

    private func detectDeadlock(startingFrom start: UInt64) -> String? {
        guard start != 0 else { return nil }
        var graph: [UInt64: Set<UInt64>] = [:]
        for (_, entry) in table {
            let holders = entry.holders.keys.filter { $0 != 0 }
            guard !holders.isEmpty else { continue }
            for waiter in entry.waiters where waiter.tid != 0 {
                let deps = holders.filter { $0 != waiter.tid }
                if !deps.isEmpty {
                    graph[waiter.tid, default: []].formUnion(deps)
                }
            }
        }
        var visited: Set<UInt64> = []
        var stack: [UInt64] = []
        var inStack: Set<UInt64> = []

        func dfs(_ node: UInt64) -> [UInt64]? {
            if inStack.contains(node) {
                if let idx = stack.firstIndex(of: node) {
                    return Array(stack[idx...]) + [node]
                }
                return [node]
            }
            if visited.contains(node) { return nil }
            visited.insert(node)
            inStack.insert(node)
            stack.append(node)
            for neighbor in graph[node] ?? [] {
                if let cycle = dfs(neighbor) { return cycle }
            }
            _ = stack.popLast()
            inStack.remove(node)
            return nil
        }

        guard let cycle = dfs(start), cycle.count > 1 else { return nil }
        return cycle.map { String($0) }.joined(separator: " -> ")
    }
}

