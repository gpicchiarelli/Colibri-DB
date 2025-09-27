//
//  LRUBufferPool.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Page carousel orchestrating LRU, clock, and LRU-2 moves.

import Foundation
import Dispatch
/// A simple LRU buffer pool with optional deferred writes and background flusher.
/// Pages are identified by `PageID` and grouped under a namespace for quota enforcement.

public final class LRUBufferPool: BufferPoolProtocol {
    public enum EvictionPolicy { case lru, clock, lru2 }
    /// Total buffer size in bytes (`capacityPages * pageSize`).
    public var sizeBytes: UInt64 { UInt64(capacityPages * pageSize) }

    private let pageSize: Int
    private let capacityPages: Int
    private let fetch: (PageID) throws -> Data
    private let flush: (PageID, Data) throws -> Void

    private struct Entry { var data: Data }
    private var map: [PageID: Entry] = [:]
    private var order: [PageID] = [] // MRU at end
    private var dirty: Set<PageID> = []
    private var pins: [PageID: Int] = [:]
    private let namespace: String
    private var group: String { namespace.split(separator: ":").map(String.init).first ?? namespace }
    private var deferredWrite: Bool
    private var maxDirty: Int
    private var flusher: DispatchSourceTimer?
    private let q: DispatchQueue
    private var policy: EvictionPolicy = .lru
    // Clock policy state
    private var refBit: [PageID: Bool] = [:]
    private var hand: Int = 0
    // LRU-2 approximate state
    private var tick: UInt64 = 1
    private var last1: [PageID: UInt64] = [:]
    private var last2: [PageID: UInt64] = [:]

    // Metrics
    private(set) public var hits: UInt64 = 0
    private(set) public var misses: UInt64 = 0
    private(set) public var evictions: UInt64 = 0

    /// Creates a new LRU buffer pool.
    /// - Parameters:
    ///   - pageSize: Fixed page size in bytes.
    ///   - capacityPages: Max number of pages in the pool.
    ///   - fetch: Callback to fetch a page from storage.
    ///   - flush: Callback to flush a page to storage.
    ///   - namespace: Quota namespace (e.g., "table" or "index").
    ///   - deferredWrite: If true, marks pages dirty and flushes later.
    ///   - maxDirty: Threshold to trigger dirty flushes when deferred.
    public init(pageSize: Int,
                capacityPages: Int,
                fetch: @escaping (PageID) throws -> Data,
                flush: @escaping (PageID, Data) throws -> Void,
                namespace: String = "default",
                deferredWrite: Bool = false,
                maxDirty: Int = 1024,
                flushQoS: DispatchQoS = .utility) {
        self.pageSize = pageSize
        self.capacityPages = max(1, capacityPages)
        self.fetch = fetch
        self.flush = flush
        self.namespace = namespace
        self.deferredWrite = deferredWrite
        self.maxDirty = maxDirty
        self.q = DispatchQueue(label: "LRUBufferPool.\(UUID().uuidString)", qos: flushQoS)
        BufferNamespaceManager.shared.register(self)
    }

    deinit { BufferNamespaceManager.shared.unregister(self) }

    /// Reads a page without pinning it.
    public func getPage(_ id: PageID) throws -> Data {
        if let e = map[id] {
            hits &+= 1
            touch(id)
            return e.data
        }
        misses &+= 1
        let data = try fetch(id)
        insert(id, data)
        return data
    }

    /// Inserts or updates a page, optionally marking it dirty.
    public func putPage(_ id: PageID, data: Data, dirty isDirty: Bool) throws {
        let existed = map[id] != nil
        map[id] = Entry(data: data)
        touchInsert(id)
        if isDirty {
            dirty.insert(id)
            if !deferredWrite {
                try flush(id, data)
                dirty.remove(id)
            } else if dirty.count >= maxDirty {
                try flushOneDirty()
            }
        }
        if map.count > capacityPages { try evictOne() }
        if !existed { BufferNamespaceManager.shared.enforceQuota(for: group) }
    }

    // Pin/unpin
    /// Pins a page and returns its data.
    public func pinPage(_ id: PageID) throws -> Data {
        let data = try getPage(id)
        pins[id] = (pins[id] ?? 0) + 1
        return data
    }

    /// Decrements pin count for a page.
    public func unpinPage(_ id: PageID) {
        if let c = pins[id] {
            let n = c - 1
            if n <= 0 { pins.removeValue(forKey: id) } else { pins[id] = n }
        }
    }

    // Flush controls
    /// Flushes a specific dirty page to storage.
    public func flushPage(_ id: PageID) throws {
        guard dirty.contains(id), let e = map[id] else { return }
        try flush(id, e.data)
        dirty.remove(id)
    }

    /// Flushes all dirty pages with parallel workers.
    public func flushAll() throws {
        let dirtyPages = Array(dirty)
        guard !dirtyPages.isEmpty else { return }
        
        // Use parallel flush for large numbers of dirty pages
        if dirtyPages.count > 8 {
            try flushAllParallel(dirtyPages)
        } else {
            for id in dirtyPages { try flushPage(id) }
        }
    }
    
    /// Parallel flush implementation using concurrent workers.
    private func flushAllParallel(_ dirtyPages: [PageID]) throws {
        let workerCount = min(4, dirtyPages.count)
        let chunkSize = max(1, dirtyPages.count / workerCount)
        
        var errors: [Error] = []
        let errorLock = NSLock()
        
        DispatchQueue.concurrentPerform(iterations: workerCount) { worker in
            let start = worker * chunkSize
            let end = min(start + chunkSize, dirtyPages.count)
            let chunk = Array(dirtyPages[start..<end])
            
            for id in chunk {
                do {
                    try self.flushPage(id)
                } catch {
                    errorLock.lock()
                    errors.append(error)
                    errorLock.unlock()
                }
            }
        }
        
        if let firstError = errors.first {
            throw firstError
        }
    }

    /// Enables or disables deferred write mode.
    public func setDeferredWrite(_ enabled: Bool) { self.deferredWrite = enabled }

    /// Sets the eviction policy to use for future evictions.
    public func setEvictionPolicy(_ policy: EvictionPolicy) { self.policy = policy }

    /// Starts a background flusher that flushes one dirty page per tick.
    /// - Parameter seconds: Interval between ticks; ignored if <= 0.
    public func startBackgroundFlush(every seconds: TimeInterval) {
        stopBackgroundFlush()
        guard seconds > 0 else { return }
        let t = DispatchSource.makeTimerSource(queue: q)
        t.schedule(deadline: .now() + seconds, repeating: seconds)
        t.setEventHandler { [weak self] in
            guard let self = self else { return }
            if self.dirty.isEmpty { return }
            do { try self.flushOneDirty() } catch { /* ignore in background */ }
        }
        t.resume()
        flusher = t
        deferredWrite = true
    }

    /// Stops the background flusher if running.
    public func stopBackgroundFlush() {
        flusher?.cancel()
        flusher = nil
    }

    /// Returns a one-line statistics summary.
    public func statsString() -> String {
        let pinned = pins.values.filter { $0 > 0 }.count
        let dirtyCount = dirty.count
        return "ns=\(namespace) hits=\(hits) misses=\(misses) evictions=\(evictions) pages=\(map.count)/\(capacityPages) pinned=\(pinned) dirty=\(dirtyCount)"
    }

    /// Snapshot of current buffer pool metrics.
    public struct Metrics {
        public let namespace: String
        public let hits: UInt64
        public let misses: UInt64
        public let evictions: UInt64
        public let pages: Int
        public let capacity: Int
        public let pinned: Int
        public let dirty: Int
    }

    /// Returns current metrics snapshot.
    public func metrics() -> Metrics {
        let pinnedCount = pins.values.filter { $0 > 0 }.count
        return Metrics(namespace: namespace, hits: hits, misses: misses, evictions: evictions, pages: map.count, capacity: capacityPages, pinned: pinnedCount, dirty: dirty.count)
    }

    private func touch(_ id: PageID) {
        if let idx = order.firstIndex(of: id) { order.remove(at: idx); order.append(id) }
        refBit[id] = true
        last2[id] = last1[id] ?? 0
        last1[id] = tick
        tick &+= 1
    }

    private func insert(_ id: PageID, _ data: Data) {
        let existed = map[id] != nil
        map[id] = Entry(data: data)
        touchInsert(id)
        if map.count > capacityPages { try? evictOne() }
        if !existed { BufferNamespaceManager.shared.enforceQuota(for: group) }
    }

    private func touchInsert(_ id: PageID) {
        if let idx = order.firstIndex(of: id) { order.remove(at: idx) }
        order.append(id)
        refBit[id] = true
        last2[id] = last1[id] ?? 0
        last1[id] = tick
        tick &+= 1
    }

    private func flushOneDirty() throws {
        if let id = dirty.first, let e = map[id] {
            try flush(id, e.data)
            dirty.remove(id)
        }
    }

    private func evictOne() throws {
        switch policy {
        case .lru:
            try evictLRU()
        case .clock:
            try evictClock()
        case .lru2:
            try evictLRU2()
        }
    }

    private func evictLRU() throws {
        var idx = 0
        while idx < order.count {
            let victim = order[idx]
            if pins[victim] ?? 0 > 0 { idx += 1; continue }
            try flushIfDirty(victim)
            removeVictim(at: idx, id: victim)
            return
        }
    }

    private func evictClock() throws {
        guard !order.isEmpty else { return }
        var scans = 0
        while scans < max(1, order.count) * 4 {
            let i = hand % max(1, order.count)
            let id = order[i]
            if (pins[id] ?? 0) == 0 {
                if (refBit[id] ?? false) {
                    refBit[id] = false
                } else {
                    try flushIfDirty(id)
                    removeVictim(at: i, id: id)
                    hand = i % max(1, order.count)
                    return
                }
            }
            hand = (hand + 1) % max(1, order.count)
            scans += 1
        }
    }

    private func evictLRU2() throws {
        var bestIdx: Int? = nil
        var bestScore: UInt64 = UInt64.max
        var bestFirst: UInt64 = UInt64.max
        for (i, id) in order.enumerated() {
            if (pins[id] ?? 0) > 0 { continue }
            let s2 = last2[id] ?? 0
            let s1 = last1[id] ?? 0
            let score = s2 == 0 ? UInt64.max - 1 : s2
            if bestIdx == nil || score < bestScore || (score == bestScore && s1 < bestFirst) {
                bestIdx = i; bestScore = score; bestFirst = s1
            }
        }
        if let idx = bestIdx {
            let victim = order[idx]
            try flushIfDirty(victim)
            removeVictim(at: idx, id: victim)
        }
    }

    private func flushIfDirty(_ id: PageID) throws {
        if dirty.contains(id), let e = map[id] {
            try flush(id, e.data)
            dirty.remove(id)
        }
    }

    private func removeVictim(at idx: Int, id: PageID) {
        order.remove(at: idx)
        map.removeValue(forKey: id)
        refBit.removeValue(forKey: id)
        last1.removeValue(forKey: id)
        last2.removeValue(forKey: id)
        evictions &+= 1
    }

    // Exposed helpers for namespace manager
    public func pageCount() -> Int { map.count }
    /// Attempts to evict one page; returns true on success.
    public func tryEvictOne() -> Bool { (try? { try evictOne() }()) != nil }
    
    /// Returns dirty page IDs for WAL consistency checks
    public func getDirtyPages() -> Set<PageID> {
        return dirty
    }
}

// MARK: - Namespace quota manager (shared across pools)
// BufferNamespaceManager moved to its own file for clarity
