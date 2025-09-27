//
//  BufferNamespaceManager.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrìDB — BSD 3-Clause License
// Global namespace quota manager for buffer pools (tables/indexes)

// Theme: Guardian of buffer namespaces keeping quotas fair.

import Foundation
/// Manages per-namespace page quotas across registered buffer pools (tables/indexes).

final class BufferNamespaceManager: @unchecked Sendable {
    static let shared = BufferNamespaceManager()
    private init() {}
    struct WeakPool { weak var pool: LRUBufferPool? }
    private var groups: [String: [WeakPool]] = [:]
    private var quota: [String: Int] = [:]
    private let lock = NSLock()

    func register(_ pool: LRUBufferPool) {
        lock.lock(); defer { lock.unlock() }
        let ns = pool.metrics().namespace
        let g = ns.split(separator: ":").map(String.init).first ?? ns
        var arr = groups[g] ?? []
        arr.append(WeakPool(pool: pool))
        groups[g] = arr
    }

    func unregister(_ pool: LRUBufferPool) {
        lock.lock(); defer { lock.unlock() }
        for (g, arr) in groups {
            groups[g] = arr.filter { $0.pool != nil && $0.pool !== pool }
        }
    }

    func setQuota(group: String, pages: Int) {
        lock.lock(); quota[group] = max(1, pages); lock.unlock()
        enforceQuota(for: group)
    }

    func enforceQuota(for group: String) {
        lock.lock(); defer { lock.unlock() }
        guard let q = quota[group], q > 0 else { return }
        var pools = (groups[group] ?? []).compactMap { $0.pool }
        groups[group] = pools.map { WeakPool(pool: $0) }
        var total = pools.reduce(0) { $0 + $1.pageCount() }
        if total <= q { return }
        pools.sort { $0.pageCount() > $1.pageCount() }
        var i = 0
        while total > q && !pools.isEmpty {
            let p = pools[i % pools.count]
            if p.tryEvictOne() { total -= 1 } else { i += 1 }
            i += 1
            if i > pools.count * 4 { break }
        }
    }
}

