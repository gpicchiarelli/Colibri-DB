//
//  LSMTreeIndex.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrìDB — BSD 3-Clause License

// Theme: Log-structured forest sketching deferred-write indexing.

import Foundation

/// Lightweight in-memory LSM tree with a mutable memtable and immutable runs.
public final class LSMTreeIndex<Element: Hashable & Comparable, Reference: Hashable>: IndexProtocol {
    public typealias Key = Element
    public typealias Ref = Reference

    private var memtable: [Key: Set<Ref>] = [:]
    private var segments: [[(Key, Set<Ref>)]] = []
    private let memtableThreshold: Int
    private let maxSegmentsBeforeMerge: Int

    public init(memtableThreshold: Int = 256, maxSegmentsBeforeMerge: Int = 4) {
        self.memtableThreshold = max(16, memtableThreshold)
        self.maxSegmentsBeforeMerge = max(2, maxSegmentsBeforeMerge)
    }

    private func flushMemtable() {
        guard !memtable.isEmpty else { return }
        let run = memtable.map { ($0.key, $0.value) }.sorted { $0.0 < $1.0 }
        segments.append(run)
        memtable.removeAll(keepingCapacity: true)
        if segments.count > maxSegmentsBeforeMerge {
            compactSegments()
        }
    }

    private func compactSegments() {
        guard segments.count >= 2 else { return }
        let a = segments.removeFirst()
        let b = segments.removeFirst()
        let merged = mergeRuns(a, b)
        segments.append(merged)
    }

    private func mergeRuns(_ a: [(Key, Set<Ref>)], _ b: [(Key, Set<Ref>)]) -> [(Key, Set<Ref>)] {
        var i = 0, j = 0
        var merged: [(Key, Set<Ref>)] = []
        merged.reserveCapacity(a.count + b.count)
        while i < a.count || j < b.count {
            if j >= b.count || (i < a.count && a[i].0 < b[j].0) {
                merged.append(a[i]); i += 1
            } else if i >= a.count || b[j].0 < a[i].0 {
                merged.append(b[j]); j += 1
            } else {
                var refs = a[i].1
                refs.formUnion(b[j].1)
                merged.append((a[i].0, refs))
                i += 1; j += 1
            }
        }
        return merged
    }

    private func binarySearch(_ run: [(Key, Set<Ref>)], key: Key) -> Int? {
        guard !run.isEmpty else { return nil }
        var l = 0
        var r = run.count - 1
        while l <= r {
            let m = (l + r) >> 1
            if run[m].0 == key { return m }
            if run[m].0 < key { l = m + 1 } else { r = m - 1 }
        }
        return nil
    }

    public func insert(_ key: Key, _ ref: Ref) throws {
        var set = memtable[key] ?? Set<Ref>()
        set.insert(ref)
        memtable[key] = set
        if memtable.count >= memtableThreshold {
            flushMemtable()
        }
    }

    public func searchEquals(_ key: Key) throws -> [Ref] {
        var result = memtable[key] ?? Set<Ref>()
        for run in segments {
            if let idx = binarySearch(run, key: key) {
                result.formUnion(run[idx].1)
            }
        }
        return Array(result)
    }

    public func range(_ lo: Key?, _ hi: Key?) throws -> [Ref] {
        var aggregate: [Key: Set<Ref>] = [:]
        for (key, refs) in memtable { aggregate[key, default: Set<Ref>()].formUnion(refs) }
        for run in segments {
            for (key, refs) in run {
                aggregate[key, default: Set<Ref>()].formUnion(refs)
            }
        }
        let keys = aggregate.keys.filter { key in
            if let lo = lo, key < lo { return false }
            if let hi = hi, key > hi { return false }
            return true
        }.sorted()
        var result: [Ref] = []
        for key in keys {
            if let refs = aggregate[key] { result.append(contentsOf: refs) }
        }
        return result
    }

    public func remove(_ key: Key, _ ref: Ref) throws {
        if var set = memtable[key] {
            set.remove(ref)
            if set.isEmpty { memtable.removeValue(forKey: key) } else { memtable[key] = set }
        }
        for i in segments.indices {
            var run = segments[i]
            if let idx = binarySearch(run, key: key) {
                run[idx].1.remove(ref)
                if run[idx].1.isEmpty { run.remove(at: idx) }
                segments[i] = run
            }
        }
    }
}

