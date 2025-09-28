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

    private struct Entry {
        var live: Set<Ref> = []
        var tombstones: Set<Ref> = []
        mutating func insert(_ ref: Ref) { tombstones.remove(ref); live.insert(ref) }
        mutating func delete(_ ref: Ref) { if live.remove(ref) != nil { tombstones.insert(ref) } }
        var visible: [Ref] { Array(live) }
        var isDead: Bool { live.isEmpty && tombstones.isEmpty }
    }

    private var memtable: [Key: Entry] = [:]
    private var segments: [[(Key, Entry)]] = []
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

    private func mergeRuns(_ a: [(Key, Entry)], _ b: [(Key, Entry)]) -> [(Key, Entry)] {
        var i = 0, j = 0
        var merged: [(Key, Entry)] = []
        merged.reserveCapacity(a.count + b.count)
        while i < a.count || j < b.count {
            if j >= b.count || (i < a.count && a[i].0 < b[j].0) {
                merged.append(a[i]); i += 1
            } else if i >= a.count || b[j].0 < a[i].0 {
                merged.append(b[j]); j += 1
            } else {
                var entry = a[i].1
                entry.live.formUnion(b[j].1.live)
                entry.tombstones.formUnion(b[j].1.tombstones)
                merged.append((a[i].0, entry))
                i += 1; j += 1
            }
        }
        return merged
    }

    private func binarySearch(_ run: [(Key, Entry)], key: Key) -> Int? {
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
        var entry = memtable[key] ?? Entry()
        entry.insert(ref)
        memtable[key] = entry
        if memtable.count >= memtableThreshold {
            flushMemtable()
        }
    }

    public func searchEquals(_ key: Key) throws -> [Ref] {
        var entry = memtable[key] ?? Entry()
        for run in segments {
            if let idx = binarySearch(run, key: key) {
                entry.live.formUnion(run[idx].1.live)
                entry.tombstones.formUnion(run[idx].1.tombstones)
            }
        }
        return entry.visible
    }

    public func range(_ lo: Key?, _ hi: Key?) throws -> [Ref] {
        var aggregate: [Key: Entry] = [:]
        for (key, entry) in memtable {
            var stored = aggregate[key] ?? Entry()
            stored.live.formUnion(entry.live)
            stored.tombstones.formUnion(entry.tombstones)
            aggregate[key] = stored
        }
        for run in segments {
            for (key, entry) in run {
                var stored = aggregate[key] ?? Entry()
                stored.live.formUnion(entry.live)
                stored.tombstones.formUnion(entry.tombstones)
                aggregate[key] = stored
            }
        }
        let keys = aggregate.keys.filter { key in
            if let lo = lo, key < lo { return false }
            if let hi = hi, key > hi { return false }
            return true
        }.sorted()
        var result: [Ref] = []
        for key in keys {
            if let entry = aggregate[key] { result.append(contentsOf: entry.visible) }
        }
        return result
    }

    public func remove(_ key: Key, _ ref: Ref) throws {
        if var entry = memtable[key] {
            entry.delete(ref)
            if entry.isDead { memtable.removeValue(forKey: key) } else { memtable[key] = entry }
        }
        for i in segments.indices {
            var run = segments[i]
            if let idx = binarySearch(run, key: key) {
                run[idx].1.delete(ref)
                if run[idx].1.isDead { run.remove(at: idx) }
                segments[i] = run
            }
        }
    }
}

