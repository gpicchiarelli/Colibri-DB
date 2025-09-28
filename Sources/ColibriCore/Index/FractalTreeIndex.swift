//
//  FractalTreeIndex.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrìDB — BSD 3-Clause License

// Theme: Fractal tree laboratory exploring buffered hierarchical merges.

import Foundation

/// Simplified fractal tree index: maintains a buffered dictionary that periodically flushes
/// into a sorted base map, mimicking message-buffered propagation.
public final class FractalTreeIndex<Element: Hashable & Comparable, Reference: Hashable>: IndexProtocol {
    public typealias Key = Element
    public typealias Ref = Reference

    private struct Entry {
        var live: Set<Ref> = []
        var tombstones: Set<Ref> = []
        mutating func insert(_ ref: Ref) { tombstones.remove(ref); live.insert(ref) }
        mutating func delete(_ ref: Ref) { if live.remove(ref) != nil { tombstones.insert(ref) } }
        func visible() -> [Ref] { Array(live) }
        var isDead: Bool { live.isEmpty && tombstones.isEmpty }
        mutating func merge(with other: Entry) {
            live.formUnion(other.live)
            tombstones.formUnion(other.tombstones)
        }
    }

    private var buffer: [Key: Entry] = [:]
    private var baseTree: [Key: Entry] = [:]
    private let bufferCapacity: Int

    public init(bufferCapacity: Int = 256) {
        self.bufferCapacity = max(16, bufferCapacity)
    }

    private func flushBufferIfNeeded() {
        guard buffer.count >= bufferCapacity else { return }
        flushBuffer()
    }

    private func flushBuffer() {
        guard !buffer.isEmpty else { return }
        for (key, entry) in buffer {
            var stored = baseTree[key] ?? Entry()
            stored.merge(with: entry)
            baseTree[key] = stored
        }
        buffer.removeAll(keepingCapacity: true)
    }

    private func materialized() -> [Key: Entry] {
        if buffer.isEmpty { return baseTree }
        var combined = baseTree
        for (key, entry) in buffer {
            var stored = combined[key] ?? Entry()
            stored.merge(with: entry)
            combined[key] = stored
        }
        return combined
    }

    public func insert(_ key: Key, _ ref: Ref) throws {
        var entry = buffer[key] ?? Entry()
        entry.insert(ref)
        buffer[key] = entry
        flushBufferIfNeeded()
    }

    public func searchEquals(_ key: Key) throws -> [Ref] {
        var entry = baseTree[key] ?? Entry()
        if let buf = buffer[key] { entry.merge(with: buf) }
        return entry.visible()
    }

    public func range(_ lo: Key?, _ hi: Key?) throws -> [Ref] {
        let combined = materialized()
        let keys = combined.keys.filter { key in
            if let lo = lo, key < lo { return false }
            if let hi = hi, key > hi { return false }
            return true
        }.sorted()
        var result: [Ref] = []
        for key in keys {
            if let entry = combined[key] { result.append(contentsOf: entry.visible()) }
        }
        return result
    }

    public func remove(_ key: Key, _ ref: Ref) throws {
        if var entry = buffer[key] {
            entry.delete(ref)
            if entry.isDead { buffer.removeValue(forKey: key) } else { buffer[key] = entry }
        }
        if var entry = baseTree[key] {
            entry.delete(ref)
            if entry.isDead { baseTree.removeValue(forKey: key) } else { baseTree[key] = entry }
        }
    }
}


