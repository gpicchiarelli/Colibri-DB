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

    private var buffer: [Key: Set<Ref>] = [:]
    private var baseTree: [Key: Set<Ref>] = [:]
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
        for (key, refs) in buffer {
            var set = baseTree[key] ?? Set<Ref>()
            set.formUnion(refs)
            baseTree[key] = set
        }
        buffer.removeAll(keepingCapacity: true)
    }

    private func materialized() -> [Key: Set<Ref>] {
        if buffer.isEmpty { return baseTree }
        var combined = baseTree
        for (key, refs) in buffer {
            combined[key, default: Set<Ref>()].formUnion(refs)
        }
        return combined
    }

    public func insert(_ key: Key, _ ref: Ref) throws {
        var set = buffer[key] ?? Set<Ref>()
        set.insert(ref)
        buffer[key] = set
        flushBufferIfNeeded()
    }

    public func searchEquals(_ key: Key) throws -> [Ref] {
        var result = baseTree[key] ?? Set<Ref>()
        if let buf = buffer[key] { result.formUnion(buf) }
        return Array(result)
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
            if let refs = combined[key] { result.append(contentsOf: refs) }
        }
        return result
    }

    public func remove(_ key: Key, _ ref: Ref) throws {
        if var set = buffer[key] {
            set.remove(ref)
            if set.isEmpty { buffer.removeValue(forKey: key) } else { buffer[key] = set }
        }
        if var set = baseTree[key] {
            set.remove(ref)
            if set.isEmpty { baseTree.removeValue(forKey: key) } else { baseTree[key] = set }
        }
    }
}


