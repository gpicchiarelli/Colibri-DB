//
//  HashIndex.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Hash index workshop implementing scatter-and-bucket lookups.

import Foundation
/// Simple in-memory hash index mapping keys to reference sets.

public struct HashIndex<Key: Hashable & Comparable, Ref: Hashable>: IndexProtocol {
    private struct Entry {
        var live: Set<Ref> = []
        var tombstones: Set<Ref> = []

        mutating func insert(_ ref: Ref) {
            tombstones.remove(ref)
            live.insert(ref)
        }

        mutating func remove(_ ref: Ref) {
            if live.remove(ref) != nil {
                tombstones.insert(ref)
            }
        }

        func visible() -> [Ref] { Array(live) }

        var isEmpty: Bool { live.isEmpty && tombstones.isEmpty }
    }

    private var map: [Key: Entry] = [:]

    public init() {}

    public mutating func insert(_ key: Key, _ ref: Ref) throws {
        var entry = map[key] ?? Entry()
        entry.insert(ref)
        map[key] = entry
    }

    public func searchEquals(_ key: Key) throws -> [Ref] {
        guard let entry = map[key] else { return [] }
        return entry.visible()
    }

    public func range(_ lo: Key?, _ hi: Key?) throws -> [Ref] {
        guard let lo = lo, let hi = hi, lo == hi else { return [] }
        return try searchEquals(lo)
    }

    public mutating func remove(_ key: Key, _ ref: Ref) throws {
        guard var entry = map[key] else { return }
        entry.remove(ref)
        if entry.isEmpty {
            map.removeValue(forKey: key)
        } else {
            map[key] = entry
        }
    }
}

