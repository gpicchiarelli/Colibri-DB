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
    private var map: [Key: Set<Ref>] = [:]

    public init() {}

    /// Inserts a reference for the given key.
    public mutating func insert(_ key: Key, _ ref: Ref) throws {
        var set = map[key] ?? Set<Ref>()
        set.insert(ref)
        map[key] = set
    }

    /// Returns all references equal to `key`.
    public func searchEquals(_ key: Key) throws -> [Ref] {
        Array(map[key] ?? [])
    }

    /// Range queries are unsupported; returns equality results only when `lo == hi`.
    public func range(_ lo: Key?, _ hi: Key?) throws -> [Ref] {
        // Hash index is not suited for range; return equality only if lo==hi
        if let l = lo, let h = hi, l == h { return try searchEquals(l) }
        return []
    }

    /// Removes a specific reference for the given key.
    public mutating func remove(_ key: Key, _ ref: Ref) throws {
        guard var set = map[key] else { return }
        set.remove(ref)
        if set.isEmpty { map.removeValue(forKey: key) } else { map[key] = set }
    }
}

