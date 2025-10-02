//
//  AnyStringIndex.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: String index adapter bridging heterogeneous backends.

import Foundation
/// Type-erased in-memory string index supporting Hash, ART, and B-Tree variants.

public enum AnyStringIndex {
    case hash(HashIndex<String, RID>)
    case art(ARTIndex<RID>)
    case btree(BTreeIndex<RID>)
    case skiplist(SkipListIndex<String, RID>)
    case fractal(FractalTreeIndex<String, RID>)
    case lsm(LSMTreeIndex<String, RID>)

    /// Initializes an index by kind string (e.g., "hash", "art", "btree").
    public init(kind: String) {
        switch kind.lowercased() {
        case "art": self = .art(ARTIndex<RID>())
        case "btree", "b+tree", "b-tree": self = .btree(BTreeIndex<RID>())
        case "skiplist", "skip-list": self = .skiplist(SkipListIndex<String, RID>())
        case "fractal", "fractal-tree": self = .fractal(FractalTreeIndex<String, RID>())
        case "lsm", "lsm-tree": self = .lsm(LSMTreeIndex<String, RID>())
        default: self = .hash(HashIndex<String, RID>())
        }
    }

    /// Inserts a (key, RID) pair.
    public mutating func insert(key: String, ref: RID) {
        switch self {
        case .hash(var h):
            try? h.insert(key, ref)
            self = .hash(h)
        case .art(var a):
            try? a.insert(key, ref)
            self = .art(a)
        case .btree(var b):
            do {
                try b.insert(key, ref)
                print("Debug AnyStringIndex: Successfully inserted key '\(key)' into BTree")
            } catch {
                print("Debug AnyStringIndex: Failed to insert key '\(key)' into BTree: \(error)")
            }
            self = .btree(b)
        case .skiplist(var s):
            try? s.insert(key, ref)
            self = .skiplist(s)
        case .fractal(var f):
            try? f.insert(key, ref)
            self = .fractal(f)
        case .lsm(var l):
            try? l.insert(key, ref)
            self = .lsm(l)
        }
    }

    /// Searches for an exact match and returns matching RIDs.
    public func searchEquals(_ key: String) -> [RID] {
        switch self {
        case .hash(let h): return (try? h.searchEquals(key)) ?? []
        case .art(let a): return (try? a.searchEquals(key)) ?? []
        case .btree(let b): 
            do {
                let result = try b.searchEquals(key)
                print("Debug AnyStringIndex: BTree search for '\(key)' returned \(result.count) results")
                return result
            } catch {
                print("Debug AnyStringIndex: BTree search for '\(key)' failed: \(error)")
                return []
            }
        case .skiplist(let s): return (try? s.searchEquals(key)) ?? []
        case .fractal(let f): return (try? f.searchEquals(key)) ?? []
        case .lsm(let l): return (try? l.searchEquals(key)) ?? []
        }
    }

    /// Performs a range query over string keys.
    public func range(_ lo: String?, _ hi: String?) -> [RID] {
        switch self {
        case .hash(let h): return (try? h.range(lo, hi)) ?? []
        case .art(let a): return (try? a.range(lo, hi)) ?? []
        case .btree(let b): return (try? b.range(lo, hi)) ?? []
        case .skiplist(let s): return (try? s.range(lo, hi)) ?? []
        case .fractal(let f): return (try? f.range(lo, hi)) ?? []
        case .lsm(let l): return (try? l.range(lo, hi)) ?? []
        }
    }

    /// Removes a specific (key, RID) pair from the index.
    public mutating func remove(key: String, ref: RID) {
        switch self {
        case .hash(var h):
            try? h.remove(key, ref)
            self = .hash(h)
        case .art(var a):
            try? a.remove(key, ref)
            self = .art(a)
        case .btree(var b):
            try? b.remove(key, ref)
            self = .btree(b)
        case .skiplist(var s):
            try? s.remove(key, ref)
            self = .skiplist(s)
        case .fractal(var f):
            try? f.remove(key, ref)
            self = .fractal(f)
        case .lsm(var l):
            try? l.remove(key, ref)
            self = .lsm(l)
        }
    }
}

