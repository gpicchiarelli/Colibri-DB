//
//  BTreeIndex.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: B-tree base class sketching balanced node behaviors.

import Foundation
/// Simple in-memory B+Tree for String keys mapping to sets of references.

// Simple in-memory B+Tree for String keys -> Set<Ref>
public final class BTreeIndex<Ref: Hashable>: IndexProtocol {
    public typealias Key = String
    public typealias Ref = Ref

    final class Node {
        var isLeaf: Bool
        var keys: [String] = []
        var children: [Node] = []
        var values: [TombstoneSet<Ref>] = []
        weak var nextLeaf: Node?
        init(isLeaf: Bool) { self.isLeaf = isLeaf }
    }

    private let maxKeys: Int
    private var root: Node

    /// Creates a B+Tree with specified order (max keys per node).
    public init(order: Int = 32) {
        self.maxKeys = max(4, order)
        self.root = Node(isLeaf: true)
    }

    /// Returns all references equal to `key`.
    public func searchEquals(_ key: String) throws -> [Ref] {
        let leaf = findLeaf(for: key)
        if let idx = leaf.keys.binarySearch(key) { return leaf.values[idx].visible() }
        return []
    }

    /// Returns all references with keys in [lo, hi] inclusive.
    public func range(_ lo: String?, _ hi: String?) throws -> [Ref] {
        var result: [Ref] = []
        var node: Node
        if let lo = lo { node = findLeaf(for: lo) } else { node = leftmostLeaf() }
        while true {
            for (i, k) in node.keys.enumerated() {
                if let lo = lo, k < lo { continue }
                if let hi = hi, k > hi { return Array(Set(result)) }
                result.append(contentsOf: node.values[i].visible())
            }
            guard let next = node.nextLeaf else { break }
            node = next
        }
        return Array(Set(result))
    }

    /// Inserts a reference for `key`.
    public func insert(_ key: String, _ ref: Ref) throws {
        let (promoKey, newRight) = insert(key: key, ref: ref, into: root)
        if let pk = promoKey, let r = newRight {
            // create new root
            let newRoot = Node(isLeaf: false)
            newRoot.keys = [pk]
            newRoot.children = [root, r]
            root = newRoot
        }
    }

    /// Removes a reference for `key` (not implemented in MVP).
    public func remove(_ key: String, _ ref: Ref) throws {
        // Not implemented in MVP
    }

    // MARK: - Internals

    private func leftmostLeaf() -> Node {
        var node = root
        while !node.isLeaf { node = node.children.first! }
        return node
    }

    private func findLeaf(for key: String) -> Node {
        var node = root
        while !node.isLeaf {
            let idx = node.keys.upperBound(for: key)
            node = node.children[idx]
        }
        return node
    }

    // returns (promotedKey, newRightNode) if split occurred
    private func insert(key: String, ref: Ref, into node: Node) -> (String?, Node?) {
        if node.isLeaf {
            if let idx = node.keys.binarySearch(key) {
                // append unique ref
                node.values[idx].insert(ref)
            } else {
                let pos = node.keys.lowerBound(for: key)
                node.keys.insert(key, at: pos)
                var ts = TombstoneSet<Ref>()
                ts.insert(ref)
                node.values.insert(ts, at: pos)
            }
            if node.keys.count > maxKeys { return splitLeaf(node) }
            return (nil, nil)
        } else {
            let childIdx = node.keys.upperBound(for: key)
            let child = node.children[childIdx]
            let (promo, right) = insert(key: key, ref: ref, into: child)
            if let pk = promo, let r = right {
                // insert promoted key and new right child
                let pos = node.keys.lowerBound(for: pk)
                node.keys.insert(pk, at: pos)
                node.children.insert(r, at: pos + 1)
                if node.keys.count > maxKeys { return splitInternal(node) }
            }
            return (nil, nil)
        }
    }

    private func splitLeaf(_ node: Node) -> (String?, Node?) {
        let mid = node.keys.count / 2
        let right = Node(isLeaf: true)
        right.keys = Array(node.keys[mid...])
        right.values = Array(node.values[mid...])
        node.keys = Array(node.keys[..<mid])
        node.values = Array(node.values[..<mid])
        right.nextLeaf = node.nextLeaf
        node.nextLeaf = right
        let promoted = right.keys.first!
        return (promoted, right)
    }

    private func splitInternal(_ node: Node) -> (String?, Node?) {
        let mid = node.keys.count / 2
        let promoted = node.keys[mid]
        let right = Node(isLeaf: false)
        right.keys = Array(node.keys[(mid+1)...])
        right.children = Array(node.children[(mid+1)...])
        node.keys = Array(node.keys[..<mid])
        node.children = Array(node.children[..<(mid+1)])
        return (promoted, right)
    }

    // MARK: - Dump (pairs)
    /// Returns all key -> refs pairs in order.
    public func pairs() -> [(String, [Ref])] {
        var res: [(String, [Ref])] = []
        var leaf = leftmostLeaf()
        while true {
            for (i, k) in leaf.keys.enumerated() {
                res.append((k, leaf.values[i].visible()))
            }
            if let n = leaf.nextLeaf { leaf = n } else { break }
        }
        return res
    }
}

// MARK: - Helpers

fileprivate extension Array where Element == String {
    // First index whose element is >= key
    func lowerBound(for key: String) -> Int {
        var l = 0, r = count
        while l < r {
            let m = (l + r) >> 1
            if self[m] < key { l = m + 1 } else { r = m }
        }
        return l
    }
    // First index whose element is > key
    func upperBound(for key: String) -> Int {
        var l = 0, r = count
        while l < r {
            let m = (l + r) >> 1
            if self[m] <= key { l = m + 1 } else { r = m }
        }
        return l
    }
    // Index of key if present
    func binarySearch(_ key: String) -> Int? {
        var l = 0, r = count - 1
        while l <= r {
            let m = (l + r) >> 1
            if self[m] == key { return m }
            if self[m] < key { l = m + 1 } else { r = m - 1 }
        }
        return nil
    }
}

