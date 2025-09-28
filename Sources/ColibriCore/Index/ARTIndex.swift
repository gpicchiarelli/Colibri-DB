//
//  ARTIndex.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Adaptive radix grove handling compressed search paths.

import Foundation
/// Simplified Adaptive Radix Tree (ART) for UTF‑8 String keys.

// Adaptive Radix Tree (semplificato) per chiavi String (UTF-8).
// MVP con path compression, children mappati da byte -> nodo.

public final class ARTIndex<Ref: Hashable>: IndexProtocol {
    public typealias Key = String
    public typealias Ref = Ref

    final class Node {
        var prefix: [UInt8]
        var children: [UInt8: Node] = [:]
        var refs: TombstoneSet<Ref> = TombstoneSet()
        init(prefix: [UInt8] = []) { self.prefix = prefix }
        var isLeaf: Bool { children.isEmpty }
        var hasLiveRefs: Bool { refs.hasLive }
        var isEmpty: Bool { !refs.hasLive && !refs.hasTombstones && children.isEmpty }
    }

    private let root = Node()
    private var arena: [Node] = []
    private let arenaChunk: Int = 1024
    private var arenaIndex: Int = 0

    public init() {}

    /// Returns all references for an exact key.
    public func searchEquals(_ key: String) throws -> [Ref] {
        let bytes = Array(key.utf8)
        if let node = findNode(bytes) { return node.refs.visible() }
        return []
    }

    /// Returns references for keys within [lo, hi] (inclusive) in lexicographic order.
    public func range(_ lo: String?, _ hi: String?) throws -> [Ref] {
        var acc: [Ref] = []
        var path: [UInt8] = []
        dfs(node: root, path: &path, lo: lo, hi: hi) { ref in
            acc.append(ref)
        }
        // Deduplicate to align with BTree behavior
        return Array(Set(acc))
    }

    /// Inserts a reference for the given key.
    public func insert(_ key: String, _ ref: Ref) throws {
        var bytes = Array(key.utf8)
        insert(bytes: &bytes, ref: ref, node: root)
    }

    /// Removes a specific reference for the given key.
    public func remove(_ key: String, _ ref: Ref) throws {
        var path: [(Node, UInt8?)] = []
        var node = root
        let bytes = Array(key.utf8)
        var i = 0
        while true {
            let common = commonPrefix(node.prefix, bytes, i)
            if common < node.prefix.count { return } // key non presente
            i += common
            if i == bytes.count {
                node.refs.remove(ref)
                // pruning semplice
                prune(&path, last: node)
                return
            }
            let b = bytes[i]
            path.append((node, b))
            guard let child = node.children[b] else { return }
            i += 1
            node = child
        }
    }

    // MARK: - Internals

    private func findNode(_ bytes: [UInt8]) -> Node? {
        var node = root
        var i = 0
        while true {
            let common = commonPrefix(node.prefix, bytes, i)
            if common < node.prefix.count { return nil }
            i += common
            if i == bytes.count { return node }
            let edge = bytes[i]
            guard let child = node.children[edge] else { return nil }
            i += 1
            node = child
        }
    }

    private func insert(bytes: inout [UInt8], ref: Ref, node: Node) {
        var i = 0
        let common = commonPrefix(node.prefix, bytes, 0)
        if common < node.prefix.count {
            // split node
            let suffix = Array(node.prefix[common...])
            let edge = suffix.first!
            let newChild = allocateNode(prefix: Array(suffix.dropFirst()))
            newChild.children = node.children
            newChild.refs = node.refs
            node.children.removeAll()
            node.refs.clearAll()
            node.prefix = Array(node.prefix[..<common])
            node.children[edge] = newChild
        }
        i += common
        if i == bytes.count {
            node.refs.insert(ref)
            return
        }
        let b = bytes[i]
        if let child = node.children[b] {
            var rest = Array(bytes[(i+1)...])
            insert(bytes: &rest, ref: ref, node: child)
        } else {
            // create leaf with remaining bytes as prefix
            let rem = (i + 1) < bytes.count ? Array(bytes[(i+1)..<bytes.count]) : []
            let leaf = allocateNode(prefix: rem)
            leaf.refs.insert(ref)
            node.children[b] = leaf
        }
    }

    // MARK: - Arena allocator (simple bump-pointer style)
    private func allocateNode(prefix: [UInt8]) -> Node {
        if arenaIndex >= arena.count {
            // bulk allocate
            arena.reserveCapacity(arena.count + arenaChunk)
            for _ in 0..<arenaChunk { arena.append(Node()) }
        }
        let n = arena[arenaIndex]
        arenaIndex += 1
        n.prefix = prefix
        n.children.removeAll(keepingCapacity: true)
        n.refs = TombstoneSet()
        return n
    }

    private func prune(_ path: inout [(Node, UInt8?)], last: Node) {
        // Se il nodo è vuoto e ha un solo figlio, comprime; se nessuno, rimuove.
        var current = last
        while let (parent, edge) = path.popLast() {
            if current.isEmpty {
                if let e = edge { parent.children.removeValue(forKey: e) }
                current = parent
            } else if !current.hasLiveRefs && current.children.count == 1, let (k, only) = current.children.first {
                // merge
                current.prefix.append(k)
                current.prefix.append(contentsOf: only.prefix)
                current.children = only.children
                current.refs = only.refs
                current = parent
            } else {
                break
            }
        }
    }

    private func dfs(node: Node, path: inout [UInt8], lo: String?, hi: String?, yield: (Ref) -> Void) {
        // Enter node: include this node's prefix in the path
        if !node.prefix.isEmpty { path.append(contentsOf: node.prefix) }
        // Emit refs for exact key at this node if within range
        let keyStr = String(bytes: path, encoding: .utf8) ?? ""
        if inRange(keyStr, lo: lo, hi: hi) {
            node.refs.visible().forEach(yield)
        }
        // Explore children in byte-sorted order for lexicographic traversal
        if !node.children.isEmpty {
            for edge in node.children.keys.sorted() {
                guard let child = node.children[edge] else { continue }
                path.append(edge)
                dfs(node: child, path: &path, lo: lo, hi: hi, yield: yield)
                _ = path.popLast() // remove edge
            }
        }
        // Exit node: remove this node's prefix
        if !node.prefix.isEmpty {
            for _ in 0..<node.prefix.count { _ = path.popLast() }
        }
    }

    private func inRange(_ key: String, lo: String?, hi: String?) -> Bool {
        if let lo = lo, key < lo { return false }
        if let hi = hi, key > hi { return false }
        return true
    }

    private func commonPrefix(_ a: [UInt8], _ bytes: [UInt8], _ start: Int) -> Int {
        var i = 0
        while i < a.count && start + i < bytes.count && a[i] == bytes[start + i] { i += 1 }
        return i
    }
}

