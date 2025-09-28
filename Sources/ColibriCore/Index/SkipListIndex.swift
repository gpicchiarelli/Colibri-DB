//
//  SkipListIndex.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrìDB — BSD 3-Clause License

// Theme: Skip list playground offering probabilistic indexing.

import Foundation

public final class SkipListIndex<Element: Hashable & Comparable, Reference: Hashable>: IndexProtocol {
    public typealias Key = Element
    public typealias Ref = Reference

    private final class Node {
        let key: Key?
        var refs: TombstoneSet<Ref>
        var next: [Node?]
        init(key: Key?, level: Int) {
            self.key = key
            self.refs = TombstoneSet()
            self.next = Array(repeating: nil, count: level)
        }
        var hasLive: Bool { refs.hasLive }
    }

    private let maxLevel: Int
    private var head: Node
    private var level: Int

    public init(maxLevel: Int = 12) {
        self.maxLevel = max(2, maxLevel)
        self.level = 1
        self.head = Node(key: nil, level: self.maxLevel)
    }

    private func randomLevel() -> Int {
        var lvl = 1
        while lvl < maxLevel && Int.random(in: 0..<2) == 0 { lvl &+= 1 }
        return lvl
    }

    public func insert(_ key: Key, _ ref: Ref) throws {
        var update = Array<Node?>(repeating: nil, count: maxLevel)
        var x: Node? = head
        for i in stride(from: level - 1, through: 0, by: -1) {
            while let next = x?.next[i], let nextKey = next.key, nextKey < key { x = next }
            update[i] = x
        }
        x = x?.next[0]
        if let node = x, node.key == key {
            node.refs.insert(ref)
            return
        }
        let lvl = randomLevel()
        if lvl > level {
            for i in level..<lvl { update[i] = head }
            level = lvl
        }
        let node = Node(key: key, level: lvl)
        node.refs.insert(ref)
        for i in 0..<lvl {
            node.next[i] = update[i]?.next[i]
            update[i]?.next[i] = node
        }
    }

    public func searchEquals(_ key: Key) throws -> [Ref] {
        var x: Node? = head
        for i in stride(from: level - 1, through: 0, by: -1) {
            while let next = x?.next[i], let nextKey = next.key, nextKey < key { x = next }
        }
        x = x?.next[0]
        if let node = x, node.key == key {
            return node.refs.visible()
        }
        return []
    }

    public func range(_ lo: Key?, _ hi: Key?) throws -> [Ref] {
        var result: [Ref] = []
        var x: Node? = head
        if let lo = lo {
            for i in stride(from: level - 1, through: 0, by: -1) {
                while let next = x?.next[i], let nextKey = next.key, nextKey < lo { x = next }
            }
            x = x?.next[0]
        } else {
            x = x?.next[0]
        }
        while let node = x {
            guard let nodeKey = node.key else { break }
            if let hi = hi, nodeKey > hi { break }
            result.append(contentsOf: node.refs.visible())
            x = node.next[0]
        }
        return result
    }

    public func remove(_ key: Key, _ ref: Ref) throws {
        var update = Array<Node?>(repeating: nil, count: maxLevel)
        var x: Node? = head
        for i in stride(from: level - 1, through: 0, by: -1) {
            while let next = x?.next[i], let nextKey = next.key, nextKey < key { x = next }
            update[i] = x
        }
        x = x?.next[0]
        if let node = x, node.key == key {
            node.refs.remove(ref)
        }
    }
}


