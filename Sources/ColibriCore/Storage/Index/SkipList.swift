//
//  SkipList.swift
//  ColibrDB
//
//  Created by AI Assistant on 2025-10-18.
//
// ColibrDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// 🚀 FIX #52: Advanced Data Structures - Skip List Implementation
// Theme: Probabilistic balanced search structure with excellent concurrency

import Foundation

/// A Skip List is a probabilistic data structure that allows O(log n) search complexity
/// as well as O(log n) insertion complexity within an ordered sequence of elements.
///
/// **Advantages over B+Trees**:
/// - Simpler implementation (no complex rebalancing)
/// - Better for concurrent access (less lock contention)
/// - Predictable performance (no worst-case rebalancing)
/// - Easy to understand and debug
///
/// **Use Cases**:
/// - In-memory indexes with concurrent access
/// - Range queries with frequent updates
/// - Sorted sets and maps
/// - Alternative to B+Trees for smaller datasets
public final class SkipList<Key: Comparable & Sendable, Value: Sendable>: @unchecked Sendable {
    
    // MARK: - Node Structure
    
    private class Node {
        let key: Key
        var value: Value?
        var forward: [Node?]
        
        init(key: Key, value: Value?, level: Int) {
            self.key = key
            self.value = value
            self.forward = Array(repeating: nil, count: level + 1)
        }
    }
    
    // MARK: - Properties
    
    /// Maximum level of the skip list
    private let maxLevel: Int
    
    /// Probability factor for level generation (typically 0.25 or 0.5)
    private let probability: Double
    
    /// Current level of the skip list
    private var level: Int = 0
    
    /// Head sentinel node
    private let head: Node
    
    /// Number of elements in the skip list
    private var count: Int = 0
    
    /// Lock for thread-safe operations
    private let lock = NSLock()
    
    // MARK: - Initialization
    
    /// Creates a new skip list
    ///
    /// - Parameters:
    ///   - maxLevel: Maximum level of the skip list (default 16, suitable for ~65K elements)
    ///   - probability: Probability of promoting to next level (default 0.25)
    public init(maxLevel: Int = 16, probability: Double = 0.25) {
        self.maxLevel = maxLevel
        self.probability = probability
        
        // Create head sentinel with minimum possible key
        // We use a dummy key value that won't be used
        self.head = Node(key: Key.self == Int.self ? 0 as! Key : "" as! Key, value: nil, level: maxLevel)
        
        print("⛷️ SkipList initialized: maxLevel=\(maxLevel), probability=\(probability)")
    }
    
    // MARK: - Public API
    
    /// Inserts or updates a key-value pair
    ///
    /// - Parameters:
    ///   - key: Key to insert
    ///   - value: Value to associate with the key
    /// - Returns: Previous value if key existed, nil otherwise
    @discardableResult
    public func insert(key: Key, value: Value) -> Value? {
        lock.lock()
        defer { lock.unlock() }
        
        var update = Array(repeating: head, count: maxLevel + 1)
        var current: Node? = head
        
        // Find position to insert
        for i in stride(from: level, through: 0, by: -1) {
            while let next = current?.forward[i], next.key < key {
                current = next
            }
            update[i] = current!
        }
        
        current = current?.forward[0]
        
        // Key already exists - update value
        if let node = current, node.key == key {
            let oldValue = node.value
            node.value = value
            return oldValue
        }
        
        // Insert new node
        let newLevel = randomLevel()
        
        if newLevel > level {
            for i in (level + 1)...newLevel {
                update[i] = head
            }
            level = newLevel
        }
        
        let newNode = Node(key: key, value: value, level: newLevel)
        
        for i in 0...newLevel {
            newNode.forward[i] = update[i].forward[i]
            update[i].forward[i] = newNode
        }
        
        count += 1
        return nil
    }
    
    /// Searches for a value by key
    ///
    /// - Parameter key: Key to search for
    /// - Returns: Value if found, nil otherwise
    public func search(key: Key) -> Value? {
        lock.lock()
        defer { lock.unlock() }
        
        var current: Node? = head
        
        for i in stride(from: level, through: 0, by: -1) {
            while let next = current?.forward[i], next.key < key {
                current = next
            }
        }
        
        current = current?.forward[0]
        
        if let node = current, node.key == key {
            return node.value
        }
        
        return nil
    }
    
    /// Deletes a key-value pair
    ///
    /// - Parameter key: Key to delete
    /// - Returns: Deleted value if found, nil otherwise
    @discardableResult
    public func delete(key: Key) -> Value? {
        lock.lock()
        defer { lock.unlock() }
        
        var update = Array(repeating: head, count: maxLevel + 1)
        var current: Node? = head
        
        // Find node to delete
        for i in stride(from: level, through: 0, by: -1) {
            while let next = current?.forward[i], next.key < key {
                current = next
            }
            update[i] = current!
        }
        
        current = current?.forward[0]
        
        guard let node = current, node.key == key else {
            return nil
        }
        
        // Remove node by updating forward pointers
        for i in 0...level {
            if update[i].forward[i] === node {
                update[i].forward[i] = node.forward[i]
            }
        }
        
        // Update level if necessary
        while level > 0 && head.forward[level] == nil {
            level -= 1
        }
        
        count -= 1
        return node.value
    }
    
    /// Performs a range query
    ///
    /// - Parameters:
    ///   - start: Start key (inclusive)
    ///   - end: End key (inclusive)
    /// - Returns: Array of key-value pairs in the range
    public func range(from start: Key, to end: Key) -> [(key: Key, value: Value)] {
        lock.lock()
        defer { lock.unlock() }
        
        var results: [(Key, Value)] = []
        var current: Node? = head
        
        // Find start position
        for i in stride(from: level, through: 0, by: -1) {
            while let next = current?.forward[i], next.key < start {
                current = next
            }
        }
        
        current = current?.forward[0]
        
        // Collect all nodes in range
        while let node = current, node.key <= end {
            if let value = node.value {
                results.append((node.key, value))
            }
            current = node.forward[0]
        }
        
        return results
    }
    
    /// Returns the minimum key-value pair
    public func min() -> (key: Key, value: Value)? {
        lock.lock()
        defer { lock.unlock() }
        
        guard let first = head.forward[0], let value = first.value else {
            return nil
        }
        
        return (first.key, value)
    }
    
    /// Returns the maximum key-value pair
    public func max() -> (key: Key, value: Value)? {
        lock.lock()
        defer { lock.unlock() }
        
        var current = head
        
        for i in stride(from: level, through: 0, by: -1) {
            while let next = current.forward[i] {
                current = next
            }
        }
        
        guard current !== head, let value = current.value else {
            return nil
        }
        
        return (current.key, value)
    }
    
    /// Returns all key-value pairs in sorted order
    public func all() -> [(key: Key, value: Value)] {
        lock.lock()
        defer { lock.unlock() }
        
        var results: [(Key, Value)] = []
        var current = head.forward[0]
        
        while let node = current {
            if let value = node.value {
                results.append((node.key, value))
            }
            current = node.forward[0]
        }
        
        return results
    }
    
    /// Returns the number of elements in the skip list
    public var size: Int {
        lock.lock()
        defer { lock.unlock() }
        return count
    }
    
    /// Checks if the skip list is empty
    public var isEmpty: Bool {
        lock.lock()
        defer { lock.unlock() }
        return count == 0
    }
    
    /// Removes all elements from the skip list
    public func clear() {
        lock.lock()
        defer { lock.unlock() }
        
        for i in 0...level {
            head.forward[i] = nil
        }
        
        level = 0
        count = 0
    }
    
    /// Returns statistics about the skip list
    public func statistics() -> SkipListStatistics {
        lock.lock()
        defer { lock.unlock() }
        
        // Count nodes at each level
        var levelCounts = Array(repeating: 0, count: level + 1)
        var current = head.forward[0]
        
        while let node = current {
            for i in 0..<node.forward.count {
                if node.forward[i] != nil {
                    levelCounts[i] += 1
                }
            }
            current = node.forward[0]
        }
        
        return SkipListStatistics(
            elementCount: count,
            currentLevel: level,
            maxLevel: maxLevel,
            levelCounts: levelCounts,
            averageLevel: levelCounts.enumerated().reduce(0) { $0 + $1.element * $1.offset } / Swift.max(1, count)
        )
    }
    
    // MARK: - Private Methods
    
    /// Generates a random level for a new node
    ///
    /// Uses geometric distribution with parameter p (probability)
    private func randomLevel() -> Int {
        var lvl = 0
        
        while Double.random(in: 0...1) < probability && lvl < maxLevel {
            lvl += 1
        }
        
        return lvl
    }
}

// MARK: - Statistics

/// Statistics about a skip list's current state
public struct SkipListStatistics {
    /// Number of elements in the skip list
    public let elementCount: Int
    
    /// Current maximum level in use
    public let currentLevel: Int
    
    /// Maximum possible level
    public let maxLevel: Int
    
    /// Number of nodes at each level
    public let levelCounts: [Int]
    
    /// Average level of nodes
    public let averageLevel: Int
    
    public var description: String {
        var result = """
        SkipList Statistics:
        - Elements: \(elementCount)
        - Current Level: \(currentLevel)/\(maxLevel)
        - Average Level: \(averageLevel)
        - Level Distribution:
        """
        
        for (level, count) in levelCounts.enumerated() {
            result += "\n  Level \(level): \(count) nodes"
        }
        
        return result
    }
}

// MARK: - Iterator Support

extension SkipList: Sequence {
    public func makeIterator() -> SkipListIterator<Key, Value> {
        return SkipListIterator(skipList: self)
    }
}

public struct SkipListIterator<Key: Comparable & Sendable, Value: Sendable>: IteratorProtocol {
    private let elements: [(key: Key, value: Value)]
    private var index = 0
    
    init(skipList: SkipList<Key, Value>) {
        self.elements = skipList.all()
    }
    
    public mutating func next() -> (key: Key, value: Value)? {
        guard index < elements.count else { return nil }
        let element = elements[index]
        index += 1
        return element
    }
}

// MARK: - Database Integration

extension SkipList where Key == String, Value == RID {
    
    /// Creates a skip list optimized for string keys (index entries)
    ///
    /// - Parameter estimatedSize: Estimated number of entries
    /// - Returns: Skip list with appropriate max level
    public static func forStringIndex(estimatedSize: Int) -> SkipList<String, RID> {
        // Calculate max level based on expected size: maxLevel = log(n) / log(1/p)
        let maxLevel = Swift.max(4, Int(ceil(log(Double(estimatedSize)) / log(4.0))))
        return SkipList<String, RID>(maxLevel: maxLevel, probability: 0.25)
    }
}

extension SkipList where Key == Int, Value == RID {
    
    /// Creates a skip list optimized for integer keys (index entries)
    ///
    /// - Parameter estimatedSize: Estimated number of entries
    /// - Returns: Skip list with appropriate max level
    public static func forIntegerIndex(estimatedSize: Int) -> SkipList<Int, RID> {
        let maxLevel = Swift.max(4, Int(ceil(log(Double(estimatedSize)) / log(4.0))))
        return SkipList<Int, RID>(maxLevel: maxLevel, probability: 0.25)
    }
}

