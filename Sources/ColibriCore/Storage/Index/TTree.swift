//
//  TTree.swift
//  ColibrDB
//
//  Created by AI Assistant on 2025-10-18.
//
// ColibrDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// 🚀 FIX #52: Advanced Data Structures - T-Tree Implementation
// Theme: Cache-friendly in-memory index combining AVL tree with sorted arrays

import Foundation

/// A T-Tree is an in-memory balanced search tree that combines the characteristics of
/// AVL trees and sorted arrays. Each node contains multiple sorted elements rather than
/// just one, making it more cache-friendly than traditional binary search trees.
///
/// **Advantages**:
/// - Cache-friendly: Multiple elements per node reduce cache misses
/// - Space-efficient: Less overhead than traditional trees
/// - Fast range queries: Sequential access within nodes
/// - Good for in-memory databases
///
/// **Use Cases**:
/// - Main-memory databases and indexes
/// - High-performance in-memory sorted maps
/// - Scenarios with frequent range scans
/// - Real-time analytics where data fits in RAM
public final class TTree<Key: Comparable & Sendable, Value: Sendable>: @unchecked Sendable {
    
    // MARK: - Node Structure
    
    private class Node {
        /// Sorted array of key-value pairs in this node
        var elements: [(key: Key, value: Value)]
        
        /// Left child (all keys < min key in this node)
        var left: Node?
        
        /// Right child (all keys > max key in this node)
        var right: Node?
        
        /// Height of the node for AVL balancing
        var height: Int = 1
        
        /// Minimum number of elements per node (except root)
        static var minElements: Int { 4 }
        
        /// Maximum number of elements per node
        static var maxElements: Int { 8 }
        
        init(key: Key, value: Value) {
            self.elements = [(key, value)]
        }
        
        /// Returns the balance factor for AVL balancing
        var balanceFactor: Int {
            let leftHeight = left?.height ?? 0
            let rightHeight = right?.height ?? 0
            return leftHeight - rightHeight
        }
        
        /// Updates the height based on children
        func updateHeight() {
            let leftHeight = left?.height ?? 0
            let rightHeight = right?.height ?? 0
            height = max(leftHeight, rightHeight) + 1
        }
        
        /// Finds a key in this node's elements
        func find(key: Key) -> Value? {
            // Binary search within node
            var low = 0
            var high = elements.count - 1
            
            while low <= high {
                let mid = low + (high - low) / 2
                let midKey = elements[mid].key
                
                if midKey == key {
                    return elements[mid].value
                } else if midKey < key {
                    low = mid + 1
                } else {
                    high = mid - 1
                }
            }
            
            return nil
        }
        
        /// Inserts a key-value pair into this node's sorted array
        func insertElement(key: Key, value: Value) -> Bool {
            // Find insertion point
            var index = 0
            while index < elements.count && elements[index].key < key {
                index += 1
            }
            
            // Update if key exists
            if index < elements.count && elements[index].key == key {
                elements[index].value = value
                return false // No new element added
            }
            
            // Insert new element
            elements.insert((key, value), at: index)
            return true
        }
        
        /// Removes a key from this node's sorted array
        func removeElement(key: Key) -> Value? {
            guard let index = elements.firstIndex(where: { $0.key == key }) else {
                return nil
            }
            
            let value = elements[index].value
            elements.remove(at: index)
            return value
        }
        
        /// Checks if node is overfull
        var isOverfull: Bool {
            return elements.count > Node.maxElements
        }
        
        /// Checks if node is underfull
        var isUnderfull: Bool {
            return elements.count < Node.minElements
        }
        
        /// Returns the minimum key in this node
        var minKey: Key {
            return elements.first!.key
        }
        
        /// Returns the maximum key in this node
        var maxKey: Key {
            return elements.last!.key
        }
    }
    
    // MARK: - Properties
    
    /// Root of the tree
    private var root: Node?
    
    /// Number of key-value pairs in the tree
    private var count: Int = 0
    
    /// Lock for thread-safe operations
    private let lock = NSLock()
    
    // MARK: - Initialization
    
    public init() {
        print("🌳 TTree initialized with node size: \(Node.minElements)-\(Node.maxElements) elements")
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
        
        if root == nil {
            root = Node(key: key, value: value)
            count += 1
            return nil
        }
        
        let (newRoot, oldValue, inserted) = insertRecursive(node: root, key: key, value: value)
        root = newRoot
        
        if inserted {
            count += 1
        }
        
        return oldValue
    }
    
    /// Searches for a value by key
    ///
    /// - Parameter key: Key to search for
    /// - Returns: Value if found, nil otherwise
    public func search(key: Key) -> Value? {
        lock.lock()
        defer { lock.unlock() }
        
        return searchRecursive(node: root, key: key)
    }
    
    /// Deletes a key-value pair
    ///
    /// - Parameter key: Key to delete
    /// - Returns: Deleted value if found, nil otherwise
    @discardableResult
    public func delete(key: Key) -> Value? {
        lock.lock()
        defer { lock.unlock() }
        
        guard root != nil else { return nil }
        
        let (newRoot, deletedValue) = deleteRecursive(node: root, key: key)
        root = newRoot
        
        if deletedValue != nil {
            count -= 1
        }
        
        return deletedValue
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
        rangeRecursive(node: root, start: start, end: end, results: &results)
        return results
    }
    
    /// Returns all key-value pairs in sorted order
    public func all() -> [(key: Key, value: Value)] {
        lock.lock()
        defer { lock.unlock() }
        
        var results: [(Key, Value)] = []
        inOrderTraversal(node: root, results: &results)
        return results
    }
    
    /// Returns the number of key-value pairs in the tree
    public var size: Int {
        lock.lock()
        defer { lock.unlock() }
        return count
    }
    
    /// Checks if the tree is empty
    public var isEmpty: Bool {
        lock.lock()
        defer { lock.unlock() }
        return root == nil
    }
    
    /// Removes all elements from the tree
    public func clear() {
        lock.lock()
        defer { lock.unlock() }
        
        root = nil
        count = 0
    }
    
    /// Returns statistics about the tree
    public func statistics() -> TTreeStatistics {
        lock.lock()
        defer { lock.unlock() }
        
        guard let root = root else {
            return TTreeStatistics(
                elementCount: 0,
                nodeCount: 0,
                height: 0,
                averageElementsPerNode: 0.0,
                minElementsPerNode: 0,
                maxElementsPerNode: 0
            )
        }
        
        var nodeCount = 0
        var totalElements = 0
        var minElements = Int.max
        var maxElements = 0
        
        func traverse(_ node: Node?) {
            guard let node = node else { return }
            
            nodeCount += 1
            totalElements += node.elements.count
            minElements = min(minElements, node.elements.count)
            maxElements = max(maxElements, node.elements.count)
            
            traverse(node.left)
            traverse(node.right)
        }
        
        traverse(root)
        
        return TTreeStatistics(
            elementCount: count,
            nodeCount: nodeCount,
            height: root.height,
            averageElementsPerNode: Double(totalElements) / Double(nodeCount),
            minElementsPerNode: minElements,
            maxElementsPerNode: maxElements
        )
    }
    
    // MARK: - Private Methods - Insertion
    
    private func insertRecursive(node: Node?, key: Key, value: Value) -> (node: Node?, oldValue: Value?, inserted: Bool) {
        guard let node = node else {
            return (Node(key: key, value: value), nil, true)
        }
        
        // Check if key belongs in current node's range
        if key < node.minKey {
            // Insert in left subtree
            let (newLeft, oldValue, inserted) = insertRecursive(node: node.left, key: key, value: value)
            node.left = newLeft
            node.updateHeight()
            return (balance(node), oldValue, inserted)
            
        } else if key > node.maxKey {
            // Insert in right subtree
            let (newRight, oldValue, inserted) = insertRecursive(node: node.right, key: key, value: value)
            node.right = newRight
            node.updateHeight()
            return (balance(node), oldValue, inserted)
            
        } else {
            // Key belongs in this node
            let wasInserted = node.insertElement(key: key, value: value)
            
            // Split node if overfull
            if node.isOverfull {
                let splitNode = split(node)
                return (splitNode, nil, wasInserted)
            }
            
            return (node, wasInserted ? nil : value, wasInserted)
        }
    }
    
    /// Splits an overfull node into two nodes
    private func split(_ node: Node) -> Node {
        let mid = node.elements.count / 2
        let leftElements = Array(node.elements[..<mid])
        let rightElements = Array(node.elements[mid...])
        
        let leftNode = Node(key: leftElements[0].key, value: leftElements[0].value)
        leftNode.elements = leftElements
        leftNode.left = node.left
        
        let rightNode = Node(key: rightElements[0].key, value: rightElements[0].value)
        rightNode.elements = rightElements
        rightNode.right = node.right
        
        // Create new parent node
        let parentKey = rightElements[0].key
        let parentValue = rightElements[0].value
        let parent = Node(key: parentKey, value: parentValue)
        parent.elements = [rightElements[0]]
        parent.left = leftNode
        parent.right = rightNode
        
        // Update heights
        leftNode.updateHeight()
        rightNode.updateHeight()
        parent.updateHeight()
        
        return parent
    }
    
    // MARK: - Private Methods - Deletion
    
    private func deleteRecursive(node: Node?, key: Key) -> (node: Node?, deletedValue: Value?) {
        guard let node = node else {
            return (nil, nil)
        }
        
        // Check if key is in current node
        if node.find(key: key) != nil {
            let removed = node.removeElement(key: key)
            
            // Handle underfull node
            if node.elements.isEmpty {
                // Node is empty, need to remove it
                return (mergeChildren(node), removed)
            }
            
            return (node, removed)
        }
        
        // Search in subtrees
        if key < node.minKey {
            let (newLeft, deleted) = deleteRecursive(node: node.left, key: key)
            node.left = newLeft
            node.updateHeight()
            return (balance(node), deleted)
        } else {
            let (newRight, deleted) = deleteRecursive(node: node.right, key: key)
            node.right = newRight
            node.updateHeight()
            return (balance(node), deleted)
        }
    }
    
    /// Merges children when a node becomes empty
    private func mergeChildren(_ node: Node) -> Node? {
        if node.left == nil {
            return node.right
        }
        if node.right == nil {
            return node.left
        }
        
        // Both children exist - merge them
        let successor = findMin(node.right!)
        successor.left = node.left
        successor.updateHeight()
        return balance(successor)
    }
    
    private func findMin(_ node: Node) -> Node {
        var current = node
        while let left = current.left {
            current = left
        }
        return current
    }
    
    // MARK: - Private Methods - AVL Balancing
    
    private func balance(_ node: Node) -> Node {
        let factor = node.balanceFactor
        
        // Left heavy
        if factor > 1 {
            if let left = node.left, left.balanceFactor < 0 {
                node.left = rotateLeft(left)
            }
            return rotateRight(node)
        }
        
        // Right heavy
        if factor < -1 {
            if let right = node.right, right.balanceFactor > 0 {
                node.right = rotateRight(right)
            }
            return rotateLeft(node)
        }
        
        return node
    }
    
    private func rotateLeft(_ node: Node) -> Node {
        guard let newRoot = node.right else { return node }
        
        node.right = newRoot.left
        newRoot.left = node
        
        node.updateHeight()
        newRoot.updateHeight()
        
        return newRoot
    }
    
    private func rotateRight(_ node: Node) -> Node {
        guard let newRoot = node.left else { return node }
        
        node.left = newRoot.right
        newRoot.right = node
        
        node.updateHeight()
        newRoot.updateHeight()
        
        return newRoot
    }
    
    // MARK: - Private Methods - Search & Traversal
    
    private func searchRecursive(node: Node?, key: Key) -> Value? {
        guard let node = node else { return nil }
        
        // Check if key is in this node
        if key >= node.minKey && key <= node.maxKey {
            return node.find(key: key)
        }
        
        // Search in appropriate subtree
        if key < node.minKey {
            return searchRecursive(node: node.left, key: key)
        } else {
            return searchRecursive(node: node.right, key: key)
        }
    }
    
    private func rangeRecursive(node: Node?, start: Key, end: Key, results: inout [(Key, Value)]) {
        guard let node = node else { return }
        
        // Traverse left if range might overlap
        if start < node.minKey {
            rangeRecursive(node: node.left, start: start, end: end, results: &results)
        }
        
        // Add elements from this node that are in range
        for (key, value) in node.elements {
            if key >= start && key <= end {
                results.append((key, value))
            }
        }
        
        // Traverse right if range might overlap
        if end > node.maxKey {
            rangeRecursive(node: node.right, start: start, end: end, results: &results)
        }
    }
    
    private func inOrderTraversal(node: Node?, results: inout [(Key, Value)]) {
        guard let node = node else { return }
        
        inOrderTraversal(node: node.left, results: &results)
        results.append(contentsOf: node.elements)
        inOrderTraversal(node: node.right, results: &results)
    }
}

// MARK: - Statistics

/// Statistics about a T-Tree's current state
public struct TTreeStatistics {
    /// Total number of key-value pairs
    public let elementCount: Int
    
    /// Number of nodes in the tree
    public let nodeCount: Int
    
    /// Height of the tree
    public let height: Int
    
    /// Average number of elements per node
    public let averageElementsPerNode: Double
    
    /// Minimum elements in any node
    public let minElementsPerNode: Int
    
    /// Maximum elements in any node
    public let maxElementsPerNode: Int
    
    public var description: String {
        """
        TTree Statistics:
        - Elements: \(elementCount)
        - Nodes: \(nodeCount)
        - Height: \(height)
        - Elements per node: \(String(format: "%.1f", averageElementsPerNode)) avg (min: \(minElementsPerNode), max: \(maxElementsPerNode))
        - Space efficiency: \(String(format: "%.1f", averageElementsPerNode)) elements/node
        """
    }
}

// MARK: - Database Integration

extension TTree where Key == String, Value == RID {
    
    /// Creates a T-Tree optimized for string keys (in-memory index)
    public static func forStringIndex() -> TTree<String, RID> {
        return TTree<String, RID>()
    }
}

extension TTree where Key == Int, Value == RID {
    
    /// Creates a T-Tree optimized for integer keys (in-memory index)
    public static func forIntegerIndex() -> TTree<Int, RID> {
        return TTree<Int, RID>()
    }
}

