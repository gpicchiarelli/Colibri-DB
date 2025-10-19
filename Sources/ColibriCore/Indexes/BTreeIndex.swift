//
//  BTreeIndex.swift
//  ColibrìDB B+Tree Index Implementation
//
//  Based on: spec/BTree.tla
//  Implements: B+Tree with insert, search, delete, range scan
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//
//  Key Properties:
//  - Structure Invariant: All nodes satisfy B+Tree properties
//  - Key Order: Keys maintain sorted order
//  - Balanced Height: All leaves at same height
//  - Link Consistency: Leaf sibling pointers correct
//
//  Based on: "The Ubiquitous B-Tree" (Comer, 1979)
//

import Foundation

// MARK: - B+Tree Node

/// B+Tree node structure
/// Corresponds to TLA+: Node
private class BTreeNode {
    var keys: [Value] = []
    var children: [BTreeNode] = []  // For internal nodes
    var rids: [[RID]] = []  // For leaf nodes
    var isLeaf: Bool
    var next: BTreeNode?  // Next leaf pointer
    weak var parent: BTreeNode?
    
    init(isLeaf: Bool) {
        self.isLeaf = isLeaf
    }
    
    var isFull: Bool {
        return keys.count >= 2 * BTreeIndex.minDegree - 1
    }
    
    var isMinimum: Bool {
        return keys.count <= BTreeIndex.minDegree - 1
    }
}

// MARK: - B+Tree Index

/// B+Tree Index implementation
/// Corresponds to TLA+ module: BTree.tla
public actor BTreeIndex {
    // MARK: - Configuration
    
    /// Minimum degree (node has [t-1, 2t-1] keys)
    /// TLA+: MIN_DEGREE
    static let minDegree = 3
    
    // MARK: - State Variables (TLA+ vars)
    
    /// Root node
    /// TLA+: root \in PageIds
    private var root: BTreeNode
    
    /// Tree height
    /// TLA+: height \in Nat
    private var height: Int
    
    /// Next node ID (for tracking)
    /// TLA+: nextNodeId \in PageIds
    private var nextNodeId: Int
    
    // MARK: - Initialization
    
    public init() {
        // TLA+ Init
        self.root = BTreeNode(isLeaf: true)
        self.height = 1
        self.nextNodeId = 2
    }
    
    // MARK: - Core Operations
    
    /// Insert a key-RID pair into B+Tree
    /// TLA+ Action: Insert(key, rid)
    /// Precondition: key and rid are valid
    /// Postcondition: key inserted, tree remains balanced
    public func insert(key: Value, rid: RID) throws {
        // If root is full, split it
        if root.isFull {
            let newRoot = BTreeNode(isLeaf: false)
            newRoot.children.append(root)
            root.parent = newRoot
            try splitChild(parent: newRoot, index: 0)
            root = newRoot
            height += 1
        }
        
        // Insert into non-full root
        try insertNonFull(node: root, key: key, rid: rid)
    }
    
    /// Search for a key in B+Tree
    /// TLA+ Action: Search(key)
    /// Precondition: key is valid
    /// Postcondition: returns RIDs if found, nil otherwise
    public func search(key: Value) -> [RID]? {
        return searchNode(node: root, key: key)
    }
    
    /// Delete a key from B+Tree
    /// TLA+ Action: Delete(key)
    /// Precondition: key exists in tree
    /// Postcondition: key deleted, tree remains balanced
    public func delete(key: Value) throws {
        try deleteFromNode(node: root, key: key)
        
        // If root is empty and has children, make first child the new root
        if !root.isLeaf && root.keys.isEmpty {
            if !root.children.isEmpty {
                root = root.children[0]
                root.parent = nil
                height -= 1
            }
        }
    }
    
    /// Range scan: find all keys in range [minKey, maxKey]
    /// TLA+ Action: RangeScan(minKey, maxKey)
    /// Precondition: minKey <= maxKey
    /// Postcondition: returns all RIDs for keys in range
    public func rangeScan(minKey: Value, maxKey: Value) -> [(Value, [RID])] {
        var results: [(Value, [RID])] = []
        
        // Find leftmost leaf containing minKey or greater
        guard let leafNode = findLeafNode(forKey: minKey) else {
            return results
        }
        
        // Scan through leaves following next pointers
        var currentLeaf: BTreeNode? = leafNode
        
        while let leaf = currentLeaf {
            for (index, key) in leaf.keys.enumerated() {
                if key >= minKey && key <= maxKey {
                    results.append((key, leaf.rids[index]))
                } else if key > maxKey {
                    // We've passed the range
                    return results
                }
            }
            
            // Move to next leaf
            currentLeaf = leaf.next
        }
        
        return results
    }
    
    // MARK: - Private Helper Methods
    
    /// Insert into a non-full node
    private func insertNonFull(node: BTreeNode, key: Value, rid: RID) throws {
        if node.isLeaf {
            // Insert key into leaf node
            let pos = findInsertPosition(keys: node.keys, key: key)
            node.keys.insert(key, at: pos)
            node.rids.insert([rid], at: pos)
        } else {
            // Find child to recurse into
            let pos = findChildIndex(keys: node.keys, key: key)
            let child = node.children[pos]
            
            // Split child if full
            if child.isFull {
                try splitChild(parent: node, index: pos)
                
                // After split, determine which child to recurse into
                if key > node.keys[pos] {
                    try insertNonFull(node: node.children[pos + 1], key: key, rid: rid)
                } else {
                    try insertNonFull(node: node.children[pos], key: key, rid: rid)
                }
            } else {
                try insertNonFull(node: child, key: key, rid: rid)
            }
        }
    }
    
    /// Split a full child node
    /// TLA+: SplitNode(nid)
    private func splitChild(parent: BTreeNode, index: Int) throws {
        let child = parent.children[index]
        let mid = Self.minDegree
        
        // Create new node
        let newNode = BTreeNode(isLeaf: child.isLeaf)
        newNode.parent = parent
        
        // Split keys
        let promotedKey = child.keys[mid - 1]
        newNode.keys = Array(child.keys[mid...])
        child.keys = Array(child.keys[0..<(mid - 1)])
        
        if child.isLeaf {
            // Split leaf node
            newNode.rids = Array(child.rids[mid...])
            child.rids = Array(child.rids[0..<(mid - 1)])
            
            // Update leaf links
            newNode.next = child.next
            child.next = newNode
        } else {
            // Split internal node
            newNode.children = Array(child.children[mid...])
            child.children = Array(child.children[0..<mid])
            
            // Update parent pointers
            for grandchild in newNode.children {
                grandchild.parent = newNode
            }
        }
        
        // Insert promoted key and new child into parent
        parent.keys.insert(promotedKey, at: index)
        parent.children.insert(newNode, at: index + 1)
        
        nextNodeId += 1
    }
    
    /// Search for a key in a subtree
    private func searchNode(node: BTreeNode, key: Value) -> [RID]? {
        if node.isLeaf {
            // Search in leaf
            if let index = node.keys.firstIndex(of: key) {
                return node.rids[index]
            }
            return nil
        } else {
            // Search in internal node
            let childIndex = findChildIndex(keys: node.keys, key: key)
            return searchNode(node: node.children[childIndex], key: key)
        }
    }
    
    /// Delete a key from a subtree
    private func deleteFromNode(node: BTreeNode, key: Value) throws {
        if node.isLeaf {
            // Delete from leaf
            if let index = node.keys.firstIndex(of: key) {
                node.keys.remove(at: index)
                node.rids.remove(at: index)
            } else {
                throw DBError.notFound
            }
        } else {
            // Delete from internal node
            let childIndex = findChildIndex(keys: node.keys, key: key)
            let child = node.children[childIndex]
            
            // Ensure child has at least minDegree keys
            if child.keys.count < Self.minDegree {
                try rebalanceChild(parent: node, index: childIndex)
            }
            
            try deleteFromNode(node: child, key: key)
        }
    }
    
    /// Rebalance a child that has too few keys
    private func rebalanceChild(parent: BTreeNode, index: Int) throws {
        let child = parent.children[index]
        
        // Try borrowing from left sibling
        if index > 0 {
            let leftSibling = parent.children[index - 1]
            if leftSibling.keys.count >= Self.minDegree {
                try borrowFromLeft(parent: parent, childIndex: index)
                return
            }
        }
        
        // Try borrowing from right sibling
        if index < parent.children.count - 1 {
            let rightSibling = parent.children[index + 1]
            if rightSibling.keys.count >= Self.minDegree {
                try borrowFromRight(parent: parent, childIndex: index)
                return
            }
        }
        
        // Merge with sibling
        if index > 0 {
            try mergeWithLeft(parent: parent, childIndex: index)
        } else if index < parent.children.count - 1 {
            try mergeWithRight(parent: parent, childIndex: index)
        }
    }
    
    /// Borrow a key from left sibling
    private func borrowFromLeft(parent: BTreeNode, childIndex: Int) throws {
        let child = parent.children[childIndex]
        let leftSibling = parent.children[childIndex - 1]
        
        // Move key from parent to child
        child.keys.insert(parent.keys[childIndex - 1], at: 0)
        
        // Move key from left sibling to parent
        parent.keys[childIndex - 1] = leftSibling.keys.removeLast()
        
        if child.isLeaf {
            child.rids.insert(leftSibling.rids.removeLast(), at: 0)
        } else {
            child.children.insert(leftSibling.children.removeLast(), at: 0)
            child.children[0].parent = child
        }
    }
    
    /// Borrow a key from right sibling
    private func borrowFromRight(parent: BTreeNode, childIndex: Int) throws {
        let child = parent.children[childIndex]
        let rightSibling = parent.children[childIndex + 1]
        
        // Move key from parent to child
        child.keys.append(parent.keys[childIndex])
        
        // Move key from right sibling to parent
        parent.keys[childIndex] = rightSibling.keys.removeFirst()
        
        if child.isLeaf {
            child.rids.append(rightSibling.rids.removeFirst())
        } else {
            child.children.append(rightSibling.children.removeFirst())
            child.children.last!.parent = child
        }
    }
    
    /// Merge child with left sibling
    private func mergeWithLeft(parent: BTreeNode, childIndex: Int) throws {
        let child = parent.children[childIndex]
        let leftSibling = parent.children[childIndex - 1]
        
        // Move parent key down
        leftSibling.keys.append(parent.keys[childIndex - 1])
        
        // Merge child into left sibling
        leftSibling.keys.append(contentsOf: child.keys)
        
        if child.isLeaf {
            leftSibling.rids.append(contentsOf: child.rids)
            leftSibling.next = child.next
        } else {
            leftSibling.children.append(contentsOf: child.children)
            for grandchild in child.children {
                grandchild.parent = leftSibling
            }
        }
        
        // Remove key and child from parent
        parent.keys.remove(at: childIndex - 1)
        parent.children.remove(at: childIndex)
    }
    
    /// Merge child with right sibling
    private func mergeWithRight(parent: BTreeNode, childIndex: Int) throws {
        let child = parent.children[childIndex]
        let rightSibling = parent.children[childIndex + 1]
        
        // Move parent key down
        child.keys.append(parent.keys[childIndex])
        
        // Merge right sibling into child
        child.keys.append(contentsOf: rightSibling.keys)
        
        if child.isLeaf {
            child.rids.append(contentsOf: rightSibling.rids)
            child.next = rightSibling.next
        } else {
            child.children.append(contentsOf: rightSibling.children)
            for grandchild in rightSibling.children {
                grandchild.parent = child
            }
        }
        
        // Remove key and child from parent
        parent.keys.remove(at: childIndex)
        parent.children.remove(at: childIndex + 1)
    }
    
    /// Find leaf node that should contain key
    private func findLeafNode(forKey key: Value) -> BTreeNode? {
        var current = root
        
        while !current.isLeaf {
            let childIndex = findChildIndex(keys: current.keys, key: key)
            current = current.children[childIndex]
        }
        
        return current
    }
    
    /// Find insert position for key in sorted array
    /// TLA+: FindInsertPos(keys, key)
    private func findInsertPosition(keys: [Value], key: Value) -> Int {
        return keys.firstIndex(where: { $0 >= key }) ?? keys.count
    }
    
    /// Find child index to follow for key
    private func findChildIndex(keys: [Value], key: Value) -> Int {
        for (index, nodeKey) in keys.enumerated() {
            if key < nodeKey {
                return index
            }
        }
        return keys.count
    }
    
    // MARK: - Query Methods
    
    /// Get tree height
    public func getHeight() -> Int {
        return height
    }
    
    /// Get total number of keys (for statistics)
    public func getKeyCount() -> Int {
        return countKeys(node: root)
    }
    
    private func countKeys(node: BTreeNode) -> Int {
        if node.isLeaf {
            return node.keys.count
        } else {
            var count = node.keys.count
            for child in node.children {
                count += countKeys(node: child)
            }
            return count
        }
    }
    
    // MARK: - Invariant Checking (for testing)
    
    /// Check key order invariant
    /// TLA+: Inv_BTree_KeyOrder
    public func checkKeyOrderInvariant() -> Bool {
        return checkKeyOrderInNode(node: root)
    }
    
    private func checkKeyOrderInNode(node: BTreeNode) -> Bool {
        // Check keys are sorted
        for i in 0..<(node.keys.count - 1) {
            if node.keys[i] >= node.keys[i + 1] {
                return false
            }
        }
        
        // Recurse into children
        if !node.isLeaf {
            for child in node.children {
                if !checkKeyOrderInNode(node: child) {
                    return false
                }
            }
        }
        
        return true
    }
    
    /// Check balanced height invariant
    /// TLA+: Inv_BTree_BalancedHeight
    public func checkBalancedHeightInvariant() -> Bool {
        let leafDepths = collectLeafDepths(node: root, depth: 0)
        let uniqueDepths = Set(leafDepths)
        return uniqueDepths.count == 1
    }
    
    private func collectLeafDepths(node: BTreeNode, depth: Int) -> [Int] {
        if node.isLeaf {
            return [depth]
        } else {
            var depths: [Int] = []
            for child in node.children {
                depths.append(contentsOf: collectLeafDepths(node: child, depth: depth + 1))
            }
            return depths
        }
    }
}

