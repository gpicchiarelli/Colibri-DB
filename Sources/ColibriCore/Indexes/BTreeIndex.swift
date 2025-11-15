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
//  - Search Correctness: Search finds key if present
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
    var nodeID: PageID  // Unique node identifier
    
    init(isLeaf: Bool, nodeID: PageID) {
        self.isLeaf = isLeaf
        self.nodeID = nodeID
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
public final class BTreeIndex: @unchecked Sendable {
    // MARK: - State
    private let lock = NSLock()
    
    // MARK: - Configuration
    
    /// Minimum degree (node has [t-1, 2t-1] keys)
    /// TLA+: MIN_DEGREE
    static let minDegree = 3
    
    // MARK: - State Variables (TLA+ vars)
    
    /// Root node ID
    /// TLA+: root \in PageIds
    private var root: PageID
    
    /// All nodes in the tree
    /// TLA+: nodes \in [PageIds -> Node]
    private var nodes: [PageID: BTreeNode] = [:]
    
    /// Tree height
    /// TLA+: height \in Nat
    private var height: Int
    
    /// Next node ID (for tracking)
    /// TLA+: nextNodeId \in PageIds
    private var nextNodeId: PageID
    
    // MARK: - Initialization
    
    public init() {
        // TLA+ Init
        self.root = 1
        self.height = 1
        self.nextNodeId = 2
        
        // Create initial root node
        let rootNode = BTreeNode(isLeaf: true, nodeID: root)
        nodes[root] = rootNode
    }
    
    // MARK: - Core Operations
    
    /// Insert a key-RID pair into B+Tree
    /// TLA+ Action: Insert(key, rid)
    /// Precondition: key and rid are valid
    /// Postcondition: key inserted, tree remains balanced
    public func insert(key: Value, rid: RID) throws {
        lock.lock()
        defer { lock.unlock() }
        
        guard let rootNode = nodes[root] else {
            throw DBError.internalError("Root node not found")
        }
        
        // If root is full, split it
        if rootNode.isFull {
            try splitRoot()
        }
        
        // Insert into non-full root
        try insertNonFull(nodeID: root, key: key, rid: rid)
    }
    
    /// Search for a key in B+Tree
    /// TLA+ Action: Search(key)
    /// Precondition: key is valid
    /// Postcondition: returns RIDs if found, nil otherwise
    public func search(key: Value) -> [RID]? {
        return searchNode(nodeID: root, key: key)
    }
    
    /// Delete a key from B+Tree
    /// TLA+ Action: Delete(key)
    /// Precondition: key exists in tree
    /// Postcondition: key deleted, tree remains balanced
    public func delete(key: Value) throws {
        try deleteFromNode(nodeID: root, key: key)
        
        // If root is empty and has children, make first child the new root
        if let rootNode = nodes[root], !rootNode.isLeaf && rootNode.keys.isEmpty {
            if !rootNode.children.isEmpty {
                let newRootID = rootNode.children[0].nodeID
                root = newRootID
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
        guard let leafNodeID = findLeafNode(forKey: minKey) else {
            return results
        }
        
        // Scan through leaves following next pointers
        var currentLeafID: PageID? = leafNodeID
        
        while let leafID = currentLeafID, let leafNode = nodes[leafID] {
            for (index, key) in leafNode.keys.enumerated() {
                if key >= minKey && key <= maxKey {
                    results.append((key, leafNode.rids[index]))
                } else if key > maxKey {
                    // We've passed the range
                    return results
                }
            }
            
            // Move to next leaf
            currentLeafID = leafNode.next?.nodeID
        }
        
        return results
    }
    
    // MARK: - Private Helper Methods
    
    /// Split root node when it's full
    /// TLA+: SplitRoot
    private func splitRoot() throws {
        guard let oldRoot = nodes[root] else {
            throw DBError.internalError("Root node not found")
        }
        
        // Create new root
        let newRootID = nextNodeId
        nextNodeId += 1
        let newRoot = BTreeNode(isLeaf: false, nodeID: newRootID)
        nodes[newRootID] = newRoot
        
        // Add old root as child
        newRoot.children.append(oldRoot)
        oldRoot.parent = newRoot
        
        // Split the old root
        try splitChild(parentID: newRootID, childIndex: 0)
        
        // Update root and height
        root = newRootID
        height += 1
    }
    
    /// Insert into a non-full node
    /// TLA+: InsertNonFull(nid, key, rid)
    private func insertNonFull(nodeID: PageID, key: Value, rid: RID) throws {
        guard let node = nodes[nodeID] else {
            throw DBError.internalError("Node not found")
        }
        
        if node.isLeaf {
            // Insert key into leaf node
            let pos = findInsertPosition(keys: node.keys, key: key)
            
            if pos < node.keys.count && node.keys[pos] == key {
                // Existing key – append RID to the same slot
                node.rids[pos].append(rid)
            } else {
                node.keys.insert(key, at: pos)
                node.rids.insert([rid], at: pos)
            }
        } else {
            // Find child to recurse into
            let pos = findChildIndex(keys: node.keys, key: key)
            let child = node.children[pos]
            
            // Split child if full
            if child.isFull {
                try splitChild(parentID: nodeID, childIndex: pos)
                
                // After split, determine which child to recurse into
                if key > node.keys[pos] {
                    try insertNonFull(nodeID: node.children[pos + 1].nodeID, key: key, rid: rid)
                } else {
                    try insertNonFull(nodeID: node.children[pos].nodeID, key: key, rid: rid)
                }
            } else {
                try insertNonFull(nodeID: child.nodeID, key: key, rid: rid)
            }
        }
    }
    
    /// Split a full child node
    /// TLA+: SplitNode(nid)
    private func splitChild(parentID: PageID, childIndex: Int) throws {
        guard let parent = nodes[parentID] else {
            throw DBError.internalError("Parent node not found")
        }
        
        guard childIndex < parent.children.count else {
            throw DBError.internalError("Child index out of range")
        }
        
        let child = parent.children[childIndex]
        let mid = Self.minDegree - 1  // Correct split point for B+Tree
        
        // Validate bounds before splitting
        guard mid < child.keys.count else {
            throw DBError.internalError("Cannot split node: insufficient keys")
        }
        
        // Create new node
        let newNodeID = nextNodeId
        nextNodeId += 1
        let newNode = BTreeNode(isLeaf: child.isLeaf, nodeID: newNodeID)
        newNode.parent = parent
        nodes[newNodeID] = newNode
        
        // Split keys - promote middle key for internal nodes
        let promotedKey = child.keys[mid]
        guard (mid + 1) < child.keys.count else {
            throw DBError.internalError("Cannot split node: invalid key range")
        }
        newNode.keys = Array(child.keys[(mid + 1)...])
        child.keys = Array(child.keys[0..<mid])
        
        if child.isLeaf {
            // Split leaf node - include promoted key in right node
            newNode.keys.insert(promotedKey, at: 0)
            guard mid < child.rids.count else {
                throw DBError.internalError("Cannot split leaf: insufficient RIDs")
            }
            newNode.rids = Array(child.rids[mid...])
            child.rids = Array(child.rids[0..<mid])
            
            // Update leaf links
            newNode.next = child.next
            child.next = newNode
        } else {
            // Split internal node - don't include promoted key in children
            guard (mid + 1) < child.children.count else {
                throw DBError.internalError("Cannot split internal node: insufficient children")
            }
            newNode.children = Array(child.children[(mid + 1)...])
            child.children = Array(child.children[0...(mid)])
            
            // Update parent pointers
            for grandchild in newNode.children {
                grandchild.parent = newNode
            }
        }
        
        // Insert promoted key and new child into parent
        parent.keys.insert(promotedKey, at: childIndex)
        parent.children.insert(newNode, at: childIndex + 1)
    }
    
    /// Search for a key in a subtree
    /// TLA+: SearchNode(nid, key)
    private func searchNode(nodeID: PageID, key: Value) -> [RID]? {
        guard let node = nodes[nodeID] else {
            return nil
        }
        
        if node.isLeaf {
            // Search in leaf
            if let index = node.keys.firstIndex(of: key) {
                return node.rids[index]
            }
            return nil
        } else {
            // Search in internal node
            let childIndex = findChildIndex(keys: node.keys, key: key)
            guard childIndex < node.children.count else {
                return nil
            }
            return searchNode(nodeID: node.children[childIndex].nodeID, key: key)
        }
    }
    
    /// Delete a key from a subtree
    /// TLA+: DeleteFromNode(nid, key)
    private func deleteFromNode(nodeID: PageID, key: Value) throws {
        guard let node = nodes[nodeID] else {
            throw DBError.internalError("Node not found")
        }
        
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
            guard childIndex < node.children.count else {
                throw DBError.notFound
            }
            let child = node.children[childIndex]
            
            // Delete from child first
            try deleteFromNode(nodeID: child.nodeID, key: key)
            
            // Then rebalance if needed
            if child.keys.count < Self.minDegree - 1 {
                try rebalanceChild(parentID: nodeID, childIndex: childIndex)
            }
        }
    }
    
    /// Rebalance a child that has too few keys
    private func rebalanceChild(parentID: PageID, childIndex: Int) throws {
        guard let parent = nodes[parentID] else {
            throw DBError.internalError("Parent node not found")
        }
        
        guard childIndex < parent.children.count else {
            throw DBError.internalError("Child index out of range")
        }
        
        let child = parent.children[childIndex]
        
        // Try borrowing from left sibling
        if childIndex > 0 {
            let leftSibling = parent.children[childIndex - 1]
            if leftSibling.keys.count >= Self.minDegree {
                try borrowFromLeft(parentID: parentID, childIndex: childIndex)
                return
            }
        }
        
        // Try borrowing from right sibling
        if childIndex < parent.children.count - 1 {
            let rightSibling = parent.children[childIndex + 1]
            if rightSibling.keys.count >= Self.minDegree {
                try borrowFromRight(parentID: parentID, childIndex: childIndex)
                return
            }
        }
        
        // Merge with sibling
        if childIndex > 0 {
            try mergeWithLeft(parentID: parentID, childIndex: childIndex)
        } else if childIndex < parent.children.count - 1 {
            try mergeWithRight(parentID: parentID, childIndex: childIndex)
        }
    }
    
    /// Borrow a key from left sibling
    private func borrowFromLeft(parentID: PageID, childIndex: Int) throws {
        guard let parent = nodes[parentID] else {
            throw DBError.internalError("Parent node not found")
        }
        
        guard childIndex < parent.children.count && childIndex > 0 else {
            throw DBError.internalError("Invalid child index for left borrow")
        }
        
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
    private func borrowFromRight(parentID: PageID, childIndex: Int) throws {
        guard let parent = nodes[parentID] else {
            throw DBError.internalError("Parent node not found")
        }
        
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
    private func mergeWithLeft(parentID: PageID, childIndex: Int) throws {
        guard let parent = nodes[parentID] else {
            throw DBError.internalError("Parent node not found")
        }
        
        guard childIndex < parent.children.count && childIndex > 0 else {
            throw DBError.internalError("Invalid child index for left merge")
        }
        
        let child = parent.children[childIndex]
        let leftSibling = parent.children[childIndex - 1]
        
        if child.isLeaf {
            // For leaf nodes, just merge child into left sibling
            // Don't add parent key to leaf nodes
            leftSibling.keys.append(contentsOf: child.keys)
            leftSibling.rids.append(contentsOf: child.rids)
            leftSibling.next = child.next
        } else {
            // For internal nodes, move parent key down
            leftSibling.keys.append(parent.keys[childIndex - 1])
            
            // Merge child into left sibling
            leftSibling.keys.append(contentsOf: child.keys)
            
            leftSibling.children.append(contentsOf: child.children)
            for grandchild in child.children {
                grandchild.parent = leftSibling
            }
        }
        
        // Remove key and child from parent
        parent.keys.remove(at: childIndex - 1)
        parent.children.remove(at: childIndex)
        
        // Remove child from nodes
        nodes.removeValue(forKey: child.nodeID)
    }
    
    /// Merge child with right sibling
    private func mergeWithRight(parentID: PageID, childIndex: Int) throws {
        guard let parent = nodes[parentID] else {
            throw DBError.internalError("Parent node not found")
        }
        
        guard childIndex < parent.children.count - 1 else {
            throw DBError.internalError("Invalid child index for right merge")
        }
        
        let child = parent.children[childIndex]
        let rightSibling = parent.children[childIndex + 1]
        
        if child.isLeaf {
            // For leaf nodes, just merge right sibling into child
            // Don't add parent key to leaf nodes
            child.keys.append(contentsOf: rightSibling.keys)
            child.rids.append(contentsOf: rightSibling.rids)
            child.next = rightSibling.next
        } else {
            // For internal nodes, move parent key down
            child.keys.append(parent.keys[childIndex])
            
            // Merge right sibling into child
            child.keys.append(contentsOf: rightSibling.keys)
            
            child.children.append(contentsOf: rightSibling.children)
            for grandchild in rightSibling.children {
                grandchild.parent = child
            }
        }
        
        // Remove key and child from parent
        parent.keys.remove(at: childIndex)
        parent.children.remove(at: childIndex + 1)
        
        // Remove right sibling from nodes
        nodes.removeValue(forKey: rightSibling.nodeID)
    }
    
    /// Find leaf node that should contain key
    /// TLA+: FindLeafNode(key)
    private func findLeafNode(forKey key: Value) -> PageID? {
        var currentID = root
        
        while let currentNode = nodes[currentID], !currentNode.isLeaf {
            let childIndex = findChildIndex(keys: currentNode.keys, key: key)
            guard childIndex < currentNode.children.count else {
                return nil
            }
            currentID = currentNode.children[childIndex].nodeID
        }
        
        return currentID
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
        return countKeys(nodeID: root)
    }
    
    /// Get root node ID
    public func getRootID() -> PageID {
        return root
    }
    
    /// Get next node ID
    public func getNextNodeID() -> PageID {
        return nextNodeId
    }
    
    /// Get node count
    public func getNodeCount() -> Int {
        return nodes.count
    }
    
    private func countKeys(nodeID: PageID) -> Int {
        guard let node = nodes[nodeID] else {
            return 0
        }
        
        if node.isLeaf {
            return node.keys.count
        } else {
            var count = 0
            for child in node.children {
                count += countKeys(nodeID: child.nodeID)
            }
            return count
        }
    }
    
    // MARK: - Invariant Checking (for testing)
    
    /// Check key order invariant
    /// TLA+: Inv_BTree_KeyOrder
    public func checkKeyOrderInvariant() -> Bool {
        return checkKeyOrderInNode(nodeID: root)
    }
    
    private func checkKeyOrderInNode(nodeID: PageID) -> Bool {
        guard let node = nodes[nodeID] else {
            return false
        }
        
        // Check keys are sorted
        for i in 0..<(node.keys.count - 1) {
            if node.keys[i] >= node.keys[i + 1] {
                return false
            }
        }
        
        // Recurse into children
        if !node.isLeaf {
            for child in node.children {
                if !checkKeyOrderInNode(nodeID: child.nodeID) {
                    return false
                }
            }
        }
        
        return true
    }
    
    /// Check balanced height invariant
    /// TLA+: Inv_BTree_BalancedHeight
    public func checkBalancedHeightInvariant() -> Bool {
        let leafDepths = collectLeafDepths(nodeID: root, depth: 0)
        let uniqueDepths = Set(leafDepths)
        return uniqueDepths.count == 1
    }
    
    private func collectLeafDepths(nodeID: PageID, depth: Int) -> [Int] {
        guard let node = nodes[nodeID] else {
            return []
        }
        
        if node.isLeaf {
            return [depth]
        } else {
            var depths: [Int] = []
            for child in node.children {
                depths.append(contentsOf: collectLeafDepths(nodeID: child.nodeID, depth: depth + 1))
            }
            return depths
        }
    }
    
    /// Check structure invariant
    /// TLA+: Inv_BTree_StructureInvariant
    public func checkStructureInvariant() -> Bool {
        return checkStructureInNode(nodeID: root)
    }
    
    private func checkStructureInNode(nodeID: PageID) -> Bool {
        guard let node = nodes[nodeID] else {
            return false
        }
        
        // Check node capacity constraints
        if nodeID != root && node.keys.count < Self.minDegree - 1 {
            return false  // Non-root node has too few keys
        }
        
        if node.keys.count > 2 * Self.minDegree - 1 {
            return false  // Node has too many keys
        }
        
        // Check internal node structure
        if !node.isLeaf {
            if node.children.count != node.keys.count + 1 {
                return false  // Internal node should have keys+1 children
            }
            
            // Recurse into children
            for child in node.children {
                if !checkStructureInNode(nodeID: child.nodeID) {
                    return false
                }
            }
        }
        
        return true
    }
    
    /// Check leaf links invariant
    /// TLA+: Inv_BTree_LeafLinks
    public func checkLeafLinksInvariant() -> Bool {
        // Find leftmost leaf
        var currentID = root
        while let node = nodes[currentID], !node.isLeaf {
            currentID = node.children[0].nodeID
        }
        
        // Traverse leaf chain
        var leafIDs: [PageID] = []
        var currentLeafID: PageID? = currentID
        
        while let leafID = currentLeafID, let leaf = nodes[leafID] {
            leafIDs.append(leafID)
            currentLeafID = leaf.next?.nodeID
        }
        
        // Check that all leaves are reachable
        let allLeafIDs = nodes.compactMap { (id, node) in
            node.isLeaf ? id : nil
        }
        
        return Set(leafIDs) == Set(allLeafIDs)
    }
}

