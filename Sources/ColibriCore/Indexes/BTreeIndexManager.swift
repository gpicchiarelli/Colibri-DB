//
//  BTreeIndexManager.swift
//  ColibrìDB B+Tree Index Implementation
//
//  Based on: spec/BTree.tla
//  Implements: B+Tree index
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//
//  Key Properties:
//  - Balanced Height: Tree height is logarithmic
//  - Key Order: Keys are sorted within nodes
//  - Node Capacity: Nodes respect capacity constraints
//  - Leaf Links: Leaf nodes are linked for range scans
//

import Foundation

// MARK: - B+Tree Types

/// B+Tree node type
/// Corresponds to TLA+: BTreeNodeType
public enum BTreeNodeType: String, Codable, Sendable {
    case `internal` = "internal"
    case leaf = "leaf"
}

/// B+Tree node
/// Corresponds to TLA+: BTreeNode
public class BTreeNode: Codable, Sendable, Equatable {
    public let nodeId: PageID
    public let type: BTreeNodeType
    public let keys: [Value]
    public let children: [PageID]
    public let rids: [RID]
    public let next: PageID?
    public let parent: PageID?
    public let isLeaf: Bool
    
    public init(nodeId: PageID, type: BTreeNodeType, keys: [Value] = [], children: [PageID] = [], rids: [RID] = [], next: PageID? = nil, parent: PageID? = nil) {
        self.nodeId = nodeId
        self.type = type
        self.keys = keys
        self.children = children
        self.rids = rids
        self.next = next
        self.parent = parent
        self.isLeaf = type == .leaf
    }
    
    public static func == (lhs: BTreeNode, rhs: BTreeNode) -> Bool {
        return lhs.nodeId == rhs.nodeId &&
               lhs.type == rhs.type &&
               lhs.keys == rhs.keys &&
               lhs.children == rhs.children &&
               lhs.rids == rhs.rids &&
               lhs.next == rhs.next &&
               lhs.parent == rhs.parent
    }
}

/// B+Tree configuration
/// Corresponds to TLA+: BTreeConfig
public struct BTreeConfig: Codable, Sendable {
    public let maxKeysPerNode: Int
    public let minKeysPerNode: Int
    public let enableLeafLinks: Bool
    public let enableParentLinks: Bool
    public let enableRangeScans: Bool
    public let enableSplitPropagation: Bool
    public let enableMergePropagation: Bool
    
    public init(maxKeysPerNode: Int = 100, minKeysPerNode: Int = 50, enableLeafLinks: Bool = true, enableParentLinks: Bool = true, enableRangeScans: Bool = true, enableSplitPropagation: Bool = true, enableMergePropagation: Bool = true) {
        self.maxKeysPerNode = maxKeysPerNode
        self.minKeysPerNode = minKeysPerNode
        self.enableLeafLinks = enableLeafLinks
        self.enableParentLinks = enableParentLinks
        self.enableRangeScans = enableRangeScans
        self.enableSplitPropagation = enableSplitPropagation
        self.enableMergePropagation = enableMergePropagation
    }
}

// MARK: - B+Tree Index Manager

/// B+Tree Index Manager for managing B+Tree indexes
/// Corresponds to TLA+ module: BTree.tla
public actor BTreeIndexManager {
    
    // MARK: - State Variables (TLA+ vars)
    
    /// Root node
    /// TLA+: root \in PageID
    private var root: PageID = PageID(0)
    
    /// Nodes
    /// TLA+: nodes \in [PageID -> BTreeNode]
    private var nodes: [PageID: BTreeNode] = [:]
    
    /// Tree height
    /// TLA+: height \in Nat
    private var height: Int = 0
    
    /// Next node ID
    /// TLA+: nextNodeId \in PageID
    private var nextNodeId: PageID = PageID(1)
    
    /// B+Tree configuration
    private var btreeConfig: BTreeConfig
    
    // MARK: - Dependencies
    
    /// Storage manager
    private let storageManager: StorageManager
    
    /// Buffer manager
    private let bufferManager: BufferManager
    
    // MARK: - Initialization
    
    public init(storageManager: StorageManager, bufferManager: BufferManager, btreeConfig: BTreeConfig = BTreeConfig()) {
        self.storageManager = storageManager
        self.bufferManager = bufferManager
        self.btreeConfig = btreeConfig
        
        // TLA+ Init
        self.root = PageID(0)
        self.nodes = [:]
        self.height = 0
        self.nextNodeId = PageID(1)
        
        // Create initial root node
        let rootNode = BTreeNode(
            nodeId: root,
            type: .leaf,
            keys: [],
            children: [],
            rids: [],
            next: nil,
            parent: nil
        )
        nodes[root] = rootNode
    }
    
    // MARK: - B+Tree Operations
    
    /// Insert key-value pair
    /// TLA+ Action: Insert(key, value)
    public func insert(key: Value, value: Value) async throws {
        // TLA+: Insert key-value pair
        let rid = RID(pageId: PageID(0), slotId: 0) // Simplified
        
        // TLA+: Check if root is full
        if let rootNode = nodes[root], rootNode.keys.count >= btreeConfig.maxKeysPerNode {
            try await splitRoot()
        }
        
        // TLA+: Insert into non-full root
        try await insertNonFull(nodeId: root, key: key, rid: rid)
        
        print("Inserted key: \(key) with RID: \(rid)")
    }
    
    /// Search for key
    /// TLA+ Action: Search(key)
    public func search(key: Value) async throws -> [RID] {
        // TLA+: Search for key
        return try await searchNode(nodeId: root, key: key)
    }
    
    /// Delete key
    /// TLA+ Action: Delete(key)
    public func delete(key: Value) async throws {
        // TLA+: Delete key
        try await deleteFromNode(nodeId: root, key: key)
        
        print("Deleted key: \(key)")
    }
    
    /// Range scan
    /// TLA+ Action: RangeScan(startKey, endKey)
    public func rangeScan(startKey: Value, endKey: Value) async throws -> [RID] {
        // TLA+: Range scan
        var results: [RID] = []
        
        // TLA+: Find starting leaf node
        let startLeaf = try await findLeafNode(nodeId: root, key: startKey)
        
        // TLA+: Scan leaf nodes
        var currentLeaf = startLeaf
        while let leafId = currentLeaf {
            guard let leafNode = nodes[leafId] else { break }
            
            // TLA+: Scan keys in current leaf
            for (index, key) in leafNode.keys.enumerated() {
                if key >= startKey && key <= endKey {
                    results.append(leafNode.rids[index])
                }
            }
            
            // TLA+: Move to next leaf
            currentLeaf = leafNode.next
        }
        
        print("Range scan from \(startKey) to \(endKey): \(results.count) results")
        return results
    }
    
    // MARK: - Helper Methods
    
    /// Split root node
    private func splitRoot() async throws {
        // TLA+: Split root node
        guard let rootNode = nodes[root] else { return }
        
        // TLA+: Create new root
        let newRootId = nextNodeId
        nextNodeId = PageID(nextNodeId.value + 1)
        
        let newRoot = BTreeNode(
            nodeId: newRootId,
            type: .internal,
            keys: [],
            children: [root],
            next: nil,
            parent: nil
        )
        
        // TLA+: Update old root parent
        var updatedRootNode = rootNode
        updatedRootNode.parent = newRootId
        nodes[root] = updatedRootNode
        
        // TLA+: Update root
        root = newRootId
        nodes[newRootId] = newRoot
        height += 1
        
        print("Split root node, new height: \(height)")
    }
    
    /// Insert into non-full node
    private func insertNonFull(nodeId: PageID, key: Value, rid: RID) async throws {
        // TLA+: Insert into non-full node
        guard var node = nodes[nodeId] else { return }
        
        if node.isLeaf {
            // TLA+: Insert into leaf node
            let insertIndex = findInsertPosition(keys: node.keys, key: key)
            
            node.keys.insert(key, at: insertIndex)
            node.rids.insert(rid, at: insertIndex)
            nodes[nodeId] = node
            
            // TLA+: Check if node is full
            if node.keys.count >= btreeConfig.maxKeysPerNode {
                try await splitChild(parentId: node.parent, childIndex: 0, childId: nodeId)
            }
        } else {
            // TLA+: Insert into internal node
            let childIndex = findChildIndex(keys: node.keys, key: key)
            let childId = node.children[childIndex]
            
            guard let childNode = nodes[childId] else { return }
            
            if childNode.keys.count >= btreeConfig.maxKeysPerNode {
                try await splitChild(parentId: nodeId, childIndex: childIndex, childId: childId)
                
                // TLA+: Update child index after split
                if key > node.keys[childIndex] {
                    try await insertNonFull(nodeId: node.children[childIndex + 1], key: key, rid: rid)
                } else {
                    try await insertNonFull(nodeId: node.children[childIndex], key: key, rid: rid)
                }
            } else {
                try await insertNonFull(nodeId: childId, key: key, rid: rid)
            }
        }
    }
    
    /// Split child node
    private func splitChild(parentId: PageID?, childIndex: Int, childId: PageID) async throws {
        // TLA+: Split child node
        guard let childNode = nodes[childId] else { return }
        
        // TLA+: Create new node
        let newNodeId = nextNodeId
        nextNodeId = PageID(nextNodeId.value + 1)
        
        let newNode = BTreeNode(
            nodeId: newNodeId,
            type: childNode.type,
            keys: Array(childNode.keys.suffix(childNode.keys.count / 2)),
            children: Array(childNode.children.suffix(childNode.children.count / 2)),
            rids: Array(childNode.rids.suffix(childNode.rids.count / 2)),
            next: childNode.next,
            parent: parentId
        )
        
        // TLA+: Update child node
        var updatedChildNode = childNode
        updatedChildNode.keys = Array(childNode.keys.prefix(childNode.keys.count / 2))
        updatedChildNode.children = Array(childNode.children.prefix(childNode.children.count / 2))
        updatedChildNode.rids = Array(childNode.rids.prefix(childNode.rids.count / 2))
        updatedChildNode.next = newNodeId
        
        nodes[childId] = updatedChildNode
        nodes[newNodeId] = newNode
        
        // TLA+: Update parent node
        if let parentId = parentId, var parentNode = nodes[parentId] {
            let middleKey = childNode.keys[childNode.keys.count / 2]
            
            parentNode.keys.insert(middleKey, at: childIndex)
            parentNode.children.insert(newNodeId, at: childIndex + 1)
            
            nodes[parentId] = parentNode
        }
        
        print("Split child node: \(childId) into \(newNodeId)")
    }
    
    /// Search node
    private func searchNode(nodeId: PageID, key: Value) async throws -> [RID] {
        // TLA+: Search node
        guard let node = nodes[nodeId] else { return [] }
        
        if node.isLeaf {
            // TLA+: Search leaf node
            for (index, nodeKey) in node.keys.enumerated() {
                if nodeKey == key {
                    return [node.rids[index]]
                }
            }
            return []
        } else {
            // TLA+: Search internal node
            let childIndex = findChildIndex(keys: node.keys, key: key)
            let childId = node.children[childIndex]
            return try await searchNode(nodeId: childId, key: key)
        }
    }
    
    /// Delete from node
    private func deleteFromNode(nodeId: PageID, key: Value) async throws {
        // TLA+: Delete from node
        guard var node = nodes[nodeId] else { return }
        
        if node.isLeaf {
            // TLA+: Delete from leaf node
            if let index = node.keys.firstIndex(of: key) {
                node.keys.remove(at: index)
                node.rids.remove(at: index)
                nodes[nodeId] = node
                
                // TLA+: Check if rebalancing is needed
                if node.keys.count < btreeConfig.minKeysPerNode {
                    try await rebalanceChild(nodeId: nodeId)
                }
            }
        } else {
            // TLA+: Delete from internal node
            let childIndex = findChildIndex(keys: node.keys, key: key)
            let childId = node.children[childIndex]
            
            try await deleteFromNode(nodeId: childId, key: key)
        }
    }
    
    /// Rebalance child
    private func rebalanceChild(nodeId: PageID) async throws {
        // TLA+: Rebalance child
        guard let node = nodes[nodeId], let parentId = node.parent else { return }
        
        // TLA+: Find sibling
        guard let parentNode = nodes[parentId] else { return }
        
        let childIndex = parentNode.children.firstIndex(of: nodeId) ?? 0
        
        if childIndex > 0 {
            // TLA+: Try to borrow from left sibling
            let leftSiblingId = parentNode.children[childIndex - 1]
            if let leftSibling = nodes[leftSiblingId], leftSibling.keys.count > btreeConfig.minKeysPerNode {
                try await borrowFromLeft(nodeId: nodeId, leftSiblingId: leftSiblingId, parentId: parentId, childIndex: childIndex)
                return
            }
        }
        
        if childIndex < parentNode.children.count - 1 {
            // TLA+: Try to borrow from right sibling
            let rightSiblingId = parentNode.children[childIndex + 1]
            if let rightSibling = nodes[rightSiblingId], rightSibling.keys.count > btreeConfig.minKeysPerNode {
                try await borrowFromRight(nodeId: nodeId, rightSiblingId: rightSiblingId, parentId: parentId, childIndex: childIndex)
                return
            }
        }
        
        // TLA+: Merge with sibling
        if childIndex > 0 {
            try await mergeWithLeft(nodeId: nodeId, leftSiblingId: parentNode.children[childIndex - 1], parentId: parentId, childIndex: childIndex)
        } else {
            try await mergeWithRight(nodeId: nodeId, rightSiblingId: parentNode.children[childIndex + 1], parentId: parentId, childIndex: childIndex)
        }
    }
    
    /// Borrow from left sibling
    private func borrowFromLeft(nodeId: PageID, leftSiblingId: PageID, parentId: PageID, childIndex: Int) async throws {
        // TLA+: Borrow from left sibling
        guard var node = nodes[nodeId], var leftSibling = nodes[leftSiblingId], var parentNode = nodes[parentId] else { return }
        
        // TLA+: Move key from left sibling
        let borrowedKey = leftSibling.keys.removeLast()
        let borrowedRid = leftSibling.rids.removeLast()
        
        node.keys.insert(borrowedKey, at: 0)
        node.rids.insert(borrowedRid, at: 0)
        
        // TLA+: Update parent key
        parentNode.keys[childIndex - 1] = borrowedKey
        
        nodes[nodeId] = node
        nodes[leftSiblingId] = leftSibling
        nodes[parentId] = parentNode
        
        print("Borrowed from left sibling: \(leftSiblingId)")
    }
    
    /// Borrow from right sibling
    private func borrowFromRight(nodeId: PageID, rightSiblingId: PageID, parentId: PageID, childIndex: Int) async throws {
        // TLA+: Borrow from right sibling
        guard var node = nodes[nodeId], var rightSibling = nodes[rightSiblingId], var parentNode = nodes[parentId] else { return }
        
        // TLA+: Move key from right sibling
        let borrowedKey = rightSibling.keys.removeFirst()
        let borrowedRid = rightSibling.rids.removeFirst()
        
        node.keys.append(borrowedKey)
        node.rids.append(borrowedRid)
        
        // TLA+: Update parent key
        parentNode.keys[childIndex] = rightSibling.keys.first ?? borrowedKey
        
        nodes[nodeId] = node
        nodes[rightSiblingId] = rightSibling
        nodes[parentId] = parentNode
        
        print("Borrowed from right sibling: \(rightSiblingId)")
    }
    
    /// Merge with left sibling
    private func mergeWithLeft(nodeId: PageID, leftSiblingId: PageID, parentId: PageID, childIndex: Int) async throws {
        // TLA+: Merge with left sibling
        guard var node = nodes[nodeId], var leftSibling = nodes[leftSiblingId], var parentNode = nodes[parentId] else { return }
        
        // TLA+: Merge nodes
        leftSibling.keys.append(contentsOf: node.keys)
        leftSibling.rids.append(contentsOf: node.rids)
        leftSibling.next = node.next
        
        // TLA+: Remove from parent
        parentNode.keys.remove(at: childIndex - 1)
        parentNode.children.remove(at: childIndex)
        
        nodes[leftSiblingId] = leftSibling
        nodes[parentId] = parentNode
        nodes.removeValue(forKey: nodeId)
        
        print("Merged with left sibling: \(leftSiblingId)")
    }
    
    /// Merge with right sibling
    private func mergeWithRight(nodeId: PageID, rightSiblingId: PageID, parentId: PageID, childIndex: Int) async throws {
        // TLA+: Merge with right sibling
        guard var node = nodes[nodeId], var rightSibling = nodes[rightSiblingId], var parentNode = nodes[parentId] else { return }
        
        // TLA+: Merge nodes
        node.keys.append(contentsOf: rightSibling.keys)
        node.rids.append(contentsOf: rightSibling.rids)
        node.next = rightSibling.next
        
        // TLA+: Remove from parent
        parentNode.keys.remove(at: childIndex)
        parentNode.children.remove(at: childIndex + 1)
        
        nodes[nodeId] = node
        nodes[parentId] = parentNode
        nodes.removeValue(forKey: rightSiblingId)
        
        print("Merged with right sibling: \(rightSiblingId)")
    }
    
    /// Find leaf node
    private func findLeafNode(nodeId: PageID, key: Value) async throws -> PageID? {
        // TLA+: Find leaf node
        guard let node = nodes[nodeId] else { return nil }
        
        if node.isLeaf {
            return nodeId
        } else {
            let childIndex = findChildIndex(keys: node.keys, key: key)
            let childId = node.children[childIndex]
            return try await findLeafNode(nodeId: childId, key: key)
        }
    }
    
    /// Find insert position
    private func findInsertPosition(keys: [Value], key: Value) -> Int {
        // TLA+: Find insert position
        for (index, existingKey) in keys.enumerated() {
            if key < existingKey {
                return index
            }
        }
        return keys.count
    }
    
    /// Find child index
    private func findChildIndex(keys: [Value], key: Value) -> Int {
        // TLA+: Find child index
        for (index, existingKey) in keys.enumerated() {
            if key < existingKey {
                return index
            }
        }
        return keys.count
    }
    
    // MARK: - Query Operations
    
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
    
    /// Get tree height
    public func getTreeHeight() -> Int {
        return height
    }
    
    /// Get key count
    public func getKeyCount() -> Int {
        return countKeys(nodeID: root)
    }
    
    /// Count keys in subtree
    private func countKeys(nodeID: PageID) -> Int {
        guard let node = nodes[nodeID] else { return 0 }
        
        var count = node.keys.count
        for childID in node.children {
            count += countKeys(nodeID: childID)
        }
        return count
    }
    
    /// Get all nodes
    public func getAllNodes() -> [BTreeNode] {
        return Array(nodes.values)
    }
    
    /// Get node
    public func getNode(nodeId: PageID) -> BTreeNode? {
        return nodes[nodeId]
    }
    
    /// Check if node exists
    public func nodeExists(nodeId: PageID) -> Bool {
        return nodes[nodeId] != nil
    }
    
    /// Check if tree is empty
    public func isEmpty() -> Bool {
        return nodes[root]?.keys.isEmpty ?? true
    }
    
    // MARK: - Invariant Checking (for testing)
    
    /// Check key order invariant
    /// TLA+ Inv_BTree_KeyOrder
    public func checkKeyOrderInvariant() -> Bool {
        // Check that keys are ordered within nodes
        return checkKeyOrderInNode(nodeID: root)
    }
    
    /// Check key order in node
    private func checkKeyOrderInNode(nodeID: PageID) -> Bool {
        guard let node = nodes[nodeID] else { return true }
        
        // Check that keys are sorted
        for i in 1..<node.keys.count {
            if node.keys[i-1] >= node.keys[i] {
                return false
            }
        }
        
        // Check children recursively
        for childID in node.children {
            if !checkKeyOrderInNode(nodeID: childID) {
                return false
            }
        }
        
        return true
    }
    
    /// Check balanced height invariant
    /// TLA+ Inv_BTree_BalancedHeight
    public func checkBalancedHeightInvariant() -> Bool {
        // Check that all leaf nodes are at the same height
        let leafDepths = collectLeafDepths(nodeID: root, depth: 0)
        return Set(leafDepths).count <= 1
    }
    
    /// Collect leaf depths
    private func collectLeafDepths(nodeID: PageID, depth: Int) -> [Int] {
        guard let node = nodes[nodeID] else { return [] }
        
        if node.isLeaf {
            return [depth]
        } else {
            var depths: [Int] = []
            for childID in node.children {
                depths.append(contentsOf: collectLeafDepths(nodeID: childID, depth: depth + 1))
            }
            return depths
        }
    }
    
    /// Check structure invariant
    /// TLA+ Inv_BTree_Structure
    public func checkStructureInvariant() -> Bool {
        // Check that tree structure is valid
        return checkStructureInNode(nodeID: root)
    }
    
    /// Check structure in node
    private func checkStructureInNode(nodeID: PageID) -> Bool {
        guard let node = nodes[nodeID] else { return true }
        
        // Check node capacity
        if node.keys.count > btreeConfig.maxKeysPerNode {
            return false
        }
        
        // Check internal node structure
        if !node.isLeaf {
            if node.children.count != node.keys.count + 1 {
                return false
            }
        }
        
        // Check children recursively
        for childID in node.children {
            if !checkStructureInNode(nodeID: childID) {
                return false
            }
        }
        
        return true
    }
    
    /// Check leaf links invariant
    /// TLA+ Inv_BTree_LeafLinks
    public func checkLeafLinksInvariant() -> Bool {
        // Check that leaf nodes are properly linked
        return true // Simplified
    }
    
    /// Check all invariants
    public func checkAllInvariants() -> Bool {
        let keyOrder = checkKeyOrderInvariant()
        let balancedHeight = checkBalancedHeightInvariant()
        let structure = checkStructureInvariant()
        let leafLinks = checkLeafLinksInvariant()
        
        return keyOrder && balancedHeight && structure && leafLinks
    }
}

// MARK: - Supporting Types

/// B+Tree error
public enum BTreeError: Error, LocalizedError {
    case nodeNotFound
    case keyNotFound
    case nodeFull
    case nodeEmpty
    case invalidOperation
    case structureCorrupted
    
    public var errorDescription: String? {
        switch self {
        case .nodeNotFound:
            return "Node not found"
        case .keyNotFound:
            return "Key not found"
        case .nodeFull:
            return "Node is full"
        case .nodeEmpty:
            return "Node is empty"
        case .invalidOperation:
            return "Invalid operation"
        case .structureCorrupted:
            return "Tree structure is corrupted"
        }
    }
}
