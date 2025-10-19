/*
 * RadixTree.swift
 * ColibrìDB - Radix Tree (Patricia Trie) Implementation
 *
 * Based on TLA+ specification: RadixTree.tla
 *
 * Space-optimized trie with path compression for efficient string indexing.
 *
 * References:
 * [1] Morrison, D. R. (1968). "PATRICIA—Practical Algorithm To Retrieve
 *     Information Coded In Alphanumeric" Journal of the ACM, 15(4), 514-534.
 * [2] Knuth, D. E. (1973). "The Art of Computer Programming, Volume 3:
 *     Sorting and Searching" Section 6.3: Digital Searching.
 * [3] Nilsson, S., & Tikkanen, M. (1998). "Implementing a Dynamic
 *     Compressed Trie" Proceedings of WAE '98, pp. 25-36.
 *
 * Properties:
 * - Space-optimized trie with path compression
 * - Efficient for string keys with common prefixes
 * - O(k) search/insert/delete where k = key length
 * - Memory efficient: stores prefixes only once
 *
 * Author: ColibrìDB Team
 * Date: 2025-10-19
 */

import Foundation

// MARK: - Radix Tree Node

/// Node in the radix tree (Morrison 1968, Figure 2)
public class RadixNode<Value> {
    /// Compressed path segment
    public var prefix: [UInt8]
    
    /// Children indexed by byte value
    public var children: [UInt8: RadixNode<Value>] = [:]
    
    /// Whether this node stores a value
    public var isLeaf: Bool
    
    /// Stored value (if leaf)
    public var value: Value?
    
    /// Last modification LSN (for WAL integration)
    public var lsn: UInt64
    
    public init(prefix: [UInt8] = [], isLeaf: Bool = false, value: Value? = nil, lsn: UInt64 = 0) {
        self.prefix = prefix
        self.isLeaf = isLeaf
        self.value = value
        self.lsn = lsn
    }
}

// MARK: - Radix Tree

/// Radix Tree (Patricia Trie) for efficient string indexing
public class RadixTree<Value> {
    
    /// Root node
    private var root: RadixNode<Value>
    
    /// Node count
    private var nodeCount: Int = 1
    
    /// Maximum nodes (for resource limits)
    private let maxNodes: Int
    
    /// Maximum key length
    private let maxKeyLength: Int
    
    /// Next LSN
    private var nextLSN: UInt64 = 1
    
    /// Statistics
    private var stats: RadixTreeStats = RadixTreeStats()
    
    public init(maxNodes: Int = 1_000_000, maxKeyLength: Int = 1024) {
        self.maxNodes = maxNodes
        self.maxKeyLength = maxKeyLength
        self.root = RadixNode<Value>()
    }
    
    // MARK: - Core Operations
    
    /// Insert a key-value pair
    public func insert(key: String, value: Value) throws {
        guard key.count <= maxKeyLength else {
            throw RadixTreeError.keyTooLong(length: key.count, max: maxKeyLength)
        }
        
        guard nodeCount < maxNodes else {
            throw RadixTreeError.maxNodesReached
        }
        
        let keyBytes = [UInt8](key.utf8)
        try insertHelper(node: root, keyBytes: keyBytes, value: value, depth: 0)
        
        stats.totalInserts += 1
        stats.totalKeys += 1
    }
    
    private func insertHelper(node: RadixNode<Value>, keyBytes: [UInt8], value: Value, depth: Int) throws {
        // Base case: reached end of key
        if depth >= keyBytes.count {
            node.isLeaf = true
            node.value = value
            node.lsn = nextLSN
            nextLSN += 1
            return
        }
        
        let byte = keyBytes[depth]
        
        // Check if child exists for this byte
        if let child = node.children[byte] {
            // Find common prefix between remaining key and child's prefix
            let remainingKey = Array(keyBytes[depth...])
            let commonPrefixLen = findCommonPrefixLength(a: remainingKey, b: child.prefix)
            
            if commonPrefixLen == child.prefix.count {
                // Child's prefix is fully matched, continue down
                try insertHelper(node: child, keyBytes: keyBytes, value: value, depth: depth + commonPrefixLen)
            } else {
                // Need to split the child node
                try splitNode(parent: node, child: child, byte: byte, 
                            remainingKey: remainingKey, value: value, 
                            commonPrefixLen: commonPrefixLen, depth: depth)
            }
        } else {
            // Create new child
            let newNode = RadixNode<Value>(
                prefix: Array(keyBytes[depth...]),
                isLeaf: true,
                value: value,
                lsn: nextLSN
            )
            nextLSN += 1
            node.children[byte] = newNode
            nodeCount += 1
            
            guard nodeCount <= maxNodes else {
                throw RadixTreeError.maxNodesReached
            }
        }
    }
    
    private func splitNode(parent: RadixNode<Value>, child: RadixNode<Value>, 
                          byte: UInt8, remainingKey: [UInt8], value: Value,
                          commonPrefixLen: Int, depth: Int) throws {
        // Create intermediate node with common prefix
        let intermediateNode = RadixNode<Value>(
            prefix: Array(child.prefix[..<commonPrefixLen]),
            isLeaf: false,
            lsn: nextLSN
        )
        nextLSN += 1
        nodeCount += 1
        
        // Update child's prefix (remove common part)
        child.prefix = Array(child.prefix[commonPrefixLen...])
        
        // Add child to intermediate node
        let childByte = child.prefix[0]
        intermediateNode.children[childByte] = child
        
        // Add new node for inserted key
        if commonPrefixLen < remainingKey.count {
            let newPrefix = Array(remainingKey[commonPrefixLen...])
            let newNode = RadixNode<Value>(
                prefix: newPrefix,
                isLeaf: true,
                value: value,
                lsn: nextLSN
            )
            nextLSN += 1
            nodeCount += 1
            
            let newByte = newPrefix[0]
            intermediateNode.children[newByte] = newNode
        } else {
            // Inserted key ends at intermediate node
            intermediateNode.isLeaf = true
            intermediateNode.value = value
        }
        
        // Replace child with intermediate node in parent
        parent.children[byte] = intermediateNode
        
        guard nodeCount <= maxNodes else {
            throw RadixTreeError.maxNodesReached
        }
    }
    
    /// Search for a key
    public func search(key: String) -> Value? {
        let keyBytes = [UInt8](key.utf8)
        let result = searchHelper(node: root, keyBytes: keyBytes, depth: 0)
        
        if result != nil {
            stats.totalSearches += 1
            stats.successfulSearches += 1
        } else {
            stats.totalSearches += 1
        }
        
        return result
    }
    
    private func searchHelper(node: RadixNode<Value>, keyBytes: [UInt8], depth: Int) -> Value? {
        // Base case: reached end of key
        if depth >= keyBytes.count {
            return node.isLeaf ? node.value : nil
        }
        
        let byte = keyBytes[depth]
        
        guard let child = node.children[byte] else {
            return nil
        }
        
        // Check if child's prefix matches remaining key
        let remainingKey = Array(keyBytes[depth...])
        if !hasPrefix(array: remainingKey, prefix: child.prefix) {
            return nil
        }
        
        return searchHelper(node: child, keyBytes: keyBytes, depth: depth + child.prefix.count)
    }
    
    /// Delete a key
    public func delete(key: String) -> Bool {
        let keyBytes = [UInt8](key.utf8)
        let deleted = deleteHelper(node: root, keyBytes: keyBytes, depth: 0)
        
        if deleted {
            stats.totalDeletes += 1
            stats.totalKeys -= 1
        }
        
        return deleted
    }
    
    @discardableResult
    private func deleteHelper(node: RadixNode<Value>, keyBytes: [UInt8], depth: Int) -> Bool {
        // Base case: reached end of key
        if depth >= keyBytes.count {
            if node.isLeaf {
                node.isLeaf = false
                node.value = nil
                node.lsn = nextLSN
                nextLSN += 1
                return true
            }
            return false
        }
        
        let byte = keyBytes[depth]
        
        guard let child = node.children[byte] else {
            return false
        }
        
        // Check if child's prefix matches
        let remainingKey = Array(keyBytes[depth...])
        if !hasPrefix(array: remainingKey, prefix: child.prefix) {
            return false
        }
        
        let deleted = deleteHelper(node: child, keyBytes: keyBytes, depth: depth + child.prefix.count)
        
        // Clean up if child has no value and only one child
        if deleted && !child.isLeaf && child.children.count == 1 {
            // Merge child with its single child
            if let (grandChildByte, grandChild) = child.children.first {
                grandChild.prefix = child.prefix + grandChild.prefix
                node.children[byte] = grandChild
                nodeCount -= 1
            }
        } else if deleted && !child.isLeaf && child.children.isEmpty {
            // Remove child if it has no value and no children
            node.children.removeValue(forKey: byte)
            nodeCount -= 1
        }
        
        return deleted
    }
    
    // MARK: - Range Queries
    
    /// Find all keys with given prefix
    public func keysWithPrefix(_ prefix: String) -> [String] {
        let prefixBytes = [UInt8](prefix.utf8)
        var results: [String] = []
        
        if let node = findNodeForPrefix(prefixBytes: prefixBytes) {
            collectKeys(node: node, prefix: prefixBytes, results: &results)
        }
        
        return results
    }
    
    private func findNodeForPrefix(prefixBytes: [UInt8]) -> RadixNode<Value>? {
        var currentNode = root
        var depth = 0
        
        while depth < prefixBytes.count {
            let byte = prefixBytes[depth]
            
            guard let child = currentNode.children[byte] else {
                return nil
            }
            
            let remainingPrefix = Array(prefixBytes[depth...])
            if !hasPrefix(array: remainingPrefix, prefix: child.prefix) &&
               !hasPrefix(array: child.prefix, prefix: remainingPrefix) {
                return nil
            }
            
            if child.prefix.count > remainingPrefix.count {
                return child
            }
            
            currentNode = child
            depth += child.prefix.count
        }
        
        return currentNode
    }
    
    private func collectKeys(node: RadixNode<Value>, prefix: [UInt8], results: inout [String]) {
        if node.isLeaf {
            if let key = String(bytes: prefix, encoding: .utf8) {
                results.append(key)
            }
        }
        
        for (byte, child) in node.children {
            var newPrefix = prefix
            newPrefix.append(contentsOf: child.prefix)
            collectKeys(node: child, prefix: newPrefix, results: &results)
        }
    }
    
    // MARK: - Helper Methods
    
    private func findCommonPrefixLength(a: [UInt8], b: [UInt8]) -> Int {
        var length = 0
        let minLen = min(a.count, b.count)
        
        while length < minLen && a[length] == b[length] {
            length += 1
        }
        
        return length
    }
    
    private func hasPrefix(array: [UInt8], prefix: [UInt8]) -> Bool {
        guard array.count >= prefix.count else { return false }
        
        for i in 0..<prefix.count {
            if array[i] != prefix[i] {
                return false
            }
        }
        
        return true
    }
    
    // MARK: - Query Methods
    
    public func getNodeCount() -> Int {
        return nodeCount
    }
    
    public func getStats() -> RadixTreeStats {
        return stats
    }
    
    public func getHeight() -> Int {
        return calculateHeight(node: root)
    }
    
    private func calculateHeight(node: RadixNode<Value>) -> Int {
        guard !node.children.isEmpty else { return 0 }
        
        var maxChildHeight = 0
        for child in node.children.values {
            let childHeight = calculateHeight(node: child)
            maxChildHeight = max(maxChildHeight, childHeight)
        }
        
        return maxChildHeight + 1
    }
    
    // MARK: - Validation
    
    /// Validate tree structure
    public func validate() -> Bool {
        return validateNode(node: root)
    }
    
    private func validateNode(node: RadixNode<Value>) -> Bool {
        // Check prefix is non-empty for non-root nodes
        // Check all children are valid
        for child in node.children.values {
            if child.prefix.isEmpty && child !== root {
                return false
            }
            if !validateNode(node: child) {
                return false
            }
        }
        
        return true
    }
}

// MARK: - Statistics

/// Radix tree statistics
public struct RadixTreeStats: Codable {
    public var totalInserts: Int = 0
    public var totalDeletes: Int = 0
    public var totalSearches: Int = 0
    public var successfulSearches: Int = 0
    public var totalKeys: Int = 0
    
    public var searchHitRate: Double {
        guard totalSearches > 0 else { return 0.0 }
        return Double(successfulSearches) / Double(totalSearches)
    }
}

// MARK: - Errors

public enum RadixTreeError: Error, LocalizedError {
    case keyTooLong(length: Int, max: Int)
    case maxNodesReached
    case invalidKey
    
    public var errorDescription: String? {
        switch self {
        case .keyTooLong(let length, let max):
            return "Key too long: \(length) bytes (max: \(max))"
        case .maxNodesReached:
            return "Maximum nodes reached"
        case .invalidKey:
            return "Invalid key"
        }
    }
}

/*
 * IMPLEMENTATION NOTES:
 *
 * This implementation follows the RadixTree.tla specification and
 * implements the PATRICIA trie algorithm (Morrison 1968):
 *
 * 1. Path Compression (Morrison 1968):
 *    - Store common prefixes only once
 *    - Each node stores a prefix (byte sequence)
 *    - Reduces space compared to standard trie
 *    - Optimal for keys with common prefixes
 *
 * 2. Node Structure:
 *    - prefix: Compressed path segment (byte array)
 *    - children: Map from byte to child node (sparse)
 *    - isLeaf: Whether node stores a value
 *    - value: Stored value (if leaf)
 *    - lsn: Last modification LSN (for WAL)
 *
 * 3. Operations (Knuth 1973, Section 6.3):
 *    - Insert: O(k) where k = key length
 *      * Navigate tree comparing prefixes
 *      * Split nodes when prefix diverges
 *      * Create new leaf for key
 *    - Search: O(k)
 *      * Navigate tree matching prefixes
 *      * Return value if found at leaf
 *    - Delete: O(k)
 *      * Find and mark leaf as non-leaf
 *      * Merge nodes with single child
 *      * Remove nodes with no value/children
 *
 * 4. Node Splitting:
 *    - When inserting key that diverges from existing prefix
 *    - Create intermediate node with common prefix
 *    - Original node becomes child (prefix shortened)
 *    - New key becomes another child
 *
 * 5. Node Merging:
 *    - After deletion, if node has no value and single child
 *    - Merge node's prefix with child's prefix
 *    - Replace node with child
 *    - Reduces tree height
 *
 * 6. Prefix Matching:
 *    - Byte-by-byte comparison
 *    - UTF-8 encoding for Unicode support
 *    - Case-sensitive by default
 *
 * 7. Range Queries:
 *    - Find node corresponding to prefix
 *    - Collect all keys in subtree
 *    - Efficient for autocomplete, prefix search
 *
 * 8. Memory Efficiency (Nilsson & Tikkanen 1998):
 *    - Sparse children storage (dictionary)
 *    - Path compression reduces nodes
 *    - Only allocate for actual keys
 *    - ~50% space savings vs. standard trie
 *
 * 9. Correctness Properties (verified by TLA+):
 *    - All prefixes are valid (non-negative length)
 *    - Unique root exists
 *    - Tree structure is valid
 *    - Search finds inserted keys
 *    - Delete removes keys
 *
 * Academic References:
 * - Morrison (1968): Original PATRICIA algorithm
 * - Knuth (1973): Digital searching theory
 * - Nilsson & Tikkanen (1998): Modern optimizations
 *
 * Production Examples:
 * - Linux kernel: Routing tables (IP prefix matching)
 * - Redis: Key indexing with radix trees
 * - Git: Object storage prefix matching
 * - Network routing: Longest prefix matching
 *
 * Use Cases:
 * - String indexing with common prefixes
 * - Autocomplete / prefix search
 * - IP routing tables
 * - URL routing
 * - Dictionary implementations
 */

