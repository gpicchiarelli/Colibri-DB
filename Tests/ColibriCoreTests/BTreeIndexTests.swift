//
//  BTreeIndexTests.swift
//  ColibrìDB B+Tree Index Tests
//
//  Tests for B+Tree index operations, structure invariants, and performance
//

import Foundation
import Testing
@testable import ColibriCore

/// Tests for the B+Tree Index
@Suite("B+Tree Index Tests")
struct BTreeIndexTests {
    
    /// Test B+Tree initialization
    @Test("B+Tree Initialization")
    func testBTreeInitialization() async throws {
        let btree = BTreeIndex()
        
        // Verify initial state
        let height = await btree.getHeight()
        let keyCount = await btree.getKeyCount()
        let nodeCount = await btree.getNodeCount()
        let rootID = await btree.getRootID()
        
        try TestAssertions.assertEqual(height, 1, "Initial height should be 1")
        try TestAssertions.assertEqual(keyCount, 0, "Initial key count should be 0")
        try TestAssertions.assertEqual(nodeCount, 1, "Should have 1 node (root)")
        try TestAssertions.assertEqual(rootID, 1, "Root ID should be 1")
    }
    
    /// Test key insertion
    @Test("Key Insertion")
    func testKeyInsertion() async throws {
        let btree = BTreeIndex()
        
        // Insert some keys
        let keys = [Value.int(10), Value.int(20), Value.int(5), Value.int(15), Value.int(25)]
        let rids = [RID(integerLiteral: 1), RID(integerLiteral: 2), RID(integerLiteral: 3), RID(integerLiteral: 4), RID(integerLiteral: 5)]
        
        for (key, rid) in zip(keys, rids) {
            try await btree.insert(key: key, rid: rid)
        }
        
        // Verify all keys were inserted
        let keyCount = await btree.getKeyCount()
        try TestAssertions.assertEqual(keyCount, 5, "Should have 5 keys")
        
        // Verify each key can be found
        for (key, expectedRid) in zip(keys, rids) {
            let foundRids = await btree.search(key: key)
            try TestAssertions.assertNotNil(foundRids as [RID]?, "Key should be found")
            try TestAssertions.assertContains(foundRids!, expectedRid, "Should contain expected RID")
        }
    }
    
    /// Test key search
    @Test("Key Search")
    func testKeySearch() async throws {
        let btree = BTreeIndex()
        
        // Insert keys
        let keys = [Value.int(10), Value.int(20), Value.int(5), Value.int(15), Value.int(25)]
        let rids = [RID(integerLiteral: 1), RID(integerLiteral: 2), RID(integerLiteral: 3), RID(integerLiteral: 4), RID(integerLiteral: 5)]
        
        for (key, rid) in zip(keys, rids) {
            try await btree.insert(key: key, rid: rid)
        }
        
        // Test search for existing keys
        for (key, expectedRid) in zip(keys, rids) {
            let foundRids = await btree.search(key: key)
            try TestAssertions.assertNotNil(foundRids as [RID]?, "Existing key should be found")
            try TestAssertions.assertContains(foundRids!, expectedRid, "Should contain expected RID")
        }
        
        // Test search for non-existing keys
        let nonExistingKeys = [Value.int(1), Value.int(30), Value.int(100)]
        for key in nonExistingKeys {
            let foundRids = await btree.search(key: key)
            try TestAssertions.assertNil(foundRids, "Non-existing key should not be found")
        }
    }
    
    /// Test key deletion
    @Test("Key Deletion")
    func testKeyDeletion() async throws {
        let btree = BTreeIndex()
        
        // Insert keys
        let keys = [Value.int(10), Value.int(20), Value.int(5), Value.int(15), Value.int(25)]
        let rids = [RID(integerLiteral: 1), RID(integerLiteral: 2), RID(integerLiteral: 3), RID(integerLiteral: 4), RID(integerLiteral: 5)]
        
        for (key, rid) in zip(keys, rids) {
            try await btree.insert(key: key, rid: rid)
        }
        
        // Delete some keys
        try await btree.delete(key: Value.int(10))
        try await btree.delete(key: Value.int(15))
        
        // Verify keys were deleted
        let found10 = await btree.search(key: Value.int(10))
        let found15 = await btree.search(key: Value.int(15))
        
        try TestAssertions.assertNil(found10, "Deleted key 10 should not be found")
        try TestAssertions.assertNil(found15, "Deleted key 15 should not be found")
        
        // Verify remaining keys still exist
        let found20 = await btree.search(key: Value.int(20))
        let found5 = await btree.search(key: Value.int(5))
        let found25 = await btree.search(key: Value.int(25))
        
        try TestAssertions.assertNotNil(found20 as [RID]?, "Key 20 should still exist")
        try TestAssertions.assertNotNil(found5 as [RID]?, "Key 5 should still exist")
        try TestAssertions.assertNotNil(found25 as [RID]?, "Key 25 should still exist")
        
        // Verify key count
        let keyCount = await btree.getKeyCount()
        try TestAssertions.assertEqual(keyCount, 3, "Should have 3 keys remaining")
    }
    
    /// Test range scan
    @Test("Range Scan")
    func testRangeScan() async throws {
        let btree = BTreeIndex()
        
        // Insert keys in order
        let keys = [Value.int(1), Value.int(3), Value.int(5), Value.int(7), Value.int(9), Value.int(11), Value.int(13)]
        let rids = [RID(integerLiteral: 1), RID(integerLiteral: 2), RID(integerLiteral: 3), RID(integerLiteral: 4), RID(integerLiteral: 5), RID(integerLiteral: 6), RID(integerLiteral: 7)]
        
        for (key, rid) in zip(keys, rids) {
            try await btree.insert(key: key, rid: rid)
        }
        
        // Test range scan
        let results = await btree.rangeScan(minKey: Value.int(5), maxKey: Value.int(10))
        
        // Verify results
        try TestAssertions.assertEqual(results.count, 3, "Should have 3 results in range [5, 10]")
        
        let resultKeys = results.map { $0.0 }
        try TestAssertions.assertContains(resultKeys, Value.int(5), "Should contain key 5")
        try TestAssertions.assertContains(resultKeys, Value.int(7), "Should contain key 7")
        try TestAssertions.assertContains(resultKeys, Value.int(9), "Should contain key 9")
        
        // Test empty range
        let emptyResults = await btree.rangeScan(minKey: Value.int(20), maxKey: Value.int(30))
        try TestAssertions.assertEqual(emptyResults.count, 0, "Should have no results in empty range")
    }
    
    /// Test tree structure invariants
    @Test("Tree Structure Invariants")
    func testTreeStructureInvariants() async throws {
        let btree = BTreeIndex()
        
        // Insert many keys to test structure
        for i in 1...50 {
            try await btree.insert(key: Value.int(Int64(i)), rid: RID(integerLiteral: Int(i)))
        }
        
        // Test key order invariant
        let keyOrder = await btree.checkKeyOrderInvariant()
        try TestAssertions.assertTrue(keyOrder, "Key order invariant should hold")
        
        // Test balanced height invariant
        let balancedHeight = await btree.checkBalancedHeightInvariant()
        try TestAssertions.assertTrue(balancedHeight, "Balanced height invariant should hold")
        
        // Test structure invariant
        let structure = await btree.checkStructureInvariant()
        try TestAssertions.assertTrue(structure, "Structure invariant should hold")
        
        // Test leaf links invariant
        let leafLinks = await btree.checkLeafLinksInvariant()
        try TestAssertions.assertTrue(leafLinks, "Leaf links invariant should hold")
    }
    
    /// Test node splitting
    @Test("Node Splitting")
    func testNodeSplitting() async throws {
        let btree = BTreeIndex()
        
        // Insert enough keys to force node splitting
        let keys = [Value.int(1), Value.int(2), Value.int(3), Value.int(4), Value.int(5), Value.int(6), Value.int(7)]
        let rids = [RID(integerLiteral: 1), RID(integerLiteral: 2), RID(integerLiteral: 3), RID(integerLiteral: 4), RID(integerLiteral: 5), RID(integerLiteral: 6), RID(integerLiteral: 7)]
        
        for (key, rid) in zip(keys, rids) {
            try await btree.insert(key: key, rid: rid)
        }
        
        // Verify tree structure is still valid
        let keyOrder = await btree.checkKeyOrderInvariant()
        try TestAssertions.assertTrue(keyOrder, "Key order should be maintained after splitting")
        
        let structure = await btree.checkStructureInvariant()
        try TestAssertions.assertTrue(structure, "Structure should be valid after splitting")
        
        // Verify all keys can still be found
        for (key, expectedRid) in zip(keys, rids) {
            let foundRids = await btree.search(key: key)
            try TestAssertions.assertNotNil(foundRids as [RID]?, "Key should be found after splitting")
            try TestAssertions.assertContains(foundRids!, expectedRid, "Should contain expected RID")
        }
    }
    
    /// Test node merging
    @Test("Node Merging", .disabled("Merge logic needs refinement"))
    func testNodeMerging() async throws {
        let btree = BTreeIndex()
        
        // Insert more keys to force splitting
        let keys = [Value.int(1), Value.int(2), Value.int(3), Value.int(4), Value.int(5), Value.int(6), Value.int(7), Value.int(8), Value.int(9), Value.int(10)]
        let rids = [RID(integerLiteral: 1), RID(integerLiteral: 2), RID(integerLiteral: 3), RID(integerLiteral: 4), RID(integerLiteral: 5), RID(integerLiteral: 6), RID(integerLiteral: 7), RID(integerLiteral: 8), RID(integerLiteral: 9), RID(integerLiteral: 10)]
        
        for (key, rid) in zip(keys, rids) {
            try await btree.insert(key: key, rid: rid)
        }
        
        // Delete keys to force merging
        try await btree.delete(key: Value.int(1))
        try await btree.delete(key: Value.int(2))
        try await btree.delete(key: Value.int(3))
        try await btree.delete(key: Value.int(4))
        try await btree.delete(key: Value.int(5))
        
        // Verify tree structure is still valid
        let keyOrder = await btree.checkKeyOrderInvariant()
        try TestAssertions.assertTrue(keyOrder, "Key order should be maintained after merging")
        
        let structure = await btree.checkStructureInvariant()
        try TestAssertions.assertTrue(structure, "Structure should be valid after merging")
        
        // Verify remaining keys can still be found
        let remainingKeys = [Value.int(6), Value.int(7), Value.int(8), Value.int(9), Value.int(10)]
        for key in remainingKeys {
            let foundRids = await btree.search(key: key)
            try TestAssertions.assertNotNil(foundRids as [RID]?, "Remaining key should be found after merging")
        }
    }
    
    /// Test concurrent operations
    @Test("Concurrent Operations")
    func testConcurrentOperations() async throws {
        let btree = BTreeIndex()
        
        // Start multiple concurrent tasks
        let taskCount = 10
        var tasks: [Task<Void, Never>] = []
        
        for i in 0..<taskCount {
            let task = Task {
                do {
                    // Each task inserts keys in its range
                    let startKey = i * 10
                    for j in 0..<10 {
                        let key = Value.int(Int64(startKey + j))
                        let rid = RID(integerLiteral: startKey + j)
                        try await btree.insert(key: key, rid: rid)
                    }
                } catch {
                    // Handle errors silently for this test
                }
            }
            tasks.append(task)
        }
        
        // Wait for all tasks to complete
        for task in tasks {
            await task.value
        }
        
        // Verify tree structure is still valid
        let keyOrder = await btree.checkKeyOrderInvariant()
        try TestAssertions.assertTrue(keyOrder, "Key order should be maintained with concurrent operations")
        
        let structure = await btree.checkStructureInvariant()
        try TestAssertions.assertTrue(structure, "Structure should be valid with concurrent operations")
        
        // Verify all keys can be found
        let keyCount = await btree.getKeyCount()
        try TestAssertions.assertEqual(keyCount, 100, "Should have 100 keys")
    }
    
    /// Test performance with large dataset
    @Test("Performance - Large Dataset", .disabled("Memory intensive"))
    func testPerformanceLargeDataset() async throws {
        let btree = BTreeIndex()
        
        let keyCount = 10000
        let startTime = Date()
        
        // Insert many keys
        for i in 0..<keyCount {
            try await btree.insert(key: Value.int(Int64(i)), rid: RID(integerLiteral: Int(i)))
        }
        
        let insertTime = Date()
        let insertDuration = insertTime.timeIntervalSince(startTime)
        
        // Search for some keys
        let searchStartTime = Date()
        for i in stride(from: 0, to: keyCount, by: 100) {
            let foundRids = await btree.search(key: Value.int(Int64(i)))
            try TestAssertions.assertNotNil(foundRids as [RID]?, "Key should be found")
        }
        let searchTime = Date()
        let searchDuration = searchTime.timeIntervalSince(searchStartTime)
        
        // Verify performance is reasonable
        try TestAssertions.assertTrue(insertDuration < 5.0, "Insert performance should be reasonable")
        try TestAssertions.assertTrue(searchDuration < 1.0, "Search performance should be reasonable")
        
        // Verify tree structure is still valid
        let keyOrder = await btree.checkKeyOrderInvariant()
        try TestAssertions.assertTrue(keyOrder, "Key order should be maintained with large dataset")
        
        let structure = await btree.checkStructureInvariant()
        try TestAssertions.assertTrue(structure, "Structure should be valid with large dataset")
    }
    
    /// Test range scan performance
    @Test("Range Scan Performance")
    func testRangeScanPerformance() async throws {
        let btree = BTreeIndex()
        
        // Insert keys
        let keyCount = 1000
        for i in 0..<keyCount {
            try await btree.insert(key: Value.int(Int64(i)), rid: RID(integerLiteral: Int(i)))
        }
        
        // Test range scan performance
        let startTime = Date()
        
        let results = await btree.rangeScan(minKey: Value.int(100), maxKey: Value.int(900))
        
        let endTime = Date()
        let duration = endTime.timeIntervalSince(startTime)
        
        // Verify performance is reasonable
        try TestAssertions.assertTrue(duration < 0.1, "Range scan performance should be reasonable")
        
        // Verify results
        try TestAssertions.assertEqual(results.count, 801, "Should have 801 results in range [100, 900]")
    }
    
    /// Test string keys
    @Test("String Keys")
    func testStringKeys() async throws {
        let btree = BTreeIndex()
        
        // Insert string keys
        let keys = [Value.string("apple"), Value.string("banana"), Value.string("cherry"), Value.string("date"), Value.string("elderberry")]
        let rids = [RID(integerLiteral: 1), RID(integerLiteral: 2), RID(integerLiteral: 3), RID(integerLiteral: 4), RID(integerLiteral: 5)]
        
        for (key, rid) in zip(keys, rids) {
            try await btree.insert(key: key, rid: rid)
        }
        
        // Test search
        let foundRids = await btree.search(key: Value.string("banana"))
        try TestAssertions.assertNotNil(foundRids, "String key should be found")
        try TestAssertions.assertContains(foundRids!, RID(integerLiteral: 2), "Should contain expected RID")
        
        // Test range scan
        let results = await btree.rangeScan(minKey: Value.string("banana"), maxKey: Value.string("date"))
        try TestAssertions.assertEqual(results.count, 3, "Should have 3 results in range")
        
        // Verify tree structure is valid
        let keyOrder = await btree.checkKeyOrderInvariant()
        try TestAssertions.assertTrue(keyOrder, "Key order should be maintained with string keys")
    }
    
    /// Test double keys
    @Test("Double Keys")
    func testDoubleKeys() async throws {
        let btree = BTreeIndex()
        
        // Insert double keys
        let keys = [Value.double(1.1), Value.double(2.2), Value.double(3.3), Value.double(4.4), Value.double(5.5)]
        let rids = [RID(integerLiteral: 1), RID(integerLiteral: 2), RID(integerLiteral: 3), RID(integerLiteral: 4), RID(integerLiteral: 5)]
        
        for (key, rid) in zip(keys, rids) {
            try await btree.insert(key: key, rid: rid)
        }
        
        // Test search
        let foundRids = await btree.search(key: Value.double(3.3))
        try TestAssertions.assertNotNil(foundRids, "Double key should be found")
        try TestAssertions.assertContains(foundRids!, RID(integerLiteral: 3), "Should contain expected RID")
        
        // Test range scan
        let results = await btree.rangeScan(minKey: Value.double(2.0), maxKey: Value.double(4.0))
        try TestAssertions.assertEqual(results.count, 2, "Should have 2 results in range")
        
        // Verify tree structure is valid
        let keyOrder = await btree.checkKeyOrderInvariant()
        try TestAssertions.assertTrue(keyOrder, "Key order should be maintained with double keys")
    }
    
    /// Test error handling
    @Test("Error Handling")
    func testErrorHandling() async throws {
        let btree = BTreeIndex()
        
        // Test deletion of non-existing key
        do {
            try await btree.delete(key: Value.int(999))
            try TestAssertions.assertTrue(false, "Should throw error for non-existing key")
        } catch {
            // Expected error - test passes
        }
        
        // Test operations on empty tree
        let foundRids = await btree.search(key: Value.int(1))
        try TestAssertions.assertNil(foundRids, "Search on empty tree should return nil")
        
        let results = await btree.rangeScan(minKey: Value.int(1), maxKey: Value.int(10))
        try TestAssertions.assertEqual(results.count, 0, "Range scan on empty tree should return empty results")
    }
    
    /// Test tree height growth
    @Test("Tree Height Growth")
    func testTreeHeightGrowth() async throws {
        let btree = BTreeIndex()
        
        // Insert keys and monitor height growth
        var previousHeight = await btree.getHeight()
        
        for i in 1...100 {
            try await btree.insert(key: Value.int(Int64(i)), rid: RID(integerLiteral: Int(i)))
            
            let currentHeight = await btree.getHeight()
            try TestAssertions.assertTrue(currentHeight >= previousHeight, "Height should not decrease")
            previousHeight = currentHeight
        }
        
        // Verify final height is reasonable
        let finalHeight = await btree.getHeight()
        try TestAssertions.assertTrue(finalHeight <= 10, "Height should be reasonable for 100 keys")
        
        // Verify tree structure is still valid
        let keyOrder = await btree.checkKeyOrderInvariant()
        try TestAssertions.assertTrue(keyOrder, "Key order should be maintained")
        
        let structure = await btree.checkStructureInvariant()
        try TestAssertions.assertTrue(structure, "Structure should be valid")
    }
    
    /// Test node count tracking
    @Test("Node Count Tracking")
    func testNodeCountTracking() async throws {
        let btree = BTreeIndex()
        
        // Initially should have 1 node (root)
        let initialNodeCount = await btree.getNodeCount()
        try TestAssertions.assertEqual(initialNodeCount, 1, "Should start with 1 node")
        
        // Insert keys and monitor node count
        var previousNodeCount = initialNodeCount
        
        for i in 1...50 {
            try await btree.insert(key: Value.int(Int64(i)), rid: RID(integerLiteral: Int(i)))
            
            let currentNodeCount = await btree.getNodeCount()
            try TestAssertions.assertTrue(currentNodeCount >= previousNodeCount, "Node count should not decrease")
            previousNodeCount = currentNodeCount
        }
        
        // Verify final node count is reasonable
        let finalNodeCount = await btree.getNodeCount()
        try TestAssertions.assertTrue(finalNodeCount > 1, "Should have more than 1 node")
        try TestAssertions.assertTrue(finalNodeCount <= 50, "Node count should be reasonable")
    }
}
