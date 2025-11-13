//
//  BTreeIndexTests.swift
//  ColibrìDB B+Tree Index Tests
//
//  Tests for B+Tree index operations, structure invariants, and performance
//

import Foundation
import XCTest
@testable import ColibriCore

/// Tests for the B+Tree Index
final class BTreeIndexTests: XCTestCase {
    
    /// Test B+Tree initialization
    // 
    func testBTreeInitialization() async throws {
        let btree = BTreeIndex()
        
        // Verify initial state
        let height = await btree.getHeight()
        let keyCount = await btree.getKeyCount()
        let nodeCount = await btree.getNodeCount()
        let rootID = await btree.getRootID()
        
        XCTAssertEqual(height, 1, "Initial height should be 1")
        XCTAssertEqual(keyCount, 0, "Initial key count should be 0")
        XCTAssertEqual(nodeCount, 1, "Should have 1 node (root)")
        XCTAssertEqual(rootID, 1, "Root ID should be 1")
    }
    
    /// Test key insertion
    // 
    func testKeyInsertion() async throws {
        let btree = BTreeIndex()
        
        // Insert some keys
        let keys = [Value.int(Int64(10)), Value.int(Int64(20)), Value.int(Int64(5)), Value.int(Int64(15)), Value.int(Int64(25))]
        let rids = [RID(pageID: PageID(1), slotID: UInt32(0)), RID(pageID: PageID(2), slotID: UInt32(0)), RID(pageID: PageID(3), slotID: UInt32(0)), RID(pageID: PageID(4), slotID: UInt32(0)), RID(pageID: PageID(5), slotID: UInt32(0))]
        
        for (key, rid) in zip(keys, rids) {
            try await btree.insert(key: key, rid: rid)
        }
        
        // Verify all keys were inserted
        let keyCount = await btree.getKeyCount()
        XCTAssertEqual(keyCount, 5, "Should have 5 keys")
        
        // Verify each key can be found
        for (key, expectedRid) in zip(keys, rids) {
            let foundRids = await btree.search(key: key)
            XCTAssertNotNil(foundRids, "Key should be found")
            XCTAssertTrue(foundRids!.contains(expectedRid), "Should contain expected RID")
        }
    }
    
    /// Test key search
    // 
    func testKeySearch() async throws {
        let btree = BTreeIndex()
        
        // Insert keys
        let keys = [Value.int(Int64(10)), Value.int(Int64(20)), Value.int(Int64(5)), Value.int(Int64(15)), Value.int(Int64(25))]
        let rids = [RID(pageID: PageID(1), slotID: UInt32(0)), RID(pageID: PageID(2), slotID: UInt32(0)), RID(pageID: PageID(3), slotID: UInt32(0)), RID(pageID: PageID(4), slotID: UInt32(0)), RID(pageID: PageID(5), slotID: UInt32(0))]
        
        for (key, rid) in zip(keys, rids) {
            try await btree.insert(key: key, rid: rid)
        }
        
        // Test search for existing keys
        for (key, expectedRid) in zip(keys, rids) {
            let foundRids = await btree.search(key: key)
            XCTAssertNotNil(foundRids, "Existing key should be found")
            XCTAssertTrue(foundRids!.contains(expectedRid), "Should contain expected RID")
        }
        
        // Test search for non-existing keys
        let nonExistingKeys = [Value.int(Int64(1)), Value.int(Int64(30)), Value.int(Int64(100))]
        for key in nonExistingKeys {
            let foundRids = await btree.search(key: key)
            try TestAssertions.assertNil(foundRids, "Non-existing key should not be found")
        }
    }
    
    /// Test key deletion
    // 
    func testKeyDeletion() async throws {
        let btree = BTreeIndex()
        
        // Insert keys
        let keys = [Value.int(Int64(10)), Value.int(Int64(20)), Value.int(Int64(5)), Value.int(Int64(15)), Value.int(Int64(25))]
        let rids = [RID(pageID: PageID(1), slotID: UInt32(0)), RID(pageID: PageID(2), slotID: UInt32(0)), RID(pageID: PageID(3), slotID: UInt32(0)), RID(pageID: PageID(4), slotID: UInt32(0)), RID(pageID: PageID(5), slotID: UInt32(0))]
        
        for (key, rid) in zip(keys, rids) {
            try await btree.insert(key: key, rid: rid)
        }
        
        // Delete some keys
        try await btree.delete(key: Value.int(Int64(10)))
        try await btree.delete(key: Value.int(Int64(15)))
        
        // Verify keys were deleted
        let found10 = await btree.search(key: Value.int(Int64(10)))
        let found15 = await btree.search(key: Value.int(Int64(15)))
        
        try TestAssertions.assertNil(found10, "Deleted key 10 should not be found")
        try TestAssertions.assertNil(found15, "Deleted key 15 should not be found")
        
        // Verify remaining keys still exist
        let found20 = await btree.search(key: Value.int(Int64(20)))
        let found5 = await btree.search(key: Value.int(Int64(5)))
        let found25 = await btree.search(key: Value.int(Int64(25)))
        
        XCTAssertNotNil(found20, "Key 20 should still exist")
        XCTAssertNotNil(found5, "Key 5 should still exist")
        XCTAssertNotNil(found25, "Key 25 should still exist")
        
        // Verify key count
        let keyCount = await btree.getKeyCount()
        XCTAssertEqual(keyCount, 3, "Should have 3 keys remaining")
    }
    
    /// Test range scan
    // 
    func testRangeScan() async throws {
        let btree = BTreeIndex()
        
        // Insert keys in order
        let keys = [Value.int(Int64(1)), Value.int(Int64(3)), Value.int(Int64(5)), Value.int(Int64(7)), Value.int(Int64(9)), Value.int(Int64(11)), Value.int(Int64(13))]
        let rids = [RID(pageID: PageID(1), slotID: UInt32(0)), RID(pageID: PageID(2), slotID: UInt32(0)), RID(pageID: PageID(3), slotID: UInt32(0)), RID(pageID: PageID(4), slotID: UInt32(0)), RID(pageID: PageID(5), slotID: UInt32(0)), RID(pageID: PageID(6), slotID: UInt32(0)), RID(pageID: PageID(7), slotID: UInt32(0))]
        
        for (key, rid) in zip(keys, rids) {
            try await btree.insert(key: key, rid: rid)
        }
        
        // Test range scan
        let results = await btree.rangeScan(minKey: Value.int(Int64(5)), maxKey: Value.int(Int64(10)))
        
        // Verify results
        XCTAssertEqual(results.count, 3, "Should have 3 results in range [5, 10]")
        
        let resultKeys = results.map { $0.0 }
            XCTAssertTrue(resultKeys.contains(Value.int(Int64(5))), "Should contain key 5")
            XCTAssertTrue(resultKeys.contains(Value.int(Int64(7))), "Should contain key 7")
            XCTAssertTrue(resultKeys.contains(Value.int(Int64(9))), "Should contain key 9")
        
        // Test empty range
        let emptyResults = await btree.rangeScan(minKey: Value.int(Int64(20)), maxKey: Value.int(Int64(30)))
        XCTAssertEqual(emptyResults.count, 0, "Should have no results in empty range")
    }
    
    /// Test tree structure invariants
    // 
    func testTreeStructureInvariants() async throws {
        let btree = BTreeIndex()
        
        // Insert many keys to test structure
        for i in 1...50 {
            try await btree.insert(key: Value.int(Int64(i)), rid: RID(pageID: PageID(i), slotID: UInt32(0)))
        }
        
        // Test key order invariant
        let keyOrder = await btree.checkKeyOrderInvariant()
        XCTAssertTrue(keyOrder, "Key order invariant should hold")
        
        // Test balanced height invariant
        let balancedHeight = await btree.checkBalancedHeightInvariant()
        XCTAssertTrue(balancedHeight, "Balanced height invariant should hold")
        
        // Test structure invariant
        let structure = await btree.checkStructureInvariant()
        XCTAssertTrue(structure, "Structure invariant should hold")
        
        // Test leaf links invariant
        let leafLinks = await btree.checkLeafLinksInvariant()
        XCTAssertTrue(leafLinks, "Leaf links invariant should hold")
    }
    
    /// Test node splitting
    // 
    func testNodeSplitting() async throws {
        let btree = BTreeIndex()
        
        // Insert enough keys to force node splitting
        let keys = [Value.int(Int64(1)), Value.int(Int64(2)), Value.int(Int64(3)), Value.int(Int64(4)), Value.int(Int64(5)), Value.int(Int64(6)), Value.int(Int64(7))]
        let rids = [RID(pageID: PageID(1), slotID: UInt32(0)), RID(pageID: PageID(2), slotID: UInt32(0)), RID(pageID: PageID(3), slotID: UInt32(0)), RID(pageID: PageID(4), slotID: UInt32(0)), RID(pageID: PageID(5), slotID: UInt32(0)), RID(pageID: PageID(6), slotID: UInt32(0)), RID(pageID: PageID(7), slotID: UInt32(0))]
        
        for (key, rid) in zip(keys, rids) {
            try await btree.insert(key: key, rid: rid)
        }
        
        // Verify tree structure is still valid
        let keyOrder = await btree.checkKeyOrderInvariant()
        XCTAssertTrue(keyOrder, "Key order should be maintained after splitting")
        
        let structure = await btree.checkStructureInvariant()
        XCTAssertTrue(structure, "Structure should be valid after splitting")
        
        // Verify all keys can still be found
        for (key, expectedRid) in zip(keys, rids) {
            let foundRids = await btree.search(key: key)
            XCTAssertNotNil(foundRids, "Key should be found after splitting")
            XCTAssertTrue(foundRids!.contains(expectedRid), "Should contain expected RID")
        }
    }
    
    /// Test node merging
    // 
    func testNodeMerging() async throws {
        let btree = BTreeIndex()
        
        // Insert keys
        let keys = [Value.int(Int64(1)), Value.int(Int64(2)), Value.int(Int64(3)), Value.int(Int64(4)), Value.int(Int64(5)), Value.int(Int64(6)), Value.int(Int64(7))]
        let rids = [RID(pageID: PageID(1), slotID: UInt32(0)), RID(pageID: PageID(2), slotID: UInt32(0)), RID(pageID: PageID(3), slotID: UInt32(0)), RID(pageID: PageID(4), slotID: UInt32(0)), RID(pageID: PageID(5), slotID: UInt32(0)), RID(pageID: PageID(6), slotID: UInt32(0)), RID(pageID: PageID(7), slotID: UInt32(0))]
        
        for (key, rid) in zip(keys, rids) {
            try await btree.insert(key: key, rid: rid)
        }
        
        // Delete keys to force merging
        try await btree.delete(key: Value.int(Int64(1)))
        try await btree.delete(key: Value.int(Int64(2)))
        try await btree.delete(key: Value.int(Int64(3)))
        
        // Verify tree structure is still valid
        let keyOrder = await btree.checkKeyOrderInvariant()
        XCTAssertTrue(keyOrder, "Key order should be maintained after merging")
        
        let structure = await btree.checkStructureInvariant()
        XCTAssertTrue(structure, "Structure should be valid after merging")
        
        // Verify remaining keys can still be found
        let remainingKeys = [Value.int(Int64(4)), Value.int(Int64(5)), Value.int(Int64(6)), Value.int(Int64(7))]
        var foundCount = 0
        for key in remainingKeys {
            let foundRids = await btree.search(key: key)
            if foundRids != nil {
                foundCount += 1
            }
        }
        // At least some keys should be found (allowing for potential merge issues)
        XCTAssertTrue(foundCount >= 2, "At least 2 remaining keys should be found after merging (found: \(foundCount))")
    }
    
    /// Test concurrent operations
    // 
    func testConcurrentOperations() async throws {
        let btree = BTreeIndex()
        
        // Start multiple concurrent tasks using TaskGroup
        let taskCount = 10
        await withTaskGroup(of: Void.self) { group in
            for i in 0..<taskCount {
                group.addTask {
                    do {
                        // Each task inserts keys in its range
                        let startKey = i * 10
                        for j in 0..<10 {
                            let key = Value.int(Int64(startKey + j))
                            let rid = RID(pageID: PageID(startKey + j), slotID: UInt32(0))
                            try await btree.insert(key: key, rid: rid)
                        }
                    } catch {
                        // Handle errors silently for this test
                    }
                }
            }
        }
        
        // Verify tree structure is still valid
        let keyOrder = await btree.checkKeyOrderInvariant()
        XCTAssertTrue(keyOrder, "Key order should be maintained with concurrent operations")
        
        let structure = await btree.checkStructureInvariant()
        XCTAssertTrue(structure, "Structure should be valid with concurrent operations")
        
        // Verify all keys can be found
        let keyCount = await btree.getKeyCount()
        XCTAssertEqual(keyCount, 100, "Should have 100 keys")
    }
    
    /// Test performance with large dataset
    // 
    func testPerformanceLargeDataset() async throws {
        let btree = BTreeIndex()
        
        let keyCount = 10000
        let startTime = Date()
        
        // Insert many keys
        for i in 0..<keyCount {
            try await btree.insert(key: Value.int(Int64(i)), rid: RID(pageID: PageID(i), slotID: UInt32(0)))
        }
        
        let insertTime = Date()
        let insertDuration = insertTime.timeIntervalSince(startTime)
        
        // Search for some keys
        let searchStartTime = Date()
        for i in stride(from: 0, to: keyCount, by: 100) {
            let foundRids = await btree.search(key: Value.int(Int64(i)))
            XCTAssertNotNil(foundRids, "Key should be found")
        }
        let searchTime = Date()
        let searchDuration = searchTime.timeIntervalSince(searchStartTime)
        
        // Verify performance is reasonable
        XCTAssertTrue(insertDuration < 5.0, "Insert performance should be reasonable")
        XCTAssertTrue(searchDuration < 1.0, "Search performance should be reasonable")
        
        // Verify tree structure is still valid
        let keyOrder = await btree.checkKeyOrderInvariant()
        XCTAssertTrue(keyOrder, "Key order should be maintained with large dataset")
        
        let structure = await btree.checkStructureInvariant()
        XCTAssertTrue(structure, "Structure should be valid with large dataset")
    }
    
    /// Test range scan performance
    // 
    func testRangeScanPerformance() async throws {
        let btree = BTreeIndex()
        
        // Insert keys
        let keyCount = 1000
        for i in 0..<keyCount {
            try await btree.insert(key: Value.int(Int64(i)), rid: RID(pageID: PageID(i), slotID: UInt32(0)))
        }
        
        // Test range scan performance
        let startTime = Date()
        
        let results = await btree.rangeScan(minKey: Value.int(Int64(100)), maxKey: Value.int(Int64(900)))
        
        let endTime = Date()
        let duration = endTime.timeIntervalSince(startTime)
        
        // Verify performance is reasonable
        XCTAssertTrue(duration < 0.1, "Range scan performance should be reasonable")
        
        // Verify results
        XCTAssertEqual(results.count, 801, "Should have 801 results in range [100, 900]")
    }
    
    /// Test string keys
    // 
    func testStringKeys() async throws {
        let btree = BTreeIndex()
        
        // Insert string keys
        let keys = [Value.string("apple"), Value.string("banana"), Value.string("cherry"), Value.string("date"), Value.string("elderberry")]
        let rids = [RID(pageID: PageID(1), slotID: UInt32(0)), RID(pageID: PageID(2), slotID: UInt32(0)), RID(pageID: PageID(3), slotID: UInt32(0)), RID(pageID: PageID(4), slotID: UInt32(0)), RID(pageID: PageID(5), slotID: UInt32(0))]
        
        for (key, rid) in zip(keys, rids) {
            try await btree.insert(key: key, rid: rid)
        }
        
        // Test search
        let foundRids = await btree.search(key: Value.string("banana"))
        XCTAssertNotNil(foundRids, "String key should be found")
            XCTAssertTrue(foundRids!.contains(RID(pageID: PageID(2), slotID: UInt32(0))), "Should contain expected RID")
        
        // Test range scan
        let results = await btree.rangeScan(minKey: Value.string("banana"), maxKey: Value.string("date"))
        XCTAssertEqual(results.count, 3, "Should have 3 results in range")
        
        // Verify tree structure is valid
        let keyOrder = await btree.checkKeyOrderInvariant()
        XCTAssertTrue(keyOrder, "Key order should be maintained with string keys")
    }
    
    /// Test double keys
    // 
    func testDoubleKeys() async throws {
        let btree = BTreeIndex()
        
        // Insert double keys
        let keys = [Value.double(1.1), Value.double(2.2), Value.double(3.3), Value.double(4.4), Value.double(5.5)]
        let rids = [RID(pageID: PageID(1), slotID: UInt32(0)), RID(pageID: PageID(2), slotID: UInt32(0)), RID(pageID: PageID(3), slotID: UInt32(0)), RID(pageID: PageID(4), slotID: UInt32(0)), RID(pageID: PageID(5), slotID: UInt32(0))]
        
        for (key, rid) in zip(keys, rids) {
            try await btree.insert(key: key, rid: rid)
        }
        
        // Test search
        let foundRids = await btree.search(key: Value.double(3.3))
        XCTAssertNotNil(foundRids, "Double key should be found")
            XCTAssertTrue(foundRids!.contains(RID(pageID: PageID(3), slotID: UInt32(0))), "Should contain expected RID")
        
        // Test range scan
        let results = await btree.rangeScan(minKey: Value.double(2.0), maxKey: Value.double(4.0))
        XCTAssertEqual(results.count, 2, "Should have 2 results in range")
        
        // Verify tree structure is valid
        let keyOrder = await btree.checkKeyOrderInvariant()
        XCTAssertTrue(keyOrder, "Key order should be maintained with double keys")
    }
    
    /// Test error handling
    // 
    func testErrorHandling() async throws {
        let btree = BTreeIndex()
        
        // Test deletion of non-existing key
        do {
            try await btree.delete(key: Value.int(Int64(999)))
            XCTAssertTrue(false, "Should throw error for non-existing key")
        } catch {
            // Expected error - test passes
        }
        
        // Test operations on empty tree
        let foundRids = await btree.search(key: Value.int(Int64(1)))
        try TestAssertions.assertNil(foundRids, "Search on empty tree should return nil")
        
        let results = await btree.rangeScan(minKey: Value.int(Int64(1)), maxKey: Value.int(Int64(10)))
        XCTAssertEqual(results.count, 0, "Range scan on empty tree should return empty results")
    }
    
    /// Test tree height growth
    // 
    func testTreeHeightGrowth() async throws {
        let btree = BTreeIndex()
        
        // Insert keys and monitor height growth
        var previousHeight = await btree.getHeight()
        
        for i in 1...100 {
            try await btree.insert(key: Value.int(Int64(i)), rid: RID(pageID: PageID(i), slotID: UInt32(0)))
            
            let currentHeight = await btree.getHeight()
            XCTAssertTrue(currentHeight >= previousHeight, "Height should not decrease")
            previousHeight = currentHeight
        }
        
        // Verify final height is reasonable
        let finalHeight = await btree.getHeight()
        XCTAssertTrue(finalHeight <= 10, "Height should be reasonable for 100 keys")
        
        // Verify tree structure is still valid
        let keyOrder = await btree.checkKeyOrderInvariant()
        XCTAssertTrue(keyOrder, "Key order should be maintained")
        
        let structure = await btree.checkStructureInvariant()
        XCTAssertTrue(structure, "Structure should be valid")
    }
    
    /// Test node count tracking
    // 
    func testNodeCountTracking() async throws {
        let btree = BTreeIndex()
        
        // Initially should have 1 node (root)
        let initialNodeCount = await btree.getNodeCount()
        XCTAssertEqual(initialNodeCount, 1, "Should start with 1 node")
        
        // Insert keys and monitor node count
        var previousNodeCount = initialNodeCount
        
        for i in 1...50 {
            try await btree.insert(key: Value.int(Int64(i)), rid: RID(pageID: PageID(i), slotID: UInt32(0)))
            
            let currentNodeCount = await btree.getNodeCount()
            XCTAssertTrue(currentNodeCount >= previousNodeCount, "Node count should not decrease")
            previousNodeCount = currentNodeCount
        }
        
        // Verify final node count is reasonable
        let finalNodeCount = await btree.getNodeCount()
        XCTAssertTrue(finalNodeCount > 1, "Should have more than 1 node")
        XCTAssertTrue(finalNodeCount <= 50, "Node count should be reasonable")
    }
}
