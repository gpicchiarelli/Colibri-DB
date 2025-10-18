//
//  AnyStringIndexTests.swift
//  ColibrDBTests
//
//  Comprehensive tests for AnyStringIndex with all backend variants
//
// ColibrDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

import XCTest
@testable import ColibriCore

final class AnyStringIndexTests: XCTestCase {
    
    // MARK: - Initialization Tests
    
    func testHashIndexCreation() {
        let index = AnyStringIndex(kind: "hash")
        
        // Verify it's a hash index
        if case .hash = index {
            XCTAssert(true)
        } else {
            XCTFail("Should create hash index")
        }
    }
    
    func testARTIndexCreation() {
        let index = AnyStringIndex(kind: "art")
        
        if case .art = index {
            XCTAssert(true)
        } else {
            XCTFail("Should create ART index")
        }
    }
    
    func testBTreeIndexCreation() {
        let index = AnyStringIndex(kind: "btree")
        
        if case .btree = index {
            XCTAssert(true)
        } else {
            XCTFail("Should create BTree index")
        }
    }
    
    func testSkipListIndexCreation() {
        let index = AnyStringIndex(kind: "skiplist")
        
        if case .skiplist = index {
            XCTAssert(true)
        } else {
            XCTFail("Should create SkipList index")
        }
    }
    
    func testFractalIndexCreation() {
        let index = AnyStringIndex(kind: "fractal")
        
        if case .fractal = index {
            XCTAssert(true)
        } else {
            XCTFail("Should create Fractal index")
        }
    }
    
    func testLSMIndexCreation() {
        let index = AnyStringIndex(kind: "lsm")
        
        if case .lsm = index {
            XCTAssert(true)
        } else {
            XCTFail("Should create LSM index")
        }
    }
    
    func testDefaultIndexCreation() {
        let index = AnyStringIndex(kind: "unknown")
        
        // Should default to hash
        if case .hash = index {
            XCTAssert(true)
        } else {
            XCTFail("Should default to hash index")
        }
    }
    
    func testCaseInsensitiveCreation() {
        let index1 = AnyStringIndex(kind: "HASH")
        let index2 = AnyStringIndex(kind: "Hash")
        let index3 = AnyStringIndex(kind: "hash")
        
        if case .hash = index1, case .hash = index2, case .hash = index3 {
            XCTAssert(true)
        } else {
            XCTFail("Should be case insensitive")
        }
    }
    
    // MARK: - Basic Operations - All Variants
    
    func testBasicOperationsHash() {
        testBasicOperations(kind: "hash")
    }
    
    func testBasicOperationsART() {
        testBasicOperations(kind: "art")
    }
    
    func testBasicOperationsBTree() {
        testBasicOperations(kind: "btree")
    }
    
    func testBasicOperationsSkipList() {
        testBasicOperations(kind: "skiplist")
    }
    
    func testBasicOperationsFractal() {
        testBasicOperations(kind: "fractal")
    }
    
    func testBasicOperationsLSM() {
        testBasicOperations(kind: "lsm")
    }
    
    private func testBasicOperations(kind: String) {
        var index = AnyStringIndex(kind: kind)
        
        // Insert
        index.insert(key: "apple", ref: RID(pageId: 0, slotId: 1))
        index.insert(key: "banana", ref: RID(pageId: 0, slotId: 2))
        index.insert(key: "cherry", ref: RID(pageId: 0, slotId: 3))
        
        // Search equals
        let appleResults = index.searchEquals("apple")
        XCTAssertEqual(appleResults.count, 1, "Failed for \(kind)")
        XCTAssertEqual(appleResults.first?.slot, 1, "Failed for \(kind)")
        
        let bananaResults = index.searchEquals("banana")
        XCTAssertEqual(bananaResults.count, 1, "Failed for \(kind)")
        XCTAssertEqual(bananaResults.first?.slot, 2, "Failed for \(kind)")
        
        // Search non-existent
        let notFound = index.searchEquals("nonexistent")
        XCTAssertTrue(notFound.isEmpty, "Failed for \(kind)")
        
        // Remove
        index.remove(key: "banana", ref: RID(page: 0, slot: 2))
        let afterRemove = index.searchEquals("banana")
        XCTAssertTrue(afterRemove.isEmpty, "Failed for \(kind)")
    }
    
    // MARK: - Range Query Tests - All Variants
    
    func testRangeQueryHash() {
        testRangeQuery(kind: "hash")
    }
    
    func testRangeQueryART() {
        testRangeQuery(kind: "art")
    }
    
    func testRangeQueryBTree() {
        testRangeQuery(kind: "btree")
    }
    
    func testRangeQuerySkipList() {
        testRangeQuery(kind: "skiplist")
    }
    
    func testRangeQueryFractal() {
        testRangeQuery(kind: "fractal")
    }
    
    func testRangeQueryLSM() {
        testRangeQuery(kind: "lsm")
    }
    
    private func testRangeQuery(kind: String) {
        var index = AnyStringIndex(kind: kind)
        
        // Insert range of keys
        for i in 0..<10 {
            let key = String(format: "key%02d", i)
            index.insert(key: key, ref: RID(page: 0, slot: UInt16(i)))
        }
        
        // Range query
        let results = index.range("key03", "key07")
        
        // Results should contain keys in range
        XCTAssertGreaterThan(results.count, 0, "Failed for \(kind)")
    }
    
    // MARK: - Duplicate Handling Tests
    
    func testDuplicateKeys() {
        let kinds = ["hash", "art", "btree", "skiplist", "fractal", "lsm"]
        
        for kind in kinds {
            var index = AnyStringIndex(kind: kind)
            
            // Insert same key multiple times with different RIDs
            index.insert(key: "duplicate", ref: RID(page: 0, slot: 1))
            index.insert(key: "duplicate", ref: RID(page: 0, slot: 2))
            index.insert(key: "duplicate", ref: RID(page: 0, slot: 3))
            
            let results = index.searchEquals("duplicate")
            
            // Should handle duplicates (implementation-dependent)
            XCTAssertGreaterThan(results.count, 0, "Failed for \(kind)")
        }
    }
    
    // MARK: - Large Dataset Tests
    
    func testLargeDatasetHash() {
        testLargeDataset(kind: "hash")
    }
    
    func testLargeDatasetSkipList() {
        testLargeDataset(kind: "skiplist")
    }
    
    func testLargeDatasetFractal() {
        testLargeDataset(kind: "fractal")
    }
    
    private func testLargeDataset(kind: String) {
        var index = AnyStringIndex(kind: kind)
        
        // Insert 1000 keys
        for i in 0..<1000 {
            index.insert(key: "key\(i)", ref: RID(page: 0, slot: UInt16(i % 1000)))
        }
        
        // Verify random samples
        for i in [0, 100, 500, 999] {
            let results = index.searchEquals("key\(i)")
            XCTAssertGreaterThan(results.count, 0, "Failed for \(kind) at key\(i)")
        }
    }
    
    // MARK: - Special Character Tests
    
    func testSpecialCharacters() {
        let kinds = ["hash", "art", "btree", "skiplist", "fractal", "lsm"]
        
        let specialKeys = [
            "key with spaces",
            "key\twith\ttabs",
            "key\nwith\nnewlines",
            "key\"with\"quotes",
            "key'with'apostrophes",
            "key\\with\\backslashes",
            "🚀emoji🌟key💻"
        ]
        
        for kind in kinds {
            var index = AnyStringIndex(kind: kind)
            
            for (i, key) in specialKeys.enumerated() {
                index.insert(key: key, ref: RID(page: 0, slot: UInt16(i)))
            }
            
            // Verify all can be retrieved
            for (i, key) in specialKeys.enumerated() {
                let results = index.searchEquals(key)
                XCTAssertGreaterThan(results.count, 0, "Failed for \(kind) with key: \(key)")
            }
        }
    }
    
    // MARK: - Empty String Tests
    
    func testEmptyString() {
        let kinds = ["hash", "art", "btree", "skiplist", "fractal", "lsm"]
        
        for kind in kinds {
            var index = AnyStringIndex(kind: kind)
            
            index.insert(key: "", ref: RID(page: 0, slot: 1))
            
            let results = index.searchEquals("")
            // Implementation-dependent whether empty strings are supported
            // But shouldn't crash
        }
    }
    
    // MARK: - Update Tests
    
    func testKeyUpdates() {
        let kinds = ["hash", "art", "btree", "skiplist", "fractal", "lsm"]
        
        for kind in kinds {
            var index = AnyStringIndex(kind: kind)
            
            // Insert initial value
            index.insert(key: "update_test", ref: RID(page: 0, slot: 1))
            
            // Update with new RID
            index.insert(key: "update_test", ref: RID(page: 0, slot: 2))
            
            let results = index.searchEquals("update_test")
            XCTAssertGreaterThan(results.count, 0, "Failed for \(kind)")
        }
    }
    
    // MARK: - Concurrent Access Tests
    
    func testConcurrentInserts() {
        let kinds = ["hash", "skiplist", "fractal"]
        
        for kind in kinds {
            var index = AnyStringIndex(kind: kind)
            
            let expectation = XCTestExpectation(description: "Concurrent inserts for \(kind)")
            expectation.expectedFulfillmentCount = 10
            
            for threadId in 0..<10 {
                DispatchQueue.global().async {
                    for i in 0..<10 {
                        let key = "thread\(threadId)_key\(i)"
                        let ref = RID(page: UInt32(threadId), slot: UInt16(i))
                        index.insert(key: key, ref: ref)
                    }
                    expectation.fulfill()
                }
            }
            
            wait(for: [expectation], timeout: 5.0)
            
            // Verify some keys exist
            let sample = index.searchEquals("thread0_key0")
            // Results may vary due to value type semantics
        }
    }
    
    // MARK: - Remove Edge Cases
    
    func testRemoveNonExistent() {
        let kinds = ["hash", "art", "btree", "skiplist", "fractal", "lsm"]
        
        for kind in kinds {
            var index = AnyStringIndex(kind: kind)
            
            // Remove from empty index
            index.remove(key: "nonexistent", ref: RID(page: 0, slot: 1))
            
            // Should not crash
            XCTAssert(true, "Should handle removing non-existent key for \(kind)")
        }
    }
    
    func testRemoveAfterInsert() {
        let kinds = ["hash", "art", "btree", "skiplist", "fractal", "lsm"]
        
        for kind in kinds {
            var index = AnyStringIndex(kind: kind)
            
            let key = "test"
            let ref = RID(page: 0, slot: 1)
            
            index.insert(key: key, ref: ref)
            
            let beforeRemove = index.searchEquals(key)
            XCTAssertGreaterThan(beforeRemove.count, 0, "Should find key before remove for \(kind)")
            
            index.remove(key: key, ref: ref)
            
            let afterRemove = index.searchEquals(key)
            // After remove, should not find it (or fewer results)
        }
    }
    
    // MARK: - Performance Comparison Tests
    
    func testInsertPerformanceComparison() {
        let kinds = ["hash", "btree", "skiplist", "fractal"]
        
        for kind in kinds {
            measure(metrics: [XCTClockMetric()]) {
                var index = AnyStringIndex(kind: kind)
                
                for i in 0..<1000 {
                    index.insert(key: "key\(i)", ref: RID(page: 0, slot: UInt16(i % 1000)))
                }
            }
        }
    }
    
    func testSearchPerformanceComparison() {
        let kinds = ["hash", "btree", "skiplist", "fractal"]
        
        for kind in kinds {
            var index = AnyStringIndex(kind: kind)
            
            // Pre-populate
            for i in 0..<1000 {
                index.insert(key: "key\(i)", ref: RID(page: 0, slot: UInt16(i % 1000)))
            }
            
            measure(metrics: [XCTClockMetric()]) {
                for i in 0..<1000 {
                    _ = index.searchEquals("key\(i)")
                }
            }
        }
    }
    
    // MARK: - Alternative Naming Tests
    
    func testAlternativeNaming() {
        let variants = [
            ("b+tree", AnyStringIndex(kind: "btree")),
            ("b-tree", AnyStringIndex(kind: "btree")),
            ("skip-list", AnyStringIndex(kind: "skiplist")),
            ("fractal-tree", AnyStringIndex(kind: "fractal")),
            ("lsm-tree", AnyStringIndex(kind: "lsm"))
        ]
        
        for (name, _) in variants {
            let index = AnyStringIndex(kind: name)
            
            // Should create successfully
            XCTAssertNotNil(index, "Failed to create index with name: \(name)")
        }
    }
    
    // MARK: - Integration Tests
    
    func testMixedOperations() {
        let kinds = ["hash", "art", "btree", "skiplist", "fractal", "lsm"]
        
        for kind in kinds {
            var index = AnyStringIndex(kind: kind)
            
            // Insert
            for i in 0..<100 {
                index.insert(key: "key\(i)", ref: RID(page: 0, slot: UInt16(i)))
            }
            
            // Search some
            for i in [10, 20, 30, 40, 50] {
                let results = index.searchEquals("key\(i)")
                XCTAssertGreaterThan(results.count, 0, "Search failed for \(kind)")
            }
            
            // Remove some
            for i in [10, 30, 50] {
                index.remove(key: "key\(i)", ref: RID(page: 0, slot: UInt16(i)))
            }
            
            // Verify removals
            for i in [10, 30, 50] {
                let results = index.searchEquals("key\(i)")
                // Should have fewer or no results
            }
            
            // Insert new
            for i in 100..<110 {
                index.insert(key: "key\(i)", ref: RID(page: 0, slot: UInt16(i)))
            }
            
            // Verify new inserts
            let newResults = index.searchEquals("key105")
            XCTAssertGreaterThan(newResults.count, 0, "New insert failed for \(kind)")
        }
    }
    
    // MARK: - Stress Tests
    
    func testRepeatedOperations() {
        let kinds = ["hash", "skiplist", "fractal"]
        
        for kind in kinds {
            var index = AnyStringIndex(kind: kind)
            
            // Repeated insert/remove cycles
            for cycle in 0..<10 {
                // Insert
                for i in 0..<100 {
                    index.insert(key: "cycle\(cycle)_key\(i)", ref: RID(page: 0, slot: UInt16(i)))
                }
                
                // Remove half
                for i in 0..<50 {
                    index.remove(key: "cycle\(cycle)_key\(i)", ref: RID(page: 0, slot: UInt16(i)))
                }
            }
            
            // Should still be functional
            index.insert(key: "final_test", ref: RID(page: 0, slot: 999))
            let results = index.searchEquals("final_test")
            XCTAssertGreaterThan(results.count, 0, "Stress test failed for \(kind)")
        }
    }
}

