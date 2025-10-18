//
//  TTreeStressTests.swift
//  ColibrDBTests
//
//  Stress and performance tests for T-Tree
//
// ColibrDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

import XCTest
@testable import ColibriCore

final class TTreeStressTests: XCTestCase {
    
    // MARK: - Large Dataset Tests
    
    func testLargeScaleInsertions() {
        let ttree = TTree<Int, String>()
        
        // Insert 100,000 elements
        for i in 0..<100_000 {
            ttree.insert(key: i, value: "value\(i)")
        }
        
        XCTAssertEqual(ttree.size, 100_000)
        
        // Verify samples
        XCTAssertEqual(ttree.search(key: 50_000), "value50000")
        XCTAssertEqual(ttree.search(key: 99_999), "value99999")
        XCTAssertNil(ttree.search(key: 100_000))
    }
    
    func testMassiveDeletions() {
        let ttree = TTree<Int, String>()
        
        // Insert 50,000 elements
        for i in 0..<50_000 {
            ttree.insert(key: i, value: "value\(i)")
        }
        
        // Delete every other element
        for i in stride(from: 0, to: 50_000, by: 2) {
            XCTAssertNotNil(ttree.delete(key: i))
        }
        
        XCTAssertEqual(ttree.size, 25_000)
        
        // Verify deletions
        for i in 0..<50_000 {
            if i % 2 == 0 {
                XCTAssertNil(ttree.search(key: i))
            } else {
                XCTAssertNotNil(ttree.search(key: i))
            }
        }
    }
    
    func testLargeRangeQueries() {
        let ttree = TTree<Int, String>()
        
        // Insert 20,000 elements
        for i in 0..<20_000 {
            ttree.insert(key: i, value: "value\(i)")
        }
        
        // Large range query
        let range = ttree.range(from: 5000, to: 15000)
        
        XCTAssertEqual(range.count, 10001) // 5000 to 15000 inclusive
        XCTAssertEqual(range.first?.key, 5000)
        XCTAssertEqual(range.last?.key, 15000)
        
        // Verify sorted order
        for i in 0..<range.count-1 {
            XCTAssertLessThan(range[i].key, range[i+1].key)
        }
    }
    
    // MARK: - Sequential vs Random Insertion
    
    func testSequentialInsertion() {
        let ttree = TTree<Int, String>()
        
        // Sequential insertion (potential worst case)
        for i in 0..<10_000 {
            ttree.insert(key: i, value: "seq\(i)")
        }
        
        let stats = ttree.statistics()
        
        XCTAssertEqual(stats.elementCount, 10_000)
        
        // T-Tree should maintain balance
        // Height should be O(log n) with node packing
        // For 10,000 elements with 4-8 elements per node: ~1250-2500 nodes
        // Height should be around log2(2000) ≈ 11
        XCTAssertLessThan(stats.height, 30)
    }
    
    func testRandomInsertion() {
        let ttree = TTree<Int, String>()
        
        var keys = Array(0..<10_000)
        keys.shuffle()
        
        for key in keys {
            ttree.insert(key: key, value: "random\(key)")
        }
        
        let stats = ttree.statistics()
        XCTAssertEqual(stats.elementCount, 10_000)
        
        // Verify all present in sorted order
        let all = ttree.all()
        XCTAssertEqual(all.count, 10_000)
        
        for i in 0..<all.count-1 {
            XCTAssertLessThan(all[i].key, all[i+1].key)
        }
    }
    
    func testReverseSequentialInsertion() {
        let ttree = TTree<Int, String>()
        
        // Reverse sequential insertion
        for i in stride(from: 10_000, through: 1, by: -1) {
            ttree.insert(key: i, value: "rev\(i)")
        }
        
        XCTAssertEqual(ttree.size, 10_000)
        
        let stats = ttree.statistics()
        XCTAssertLessThan(stats.height, 30)
    }
    
    func testAlternatingInsertion() {
        let ttree = TTree<Int, String>()
        
        // Alternating: 1, 10000, 2, 9999, 3, 9998, ...
        for i in 0..<5000 {
            ttree.insert(key: i, value: "low\(i)")
            ttree.insert(key: 10000 - i, value: "high\(10000 - i)")
        }
        
        XCTAssertEqual(ttree.size, 10_000)
        
        let all = ttree.all()
        for i in 0..<all.count-1 {
            XCTAssertLessThan(all[i].key, all[i+1].key)
        }
    }
    
    // MARK: - Concurrent Stress Tests
    
    func testHighConcurrencyInserts() {
        let ttree = TTree<Int, String>()
        let expectation = XCTestExpectation(description: "High concurrency inserts")
        expectation.expectedFulfillmentCount = 50
        
        // 50 threads each inserting 100 elements
        for threadId in 0..<50 {
            DispatchQueue.global().async {
                for i in 0..<100 {
                    let key = threadId * 1000 + i
                    ttree.insert(key: key, value: "thread\(threadId)_\(i)")
                }
                expectation.fulfill()
            }
        }
        
        wait(for: [expectation], timeout: 10.0)
        
        XCTAssertEqual(ttree.size, 5000)
    }
    
    func testConcurrentMixedOperations() {
        let ttree = TTree<Int, String>()
        
        // Pre-populate
        for i in 0..<2000 {
            ttree.insert(key: i, value: "initial\(i)")
        }
        
        let expectation = XCTestExpectation(description: "Mixed operations")
        expectation.expectedFulfillmentCount = 30
        
        // Inserters
        for threadId in 0..<10 {
            DispatchQueue.global().async {
                for i in 0..<50 {
                    let key = 2000 + threadId * 100 + i
                    ttree.insert(key: key, value: "new\(key)")
                }
                expectation.fulfill()
            }
        }
        
        // Readers
        for _ in 0..<10 {
            DispatchQueue.global().async {
                for i in 0..<100 {
                    _ = ttree.search(key: i)
                }
                expectation.fulfill()
            }
        }
        
        // Deleters
        for threadId in 0..<10 {
            DispatchQueue.global().async {
                for i in 0..<10 {
                    let key = threadId * 20 + i
                    ttree.delete(key: key)
                }
                expectation.fulfill()
            }
        }
        
        wait(for: [expectation], timeout: 15.0)
    }
    
    func testConcurrentRangeQueries() {
        let ttree = TTree<Int, String>()
        
        // Pre-populate
        for i in 0..<10_000 {
            ttree.insert(key: i, value: "value\(i)")
        }
        
        let expectation = XCTestExpectation(description: "Concurrent range queries")
        expectation.expectedFulfillmentCount = 20
        
        for threadId in 0..<20 {
            DispatchQueue.global().async {
                let start = threadId * 400
                let end = start + 500
                _ = ttree.range(from: start, to: end)
                expectation.fulfill()
            }
        }
        
        wait(for: [expectation], timeout: 5.0)
    }
    
    // MARK: - Node Packing Tests
    
    func testNodePackingEfficiency() {
        let ttree = TTree<Int, String>()
        
        // Insert enough to fill multiple nodes
        for i in 0..<1000 {
            ttree.insert(key: i, value: "value\(i)")
        }
        
        let stats = ttree.statistics()
        
        // With 4-8 elements per node, we should have 125-250 nodes for 1000 elements
        XCTAssertGreaterThan(stats.nodeCount, 100)
        XCTAssertLessThan(stats.nodeCount, 300)
        
        // Average should be between min and max
        XCTAssertGreaterThanOrEqual(stats.averageElementsPerNode, Double(stats.minElementsPerNode))
        XCTAssertLessThanOrEqual(stats.averageElementsPerNode, Double(stats.maxElementsPerNode))
    }
    
    func testNodeSplittingBehavior() {
        let ttree = TTree<Int, String>()
        
        // Insert elements to force node splits
        for i in 0..<100 {
            ttree.insert(key: i, value: "value\(i)")
            
            let stats = ttree.statistics()
            
            // No node should exceed maximum capacity
            XCTAssertLessThanOrEqual(stats.maxElementsPerNode, 8) // TTree.Node.maxElements
        }
    }
    
    // MARK: - Balance and Height Tests
    
    func testTreeBalanceUnderLoad() {
        let ttree = TTree<Int, String>()
        
        // Insert elements in various patterns
        // Pattern 1: Sequential
        for i in 0..<1000 {
            ttree.insert(key: i, value: "seq\(i)")
        }
        
        let stats1 = ttree.statistics()
        let height1 = stats1.height
        
        // Pattern 2: Random
        for i in 1000..<2000 {
            ttree.insert(key: Int.random(in: 10000..<20000), value: "random\(i)")
        }
        
        let stats2 = ttree.statistics()
        
        // Height should not grow excessively
        XCTAssertLessThan(stats2.height, height1 * 2)
    }
    
    func testHeightAfterDeletions() {
        let ttree = TTree<Int, String>()
        
        // Insert 5000 elements
        for i in 0..<5000 {
            ttree.insert(key: i, value: "value\(i)")
        }
        
        let statsAfterInsert = ttree.statistics()
        let heightAfterInsert = statsAfterInsert.height
        
        // Delete 4000 elements
        for i in 0..<4000 {
            ttree.delete(key: i)
        }
        
        let statsAfterDelete = ttree.statistics()
        
        // Tree should still be reasonably balanced
        // Height might not change much due to structure, but should be reasonable
        XCTAssertLessThan(statsAfterDelete.height, heightAfterInsert + 5)
    }
    
    // MARK: - Memory Stress Tests
    
    func testLargeStringValues() {
        let ttree = TTree<Int, String>()
        
        let largeString = String(repeating: "x", count: 1000)
        
        for i in 0..<1000 {
            ttree.insert(key: i, value: "\(i)_\(largeString)")
        }
        
        XCTAssertEqual(ttree.size, 1000)
        
        // Verify retrieval
        if let value = ttree.search(key: 500) {
            XCTAssertTrue(value.hasPrefix("500_"))
        } else {
            XCTFail("Key 500 should exist")
        }
    }
    
    func testRepeatedClearAndRefill() {
        let ttree = TTree<Int, String>()
        
        for cycle in 0..<10 {
            // Fill
            for i in 0..<5000 {
                ttree.insert(key: i, value: "cycle\(cycle)_\(i)")
            }
            
            XCTAssertEqual(ttree.size, 5000)
            
            // Clear
            ttree.clear()
            
            XCTAssertEqual(ttree.size, 0)
            XCTAssertTrue(ttree.isEmpty)
        }
    }
    
    // MARK: - Edge Cases
    
    func testDuplicateKeyUpdates() {
        let ttree = TTree<Int, String>()
        
        // Insert same keys multiple times
        for round in 0..<100 {
            for i in 0..<1000 {
                ttree.insert(key: i, value: "round\(round)_\(i)")
            }
        }
        
        // Size should remain 1000
        XCTAssertEqual(ttree.size, 1000)
        
        // Last update should win
        XCTAssertEqual(ttree.search(key: 500), "round99_500")
    }
    
    func testBoundaryValues() {
        let ttree = TTree<Int, String>()
        
        let values = [Int.min, Int.max, 0, -1, 1, -1000, 1000]
        
        for val in values {
            ttree.insert(key: val, value: "boundary\(val)")
        }
        
        for val in values {
            XCTAssertNotNil(ttree.search(key: val), "Failed to find \(val)")
        }
        
        // Test range including boundaries
        let range = ttree.range(from: Int.min, to: Int.max)
        XCTAssertEqual(range.count, values.count)
    }
    
    func testEmptyRangeQueries() {
        let ttree = TTree<Int, String>()
        
        for i in 0..<100 {
            ttree.insert(key: i * 10, value: "value\(i)")
        }
        
        // Query range with no elements
        let emptyRange = ttree.range(from: 5, to: 8)
        XCTAssertTrue(emptyRange.isEmpty)
        
        // Query range before all elements
        let beforeRange = ttree.range(from: -100, to: -1)
        XCTAssertTrue(beforeRange.isEmpty)
        
        // Query range after all elements
        let afterRange = ttree.range(from: 1000, to: 2000)
        XCTAssertTrue(afterRange.isEmpty)
    }
    
    // MARK: - Performance Benchmarks
    
    func testInsertPerformance() {
        measure {
            let ttree = TTree<Int, String>()
            
            for i in 0..<10_000 {
                ttree.insert(key: i, value: "value\(i)")
            }
        }
    }
    
    func testSearchPerformance() {
        let ttree = TTree<Int, String>()
        
        // Pre-populate
        for i in 0..<10_000 {
            ttree.insert(key: i, value: "value\(i)")
        }
        
        measure {
            for i in 0..<10_000 {
                _ = ttree.search(key: i)
            }
        }
    }
    
    func testRangeQueryPerformance() {
        let ttree = TTree<Int, String>()
        
        for i in 0..<10_000 {
            ttree.insert(key: i, value: "value\(i)")
        }
        
        measure {
            for _ in 0..<100 {
                _ = ttree.range(from: 2000, to: 3000)
            }
        }
    }
    
    func testDeletePerformance() {
        measure {
            let ttree = TTree<Int, String>()
            
            // Insert
            for i in 0..<10_000 {
                ttree.insert(key: i, value: "value\(i)")
            }
            
            // Delete half
            for i in stride(from: 0, to: 10_000, by: 2) {
                ttree.delete(key: i)
            }
        }
    }
    
    func testAllElementsPerformance() {
        let ttree = TTree<Int, String>()
        
        for i in 0..<10_000 {
            ttree.insert(key: i, value: "value\(i)")
        }
        
        measure {
            _ = ttree.all()
        }
    }
    
    // MARK: - String Keys Tests
    
    func testStringKeysStress() {
        let ttree = TTree<String, Int>()
        
        // Insert many string keys
        for i in 0..<5000 {
            ttree.insert(key: "key_\(String(format: "%08d", i))", value: i)
        }
        
        XCTAssertEqual(ttree.size, 5000)
        
        // Test range query with strings
        let range = ttree.range(from: "key_00001000", to: "key_00002000")
        XCTAssertEqual(range.count, 1001)
        
        // Verify sorted order
        for i in 0..<range.count-1 {
            XCTAssertLessThan(range[i].key, range[i+1].key)
        }
    }
    
    // MARK: - Cache Locality Tests
    
    func testCacheFriendlyAccess() {
        let ttree = TTree<Int, String>()
        
        // Insert elements
        for i in 0..<10_000 {
            ttree.insert(key: i, value: "value\(i)")
        }
        
        // Sequential access (should be cache-friendly)
        measure {
            for i in 0..<10_000 {
                _ = ttree.search(key: i)
            }
        }
    }
    
    func testNodeTraversalEfficiency() {
        let ttree = TTree<Int, String>()
        
        for i in 0..<10_000 {
            ttree.insert(key: i, value: "value\(i)")
        }
        
        let stats = ttree.statistics()
        
        // With good node packing, we should have efficient traversal
        // Average elements per node should be reasonably high
        XCTAssertGreaterThan(stats.averageElementsPerNode, 2.0)
    }
}

