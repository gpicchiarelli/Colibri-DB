//
//  SkipListStressTests.swift
//  ColibrDBTests
//
//  Stress and performance tests for SkipList
//
// ColibrDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

import XCTest
@testable import ColibriCore

final class SkipListStressTests: XCTestCase {
    
    // MARK: - Large Dataset Tests
    
    func testLargeInsertions() {
        let skipList = SkipList<Int, String>()
        
        // Insert 100,000 elements
        for i in 0..<100_000 {
            skipList.insert(key: i, value: "value\(i)")
        }
        
        XCTAssertEqual(skipList.size, 100_000)
        
        // Verify random samples
        XCTAssertEqual(skipList.search(key: 50_000), "value50000")
        XCTAssertEqual(skipList.search(key: 99_999), "value99999")
    }
    
    func testLargeRangeQueries() {
        let skipList = SkipList<Int, String>()
        
        // Insert 10,000 elements
        for i in 0..<10_000 {
            skipList.insert(key: i, value: "value\(i)")
        }
        
        // Large range query
        let range = skipList.range(from: 1000, to: 9000)
        
        XCTAssertEqual(range.count, 8001) // 1000 to 9000 inclusive
        XCTAssertEqual(range.first?.key, 1000)
        XCTAssertEqual(range.last?.key, 9000)
    }
    
    func testMassiveDeletions() {
        let skipList = SkipList<Int, String>()
        
        // Insert 50,000 elements
        for i in 0..<50_000 {
            skipList.insert(key: i, value: "value\(i)")
        }
        
        // Delete half of them
        for i in stride(from: 0, to: 50_000, by: 2) {
            XCTAssertNotNil(skipList.delete(key: i))
        }
        
        XCTAssertEqual(skipList.size, 25_000)
        
        // Verify remaining elements
        XCTAssertNil(skipList.search(key: 1000)) // Deleted (even)
        XCTAssertNotNil(skipList.search(key: 1001)) // Remaining (odd)
    }
    
    // MARK: - Sequential vs Random Insertion
    
    func testSequentialInsertion() {
        let skipList = SkipList<Int, String>()
        
        // Sequential insertion (worst case for some trees)
        for i in 0..<10_000 {
            skipList.insert(key: i, value: "seq\(i)")
        }
        
        let stats = skipList.statistics()
        
        // Skip list should handle this well
        XCTAssertEqual(stats.elementCount, 10_000)
        XCTAssertLessThan(stats.currentLevel, 25) // Reasonable level
    }
    
    func testRandomInsertion() {
        let skipList = SkipList<Int, String>()
        
        var keys = Array(0..<10_000)
        keys.shuffle()
        
        for key in keys {
            skipList.insert(key: key, value: "random\(key)")
        }
        
        let stats = skipList.statistics()
        XCTAssertEqual(stats.elementCount, 10_000)
        
        // Verify all present in sorted order
        let all = skipList.all()
        XCTAssertEqual(all.count, 10_000)
        
        for i in 0..<all.count-1 {
            XCTAssertLessThan(all[i].key, all[i+1].key)
        }
    }
    
    func testReverseSequentialInsertion() {
        let skipList = SkipList<Int, String>()
        
        // Reverse sequential (another worst case)
        for i in stride(from: 10_000, through: 1, by: -1) {
            skipList.insert(key: i, value: "rev\(i)")
        }
        
        XCTAssertEqual(skipList.size, 10_000)
        
        // Should still maintain sorted order
        let all = skipList.all()
        for i in 0..<all.count-1 {
            XCTAssertLessThan(all[i].key, all[i+1].key)
        }
    }
    
    // MARK: - Concurrent Stress Tests
    
    func testHighConcurrencyInserts() {
        let skipList = SkipList<Int, String>()
        let expectation = XCTestExpectation(description: "High concurrency inserts")
        expectation.expectedFulfillmentCount = 50
        
        // 50 threads each inserting 100 elements
        for threadId in 0..<50 {
            DispatchQueue.global().async {
                for i in 0..<100 {
                    let key = threadId * 1000 + i
                    skipList.insert(key: key, value: "thread\(threadId)_\(i)")
                }
                expectation.fulfill()
            }
        }
        
        wait(for: [expectation], timeout: 10.0)
        
        XCTAssertEqual(skipList.size, 5000)
    }
    
    func testConcurrentMixedOperations() {
        let skipList = SkipList<Int, String>()
        
        // Pre-populate
        for i in 0..<1000 {
            skipList.insert(key: i, value: "initial\(i)")
        }
        
        let expectation = XCTestExpectation(description: "Mixed operations")
        expectation.expectedFulfillmentCount = 30
        
        // Inserters (10 threads)
        for threadId in 0..<10 {
            DispatchQueue.global().async {
                for i in 0..<50 {
                    let key = 1000 + threadId * 100 + i
                    skipList.insert(key: key, value: "new\(key)")
                }
                expectation.fulfill()
            }
        }
        
        // Readers (10 threads)
        for _ in 0..<10 {
            DispatchQueue.global().async {
                for i in 0..<100 {
                    _ = skipList.search(key: i)
                }
                expectation.fulfill()
            }
        }
        
        // Deleters (10 threads)
        for threadId in 0..<10 {
            DispatchQueue.global().async {
                for i in 0..<10 {
                    let key = threadId * 10 + i
                    skipList.delete(key: key)
                }
                expectation.fulfill()
            }
        }
        
        wait(for: [expectation], timeout: 15.0)
    }
    
    // MARK: - Memory Stress Tests
    
    func testLargeStringValues() {
        let skipList = SkipList<Int, String>()
        
        // Insert elements with large string values
        let largeString = String(repeating: "x", count: 1000)
        
        for i in 0..<1000 {
            skipList.insert(key: i, value: "\(i)_\(largeString)")
        }
        
        XCTAssertEqual(skipList.size, 1000)
        
        // Verify retrieval
        if let value = skipList.search(key: 500) {
            XCTAssertTrue(value.hasPrefix("500_"))
        } else {
            XCTFail("Key 500 should exist")
        }
    }
    
    func testRepeatedClearAndRefill() {
        let skipList = SkipList<Int, String>()
        
        for cycle in 0..<10 {
            // Fill
            for i in 0..<5000 {
                skipList.insert(key: i, value: "cycle\(cycle)_\(i)")
            }
            
            XCTAssertEqual(skipList.size, 5000)
            
            // Clear
            skipList.clear()
            
            XCTAssertEqual(skipList.size, 0)
            XCTAssertTrue(skipList.isEmpty)
        }
    }
    
    // MARK: - Edge Case Stress Tests
    
    func testDuplicateKeyUpdates() {
        let skipList = SkipList<Int, String>()
        
        // Insert same keys multiple times with different values
        for round in 0..<100 {
            for i in 0..<1000 {
                skipList.insert(key: i, value: "round\(round)_value\(i)")
            }
        }
        
        // Size should remain 1000 (updates, not insertions)
        XCTAssertEqual(skipList.size, 1000)
        
        // Last update should win
        XCTAssertEqual(skipList.search(key: 500), "round99_value500")
    }
    
    func testBoundaryValues() {
        let skipList = SkipList<Int, String>()
        
        // Test with extreme values
        let values = [Int.min, Int.max, 0, -1, 1]
        
        for val in values {
            skipList.insert(key: val, value: "boundary\(val)")
        }
        
        for val in values {
            XCTAssertNotNil(skipList.search(key: val))
        }
        
        // Test range including boundaries
        let range = skipList.range(from: Int.min, to: Int.max)
        XCTAssertEqual(range.count, values.count)
    }
    
    // MARK: - Performance Benchmarks
    
    func testInsertPerformance() {
        measure {
            let skipList = SkipList<Int, String>()
            
            for i in 0..<10_000 {
                skipList.insert(key: i, value: "value\(i)")
            }
        }
    }
    
    func testSearchPerformance() {
        let skipList = SkipList<Int, String>()
        
        // Pre-populate
        for i in 0..<10_000 {
            skipList.insert(key: i, value: "value\(i)")
        }
        
        measure {
            for i in 0..<10_000 {
                _ = skipList.search(key: i)
            }
        }
    }
    
    func testRangeQueryPerformance() {
        let skipList = SkipList<Int, String>()
        
        for i in 0..<10_000 {
            skipList.insert(key: i, value: "value\(i)")
        }
        
        measure {
            for _ in 0..<100 {
                _ = skipList.range(from: 1000, to: 2000)
            }
        }
    }
    
    func testDeletePerformance() {
        measure {
            let skipList = SkipList<Int, String>()
            
            // Insert
            for i in 0..<10_000 {
                skipList.insert(key: i, value: "value\(i)")
            }
            
            // Delete half
            for i in stride(from: 0, to: 10_000, by: 2) {
                skipList.delete(key: i)
            }
        }
    }
    
    // MARK: - Level Distribution Tests
    
    func testLevelDistribution() {
        let skipList = SkipList<Int, String>(maxLevel: 16, probability: 0.25)
        
        // Insert many elements
        for i in 0..<10_000 {
            skipList.insert(key: i, value: "value\(i)")
        }
        
        let stats = skipList.statistics()
        
        // Level should be reasonable (roughly log base 4 of 10000 ≈ 7)
        XCTAssertGreaterThan(stats.currentLevel, 5)
        XCTAssertLessThan(stats.currentLevel, 15)
        
        // Average level should be close to 1/(1-p) - 1 ≈ 0.33 for p=0.25
        XCTAssertLessThan(stats.averageLevel, 3)
    }
    
    // MARK: - String Key Tests
    
    func testStringKeysStress() {
        let skipList = SkipList<String, Int>()
        
        // Insert many string keys
        for i in 0..<5000 {
            skipList.insert(key: "key_\(String(format: "%08d", i))", value: i)
        }
        
        XCTAssertEqual(skipList.size, 5000)
        
        // Test range query with strings
        let range = skipList.range(from: "key_00001000", to: "key_00002000")
        XCTAssertEqual(range.count, 1001)
    }
    
    // MARK: - Iterator Stress Tests
    
    func testLargeIteratorTraversal() {
        let skipList = SkipList<Int, String>()
        
        for i in 0..<10_000 {
            skipList.insert(key: i, value: "value\(i)")
        }
        
        var count = 0
        var lastKey = -1
        
        for (key, _) in skipList {
            XCTAssertGreaterThan(key, lastKey) // Verify sorted order
            lastKey = key
            count += 1
        }
        
        XCTAssertEqual(count, 10_000)
    }
}

