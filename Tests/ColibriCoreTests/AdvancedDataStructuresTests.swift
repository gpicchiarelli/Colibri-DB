//
//  AdvancedDataStructuresTests.swift
//  ColibrDBTests
//
//  Created by AI Assistant on 2025-10-18.
//
// ColibrDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// 🧪 Tests for Issue #52: Advanced Data Structures

import XCTest
@testable import ColibriCore

final class AdvancedDataStructuresTests: XCTestCase {
    
    // MARK: - Bloom Filter Tests
    
    func testBloomFilterBasicOperations() {
        let filter = BloomFilter(expectedElements: 100, falsePositiveRate: 0.01)
        
        // Insert elements
        filter.insert("apple")
        filter.insert("banana")
        filter.insert("cherry")
        
        // Test positive cases
        XCTAssertTrue(filter.mightContain("apple"))
        XCTAssertTrue(filter.mightContain("banana"))
        XCTAssertTrue(filter.mightContain("cherry"))
        
        // Test negative cases (should be false for items not inserted)
        // Note: There's a small probability of false positives
        XCTAssertFalse(filter.mightContain("grape"))
        XCTAssertFalse(filter.mightContain("orange"))
    }
    
    func testBloomFilterIntegerOperations() {
        let filter = BloomFilter(expectedElements: 1000, falsePositiveRate: 0.01)
        
        // Insert integers
        for i in 0..<100 {
            filter.insert(i)
        }
        
        // Test membership
        for i in 0..<100 {
            XCTAssertTrue(filter.mightContain(i))
        }
        
        // Test non-membership (with some tolerance for false positives)
        var falsePositives = 0
        for i in 1000..<1100 {
            if filter.mightContain(i) {
                falsePositives += 1
            }
        }
        
        // False positive rate should be roughly 1%
        XCTAssertLessThan(falsePositives, 5) // Allow up to 5% due to randomness
    }
    
    func testBloomFilterClear() {
        let filter = BloomFilter(expectedElements: 100)
        
        filter.insert("test1")
        filter.insert("test2")
        XCTAssertTrue(filter.mightContain("test1"))
        
        filter.clear()
        
        // After clear, all elements should be gone
        XCTAssertFalse(filter.mightContain("test1"))
        XCTAssertFalse(filter.mightContain("test2"))
    }
    
    func testBloomFilterStatistics() {
        let filter = BloomFilter(expectedElements: 100, falsePositiveRate: 0.01)
        
        for i in 0..<50 {
            filter.insert("key\(i)")
        }
        
        let stats = filter.statistics()
        
        XCTAssertEqual(stats.elementCount, 50)
        XCTAssertGreaterThan(stats.bitCount, 0)
        XCTAssertGreaterThan(stats.bitsSet, 0)
        XCTAssertGreaterThan(stats.fillRatio, 0.0)
        XCTAssertLessThan(stats.fillRatio, 1.0)
    }
    
    func testBloomFilterFactoryMethods() {
        let tableFilter = BloomFilter.forTableRows(estimatedRowCount: 10000)
        let indexFilter = BloomFilter.forIndexKeys(estimatedKeyCount: 5000)
        let cacheFilter = BloomFilter.forCacheKeys(estimatedCacheSize: 1000)
        
        // Just verify they were created successfully
        XCTAssertNotNil(tableFilter)
        XCTAssertNotNil(indexFilter)
        XCTAssertNotNil(cacheFilter)
    }
    
    // MARK: - Skip List Tests
    
    func testSkipListBasicOperations() {
        let skipList = SkipList<Int, String>()
        
        // Insert elements
        XCTAssertNil(skipList.insert(key: 5, value: "five"))
        XCTAssertNil(skipList.insert(key: 2, value: "two"))
        XCTAssertNil(skipList.insert(key: 8, value: "eight"))
        XCTAssertNil(skipList.insert(key: 1, value: "one"))
        
        XCTAssertEqual(skipList.size, 4)
        
        // Search
        XCTAssertEqual(skipList.search(key: 5), "five")
        XCTAssertEqual(skipList.search(key: 2), "two")
        XCTAssertNil(skipList.search(key: 10))
        
        // Update
        XCTAssertEqual(skipList.insert(key: 5, value: "FIVE"), "five")
        XCTAssertEqual(skipList.search(key: 5), "FIVE")
        XCTAssertEqual(skipList.size, 4) // Size shouldn't change on update
    }
    
    func testSkipListDelete() {
        let skipList = SkipList<Int, String>()
        
        skipList.insert(key: 1, value: "one")
        skipList.insert(key: 2, value: "two")
        skipList.insert(key: 3, value: "three")
        
        // Delete existing
        XCTAssertEqual(skipList.delete(key: 2), "two")
        XCTAssertEqual(skipList.size, 2)
        XCTAssertNil(skipList.search(key: 2))
        
        // Delete non-existing
        XCTAssertNil(skipList.delete(key: 10))
        XCTAssertEqual(skipList.size, 2)
    }
    
    func testSkipListRangeQuery() {
        let skipList = SkipList<Int, String>()
        
        for i in 1...10 {
            skipList.insert(key: i, value: "value\(i)")
        }
        
        let range = skipList.range(from: 3, to: 7)
        
        XCTAssertEqual(range.count, 5)
        XCTAssertEqual(range[0].key, 3)
        XCTAssertEqual(range[4].key, 7)
        
        // Verify sorted order
        for i in 0..<range.count-1 {
            XCTAssertLessThan(range[i].key, range[i+1].key)
        }
    }
    
    func testSkipListMinMax() {
        let skipList = SkipList<Int, String>()
        
        skipList.insert(key: 5, value: "five")
        skipList.insert(key: 2, value: "two")
        skipList.insert(key: 8, value: "eight")
        skipList.insert(key: 1, value: "one")
        skipList.insert(key: 10, value: "ten")
        
        let min = skipList.min()
        let max = skipList.max()
        
        XCTAssertEqual(min?.key, 1)
        XCTAssertEqual(min?.value, "one")
        XCTAssertEqual(max?.key, 10)
        XCTAssertEqual(max?.value, "ten")
    }
    
    func testSkipListAll() {
        let skipList = SkipList<Int, String>()
        
        let keys = [5, 2, 8, 1, 9, 3]
        for key in keys {
            skipList.insert(key: key, value: "value\(key)")
        }
        
        let all = skipList.all()
        
        XCTAssertEqual(all.count, keys.count)
        
        // Verify sorted order
        for i in 0..<all.count-1 {
            XCTAssertLessThan(all[i].key, all[i+1].key)
        }
    }
    
    func testSkipListClear() {
        let skipList = SkipList<Int, String>()
        
        for i in 1...10 {
            skipList.insert(key: i, value: "value\(i)")
        }
        
        XCTAssertEqual(skipList.size, 10)
        XCTAssertFalse(skipList.isEmpty)
        
        skipList.clear()
        
        XCTAssertEqual(skipList.size, 0)
        XCTAssertTrue(skipList.isEmpty)
    }
    
    func testSkipListStatistics() {
        let skipList = SkipList<Int, String>()
        
        for i in 1...100 {
            skipList.insert(key: i, value: "value\(i)")
        }
        
        let stats = skipList.statistics()
        
        XCTAssertEqual(stats.elementCount, 100)
        XCTAssertGreaterThan(stats.currentLevel, 0)
        XCTAssertLessThanOrEqual(stats.currentLevel, stats.maxLevel)
    }
    
    func testSkipListIterator() {
        let skipList = SkipList<Int, String>()
        
        for i in 1...5 {
            skipList.insert(key: i, value: "value\(i)")
        }
        
        var count = 0
        var lastKey = 0
        
        for (key, _) in skipList {
            count += 1
            XCTAssertGreaterThan(key, lastKey) // Verify sorted order
            lastKey = key
        }
        
        XCTAssertEqual(count, 5)
    }
    
    func testSkipListFactoryMethods() {
        let stringIndex = SkipList<String, RID>.forStringIndex(estimatedSize: 1000)
        let intIndex = SkipList<Int, RID>.forIntegerIndex(estimatedSize: 1000)
        
        XCTAssertNotNil(stringIndex)
        XCTAssertNotNil(intIndex)
    }
    
    // MARK: - T-Tree Tests
    
    func testTTreeBasicOperations() {
        let ttree = TTree<Int, String>()
        
        // Insert
        XCTAssertNil(ttree.insert(key: 5, value: "five"))
        XCTAssertNil(ttree.insert(key: 2, value: "two"))
        XCTAssertNil(ttree.insert(key: 8, value: "eight"))
        
        XCTAssertEqual(ttree.size, 3)
        
        // Search
        XCTAssertEqual(ttree.search(key: 5), "five")
        XCTAssertEqual(ttree.search(key: 2), "two")
        XCTAssertNil(ttree.search(key: 10))
        
        // Update
        XCTAssertEqual(ttree.insert(key: 5, value: "FIVE"), "FIVE")
        XCTAssertEqual(ttree.search(key: 5), "FIVE")
    }
    
    func testTTreeDelete() {
        let ttree = TTree<Int, String>()
        
        for i in 1...10 {
            ttree.insert(key: i, value: "value\(i)")
        }
        
        XCTAssertEqual(ttree.size, 10)
        
        // Delete
        XCTAssertEqual(ttree.delete(key: 5), "value5")
        XCTAssertEqual(ttree.size, 9)
        XCTAssertNil(ttree.search(key: 5))
        
        // Delete non-existing
        XCTAssertNil(ttree.delete(key: 100))
        XCTAssertEqual(ttree.size, 9)
    }
    
    func testTTreeRangeQuery() {
        let ttree = TTree<Int, String>()
        
        for i in 1...20 {
            ttree.insert(key: i, value: "value\(i)")
        }
        
        let range = ttree.range(from: 5, to: 15)
        
        XCTAssertEqual(range.count, 11) // 5 through 15 inclusive
        XCTAssertEqual(range.first?.key, 5)
        XCTAssertEqual(range.last?.key, 15)
        
        // Verify sorted order
        for i in 0..<range.count-1 {
            XCTAssertLessThan(range[i].key, range[i+1].key)
        }
    }
    
    func testTTreeAll() {
        let ttree = TTree<Int, String>()
        
        let keys = [15, 5, 20, 3, 10, 1, 18]
        for key in keys {
            ttree.insert(key: key, value: "value\(key)")
        }
        
        let all = ttree.all()
        
        XCTAssertEqual(all.count, keys.count)
        
        // Verify sorted order
        for i in 0..<all.count-1 {
            XCTAssertLessThan(all[i].key, all[i+1].key)
        }
    }
    
    func testTTreeClear() {
        let ttree = TTree<Int, String>()
        
        for i in 1...10 {
            ttree.insert(key: i, value: "value\(i)")
        }
        
        XCTAssertFalse(ttree.isEmpty)
        
        ttree.clear()
        
        XCTAssertTrue(ttree.isEmpty)
        XCTAssertEqual(ttree.size, 0)
    }
    
    func testTTreeBalancing() {
        let ttree = TTree<Int, String>()
        
        // Insert in order (worst case for unbalanced trees)
        for i in 1...100 {
            ttree.insert(key: i, value: "value\(i)")
        }
        
        let stats = ttree.statistics()
        
        // Tree should be balanced - height should be O(log n)
        // For 100 elements: log2(100) ≈ 6.6, but with node packing it should be even less
        XCTAssertLessThan(stats.height, 20) // Very generous bound
        XCTAssertEqual(stats.elementCount, 100)
    }
    
    func testTTreeStatistics() {
        let ttree = TTree<Int, String>()
        
        for i in 1...50 {
            ttree.insert(key: i, value: "value\(i)")
        }
        
        let stats = ttree.statistics()
        
        XCTAssertEqual(stats.elementCount, 50)
        XCTAssertGreaterThan(stats.nodeCount, 0)
        XCTAssertGreaterThan(stats.averageElementsPerNode, 0.0)
    }
    
    func testTTreeFactoryMethods() {
        let stringIndex = TTree<String, RID>.forStringIndex()
        let intIndex = TTree<Int, RID>.forIntegerIndex()
        
        XCTAssertNotNil(stringIndex)
        XCTAssertNotNil(intIndex)
    }
    
    // MARK: - Radix Tree Tests
    
    func testRadixTreeBasicOperations() {
        let radix = RadixTree<String>()
        
        // Insert
        XCTAssertNil(radix.insert(key: "apple", value: "fruit1"))
        XCTAssertNil(radix.insert(key: "app", value: "software"))
        XCTAssertNil(radix.insert(key: "application", value: "program"))
        
        XCTAssertEqual(radix.size, 3)
        
        // Search
        XCTAssertEqual(radix.search(key: "apple"), "fruit1")
        XCTAssertEqual(radix.search(key: "app"), "software")
        XCTAssertEqual(radix.search(key: "application"), "program")
        XCTAssertNil(radix.search(key: "appl"))
    }
    
    func testRadixTreePrefixCompression() {
        let radix = RadixTree<String>()
        
        // Insert keys with common prefix
        radix.insert(key: "test", value: "1")
        radix.insert(key: "testing", value: "2")
        radix.insert(key: "tester", value: "3")
        radix.insert(key: "team", value: "4")
        
        XCTAssertEqual(radix.size, 4)
        
        // All should be findable
        XCTAssertEqual(radix.search(key: "test"), "1")
        XCTAssertEqual(radix.search(key: "testing"), "2")
        XCTAssertEqual(radix.search(key: "tester"), "3")
        XCTAssertEqual(radix.search(key: "team"), "4")
    }
    
    func testRadixTreeDelete() {
        let radix = RadixTree<String>()
        
        radix.insert(key: "test", value: "1")
        radix.insert(key: "testing", value: "2")
        radix.insert(key: "tester", value: "3")
        
        // Delete
        XCTAssertEqual(radix.delete(key: "testing"), "2")
        XCTAssertEqual(radix.size, 2)
        XCTAssertNil(radix.search(key: "testing"))
        
        // Others should still exist
        XCTAssertEqual(radix.search(key: "test"), "1")
        XCTAssertEqual(radix.search(key: "tester"), "3")
    }
    
    func testRadixTreePrefixSearch() {
        let radix = RadixTree<String>()
        
        radix.insert(key: "apple", value: "1")
        radix.insert(key: "application", value: "2")
        radix.insert(key: "apply", value: "3")
        radix.insert(key: "banana", value: "4")
        
        let apKeys = radix.keysWithPrefix("app")
        
        XCTAssertEqual(apKeys.count, 3)
        XCTAssertTrue(apKeys.contains { $0.key == "apple" })
        XCTAssertTrue(apKeys.contains { $0.key == "application" })
        XCTAssertTrue(apKeys.contains { $0.key == "apply" })
        XCTAssertFalse(apKeys.contains { $0.key == "banana" })
    }
    
    func testRadixTreeLongestCommonPrefix() {
        let radix = RadixTree<String>()
        
        radix.insert(key: "testing123", value: "1")
        radix.insert(key: "testing456", value: "2")
        radix.insert(key: "testing789", value: "3")
        
        let lcp = radix.longestCommonPrefix()
        
        XCTAssertEqual(lcp, "testing")
    }
    
    func testRadixTreeAll() {
        let radix = RadixTree<String>()
        
        let keys = ["zebra", "apple", "banana", "cherry", "date"]
        for (index, key) in keys.enumerated() {
            radix.insert(key: key, value: "value\(index)")
        }
        
        let all = radix.all()
        
        XCTAssertEqual(all.count, keys.count)
        
        // Verify sorted order
        for i in 0..<all.count-1 {
            XCTAssertLessThan(all[i].key, all[i+1].key)
        }
    }
    
    func testRadixTreeClear() {
        let radix = RadixTree<String>()
        
        radix.insert(key: "test1", value: "1")
        radix.insert(key: "test2", value: "2")
        
        XCTAssertFalse(radix.isEmpty)
        
        radix.clear()
        
        XCTAssertTrue(radix.isEmpty)
        XCTAssertEqual(radix.size, 0)
    }
    
    func testRadixTreeStatistics() {
        let radix = RadixTree<String>()
        
        // Insert keys with common prefixes for good compression
        for i in 1...100 {
            radix.insert(key: "prefix\(i)", value: "value\(i)")
        }
        
        let stats = radix.statistics()
        
        XCTAssertEqual(stats.elementCount, 100)
        XCTAssertGreaterThan(stats.nodeCount, 0)
        XCTAssertGreaterThan(stats.terminalNodeCount, 0)
        XCTAssertLessThanOrEqual(stats.terminalNodeCount, stats.nodeCount)
    }
    
    func testRadixTreeFactoryMethods() {
        let stringIndex = RadixTree<RID>.forStringIndex()
        let ipIndex = RadixTree<RID>.forIPAddresses()
        
        XCTAssertNotNil(stringIndex)
        XCTAssertNotNil(ipIndex)
    }
    
    func testRadixTreeAutocomplete() {
        let autocomplete = RadixTree<[String]>.forAutocomplete()
        
        autocomplete.addSuggestion(prefix: "pr", suggestion: "print")
        autocomplete.addSuggestion(prefix: "pr", suggestion: "process")
        autocomplete.addSuggestion(prefix: "pr", suggestion: "program")
        
        let suggestions = autocomplete.search(key: "pr")
        
        XCTAssertNotNil(suggestions)
        XCTAssertEqual(suggestions?.count, 3)
        XCTAssertTrue(suggestions?.contains("print") ?? false)
        XCTAssertTrue(suggestions?.contains("process") ?? false)
        XCTAssertTrue(suggestions?.contains("program") ?? false)
    }
    
    // MARK: - Integration Tests
    
    func testBloomFilterWithSkipList() {
        // Use Bloom filter to check existence before querying skip list
        let bloom = BloomFilter(expectedElements: 1000)
        let skipList = SkipList<Int, String>()
        
        // Insert data into both
        for i in 0..<100 {
            bloom.insert(i)
            skipList.insert(key: i, value: "value\(i)")
        }
        
        // Query with Bloom filter first
        for i in 0..<200 {
            if bloom.mightContain(i) {
                // Only query skip list if Bloom filter says it might be there
                let result = skipList.search(key: i)
                if i < 100 {
                    XCTAssertNotNil(result)
                }
            } else {
                // If Bloom filter says no, skip list definitely won't have it
                XCTAssertNil(skipList.search(key: i))
            }
        }
    }
    
    func testConcurrentSkipListAccess() {
        let skipList = SkipList<Int, String>()
        let expectation = XCTestExpectation(description: "Concurrent operations")
        expectation.expectedFulfillmentCount = 10
        
        // Multiple threads inserting
        for i in 0..<10 {
            DispatchQueue.global().async {
                for j in 0..<10 {
                    skipList.insert(key: i * 10 + j, value: "value\(i)-\(j)")
                }
                expectation.fulfill()
            }
        }
        
        wait(for: [expectation], timeout: 5.0)
        
        XCTAssertEqual(skipList.size, 100)
    }
    
    func testConcurrentTTreeAccess() {
        let ttree = TTree<Int, String>()
        let expectation = XCTestExpectation(description: "Concurrent operations")
        expectation.expectedFulfillmentCount = 10
        
        // Multiple threads inserting
        for i in 0..<10 {
            DispatchQueue.global().async {
                for j in 0..<10 {
                    ttree.insert(key: i * 10 + j, value: "value\(i)-\(j)")
                }
                expectation.fulfill()
            }
        }
        
        wait(for: [expectation], timeout: 5.0)
        
        XCTAssertEqual(ttree.size, 100)
    }
}

