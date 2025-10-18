//
//  BloomFilterExtendedTests.swift
//  ColibrDBTests
//
//  Extended and comprehensive tests for BloomFilter
//
// ColibrDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

import XCTest
@testable import ColibriCore

final class BloomFilterExtendedTests: XCTestCase {
    
    // MARK: - Edge Cases
    
    func testEmptyFilter() {
        let filter = BloomFilter(expectedElements: 100)
        
        // Empty filter should return false for everything
        XCTAssertFalse(filter.mightContain("anything"))
        XCTAssertFalse(filter.mightContain(42))
        XCTAssertFalse(filter.mightContain(""))
    }
    
    func testSingleElement() {
        let filter = BloomFilter(expectedElements: 1)
        
        filter.insert("single")
        
        XCTAssertTrue(filter.mightContain("single"))
        XCTAssertFalse(filter.mightContain("other"))
    }
    
    func testEmptyStringInsertion() {
        let filter = BloomFilter(expectedElements: 10)
        
        filter.insert("")
        
        XCTAssertTrue(filter.mightContain(""))
        XCTAssertFalse(filter.mightContain("non-empty"))
    }
    
    func testVeryLongStrings() {
        let filter = BloomFilter(expectedElements: 100)
        
        let longString = String(repeating: "a", count: 10000)
        filter.insert(longString)
        
        XCTAssertTrue(filter.mightContain(longString))
        
        let differentLongString = String(repeating: "b", count: 10000)
        // High probability this should be false (not a false positive)
        // But we can't guarantee it 100%
    }
    
    func testUnicodeStrings() {
        let filter = BloomFilter(expectedElements: 100)
        
        let unicodeStrings = [
            "Hello, 世界!",
            "🚀🌟💻",
            "Привет мир",
            "مرحبا بالعالم",
            "こんにちは世界"
        ]
        
        for str in unicodeStrings {
            filter.insert(str)
        }
        
        for str in unicodeStrings {
            XCTAssertTrue(filter.mightContain(str), "Failed for: \(str)")
        }
        
        XCTAssertFalse(filter.mightContain("Not inserted"))
    }
    
    func testSpecialCharacters() {
        let filter = BloomFilter(expectedElements: 50)
        
        let specialStrings = [
            "\n\r\t",
            "\"quotes\"",
            "'apostrophes'",
            "back\\slash",
            "null\0character"
        ]
        
        for str in specialStrings {
            filter.insert(str)
        }
        
        for str in specialStrings {
            XCTAssertTrue(filter.mightContain(str))
        }
    }
    
    // MARK: - Boundary Value Tests
    
    func testMinimumBitCount() {
        // Minimum should be 64 bits
        let filter = BloomFilter(bitCount: 1, hashFunctionCount: 1)
        
        filter.insert("test")
        XCTAssertTrue(filter.mightContain("test"))
        
        let stats = filter.statistics()
        XCTAssertGreaterThanOrEqual(stats.bitCount, 64)
    }
    
    func testMaximumHashFunctions() {
        // Should cap at 10 hash functions
        let filter = BloomFilter(bitCount: 1000, hashFunctionCount: 100)
        
        let stats = filter.statistics()
        XCTAssertLessThanOrEqual(stats.hashFunctionCount, 10)
    }
    
    func testVerySmallExpectedElements() {
        let filter = BloomFilter(expectedElements: 1, falsePositiveRate: 0.01)
        
        filter.insert("one")
        XCTAssertTrue(filter.mightContain("one"))
    }
    
    func testVeryLargeExpectedElements() {
        let filter = BloomFilter(expectedElements: 1_000_000, falsePositiveRate: 0.001)
        
        // Should not crash or cause issues
        filter.insert("test")
        XCTAssertTrue(filter.mightContain("test"))
        
        let stats = filter.statistics()
        XCTAssertGreaterThan(stats.bitCount, 0)
    }
    
    // MARK: - False Positive Rate Tests
    
    func testFalsePositiveRate() {
        let expectedElements = 1000
        let targetRate = 0.01 // 1%
        let filter = BloomFilter(expectedElements: expectedElements, falsePositiveRate: targetRate)
        
        // Insert expected number of elements
        for i in 0..<expectedElements {
            filter.insert("key\(i)")
        }
        
        // Test false positives
        var falsePositives = 0
        let testCount = 1000
        
        for i in 0..<testCount {
            let testKey = "notinserted\(i)"
            if filter.mightContain(testKey) {
                falsePositives += 1
            }
        }
        
        let actualRate = Double(falsePositives) / Double(testCount)
        
        // Allow some variance (2x the target rate to account for probability)
        XCTAssertLessThan(actualRate, targetRate * 2.0, 
                         "Actual FP rate \(actualRate) exceeds 2x target \(targetRate)")
    }
    
    func testFalsePositiveRateEstimation() {
        let filter = BloomFilter(expectedElements: 100, falsePositiveRate: 0.01)
        
        // Insert elements
        for i in 0..<100 {
            filter.insert(i)
        }
        
        let estimatedRate = filter.estimatedFalsePositiveRate()
        
        // Should be close to target rate (within 5x for small datasets)
        XCTAssertLessThan(estimatedRate, 0.05)
    }
    
    func testDifferentFalsePositiveRates() {
        let rates = [0.001, 0.01, 0.05, 0.1]
        
        for rate in rates {
            let filter = BloomFilter(expectedElements: 100, falsePositiveRate: rate)
            
            for i in 0..<100 {
                filter.insert("key\(i)")
            }
            
            let estimatedRate = filter.estimatedFalsePositiveRate()
            
            // Verify it's in a reasonable range
            XCTAssertGreaterThan(estimatedRate, 0.0)
            XCTAssertLessThan(estimatedRate, 1.0)
        }
    }
    
    // MARK: - Capacity and Overflow Tests
    
    func testOverfillFilter() {
        let filter = BloomFilter(expectedElements: 10, falsePositiveRate: 0.01)
        
        // Insert way more than expected
        for i in 0..<1000 {
            filter.insert("key\(i)")
        }
        
        // Should still work, but FP rate will increase
        XCTAssertTrue(filter.mightContain("key500"))
        
        let stats = filter.statistics()
        XCTAssertEqual(stats.elementCount, 1000)
        
        // Fill ratio should be high
        XCTAssertGreaterThan(stats.fillRatio, 0.5)
    }
    
    func testFillRatioProgression() {
        let filter = BloomFilter(expectedElements: 100)
        
        let stats1 = filter.statistics()
        XCTAssertEqual(stats1.fillRatio, 0.0)
        
        // Insert 50 elements
        for i in 0..<50 {
            filter.insert(i)
        }
        
        let stats2 = filter.statistics()
        let fillRatio50 = stats2.fillRatio
        
        // Insert 50 more (total 100)
        for i in 50..<100 {
            filter.insert(i)
        }
        
        let stats3 = filter.statistics()
        let fillRatio100 = stats3.fillRatio
        
        // Fill ratio should increase
        XCTAssertGreaterThan(fillRatio50, 0.0)
        XCTAssertGreaterThan(fillRatio100, fillRatio50)
    }
    
    // MARK: - Clear and Reset Tests
    
    func testClearResetsState() {
        let filter = BloomFilter(expectedElements: 100)
        
        for i in 0..<50 {
            filter.insert("key\(i)")
        }
        
        XCTAssertTrue(filter.mightContain("key25"))
        
        filter.clear()
        
        // After clear, should not contain anything
        XCTAssertFalse(filter.mightContain("key25"))
        
        let stats = filter.statistics()
        XCTAssertEqual(stats.elementCount, 0)
        XCTAssertEqual(stats.bitsSet, 0)
        XCTAssertEqual(stats.fillRatio, 0.0)
    }
    
    func testMultipleClearOperations() {
        let filter = BloomFilter(expectedElements: 100)
        
        for cycle in 0..<5 {
            // Insert elements
            for i in 0..<20 {
                filter.insert("cycle\(cycle)_key\(i)")
            }
            
            // Verify they're there
            XCTAssertTrue(filter.mightContain("cycle\(cycle)_key10"))
            
            // Clear
            filter.clear()
            
            // Verify they're gone
            XCTAssertFalse(filter.mightContain("cycle\(cycle)_key10"))
        }
    }
    
    func testClearAndReuse() {
        let filter = BloomFilter(expectedElements: 100)
        
        // First batch
        for i in 0..<50 {
            filter.insert("first\(i)")
        }
        
        filter.clear()
        
        // Second batch with same filter
        for i in 0..<50 {
            filter.insert("second\(i)")
        }
        
        // Should contain second batch
        XCTAssertTrue(filter.mightContain("second25"))
        // Should not contain first batch
        XCTAssertFalse(filter.mightContain("first25"))
    }
    
    // MARK: - Concurrent Access Tests
    
    func testConcurrentInserts() {
        let filter = BloomFilter(expectedElements: 10000)
        let expectation = XCTestExpectation(description: "Concurrent inserts")
        expectation.expectedFulfillmentCount = 10
        
        for threadId in 0..<10 {
            DispatchQueue.global().async {
                for i in 0..<100 {
                    filter.insert("thread\(threadId)_key\(i)")
                }
                expectation.fulfill()
            }
        }
        
        wait(for: [expectation], timeout: 5.0)
        
        // Verify all elements are present
        for threadId in 0..<10 {
            XCTAssertTrue(filter.mightContain("thread\(threadId)_key50"))
        }
        
        let stats = filter.statistics()
        XCTAssertEqual(stats.elementCount, 1000)
    }
    
    func testConcurrentInsertsAndQueries() {
        let filter = BloomFilter(expectedElements: 1000)
        let expectation = XCTestExpectation(description: "Concurrent operations")
        expectation.expectedFulfillmentCount = 20
        
        // Writers
        for threadId in 0..<10 {
            DispatchQueue.global().async {
                for i in 0..<50 {
                    filter.insert("key\(threadId * 100 + i)")
                }
                expectation.fulfill()
            }
        }
        
        // Readers
        for threadId in 0..<10 {
            DispatchQueue.global().async {
                for i in 0..<50 {
                    _ = filter.mightContain("key\(i)")
                }
                expectation.fulfill()
            }
        }
        
        wait(for: [expectation], timeout: 5.0)
    }
    
    func testConcurrentClearOperations() {
        let filter = BloomFilter(expectedElements: 1000)
        
        // Insert some data
        for i in 0..<100 {
            filter.insert(i)
        }
        
        let expectation = XCTestExpectation(description: "Concurrent clears")
        expectation.expectedFulfillmentCount = 5
        
        // Multiple threads clearing simultaneously
        for _ in 0..<5 {
            DispatchQueue.global().async {
                filter.clear()
                expectation.fulfill()
            }
        }
        
        wait(for: [expectation], timeout: 2.0)
        
        // Filter should be empty
        let stats = filter.statistics()
        XCTAssertEqual(stats.elementCount, 0)
    }
    
    // MARK: - Statistics Tests
    
    func testStatisticsAccuracy() {
        let filter = BloomFilter(expectedElements: 100, falsePositiveRate: 0.01)
        
        let initialStats = filter.statistics()
        XCTAssertEqual(initialStats.elementCount, 0)
        XCTAssertEqual(initialStats.bitsSet, 0)
        XCTAssertEqual(initialStats.fillRatio, 0.0)
        
        // Insert 50 elements
        for i in 0..<50 {
            filter.insert("key\(i)")
        }
        
        let stats = filter.statistics()
        XCTAssertEqual(stats.elementCount, 50)
        XCTAssertGreaterThan(stats.bitsSet, 0)
        XCTAssertGreaterThan(stats.fillRatio, 0.0)
        XCTAssertLessThan(stats.fillRatio, 1.0)
    }
    
    // MARK: - Database Integration Tests
    
    func testForTableRows() {
        let filter = BloomFilter.forTableRows(estimatedRowCount: 10000)
        
        // Insert row IDs
        for i in 0..<1000 {
            filter.insert("row_\(i)")
        }
        
        // Check existence
        XCTAssertTrue(filter.mightContain("row_500"))
        XCTAssertFalse(filter.mightContain("row_9999"))
        
        // Very low FP rate (0.1%)
        let stats = filter.statistics()
        XCTAssertLessThan(stats.estimatedFalsePositiveRate, 0.01)
    }
    
    func testForIndexKeys() {
        let filter = BloomFilter.forIndexKeys(estimatedKeyCount: 5000)
        
        for i in 0..<1000 {
            filter.insert("index_key_\(i)")
        }
        
        XCTAssertTrue(filter.mightContain("index_key_750"))
    }
    
    func testForCacheKeys() {
        let filter = BloomFilter.forCacheKeys(estimatedCacheSize: 1000)
        
        for i in 0..<100 {
            filter.insert("cache_\(i)")
        }
        
        XCTAssertTrue(filter.mightContain("cache_50"))
    }
    
    // MARK: - Performance Tests
    
    func testInsertPerformance() {
        let filter = BloomFilter(expectedElements: 10000)
        
        measure {
            for i in 0..<10000 {
                filter.insert("key\(i)")
            }
        }
    }
    
    func testQueryPerformance() {
        let filter = BloomFilter(expectedElements: 10000)
        
        // Pre-populate
        for i in 0..<10000 {
            filter.insert("key\(i)")
        }
        
        measure {
            for i in 0..<10000 {
                _ = filter.mightContain("key\(i)")
            }
        }
    }
    
    func testMixedOperationsPerformance() {
        let filter = BloomFilter(expectedElements: 10000)
        
        measure {
            for i in 0..<5000 {
                filter.insert("key\(i)")
                _ = filter.mightContain("key\(i / 2)")
            }
        }
    }
    
    // MARK: - Hash Function Tests
    
    func testHashDistribution() {
        let filter = BloomFilter(expectedElements: 1000, falsePositiveRate: 0.01)
        
        // Insert sequential keys
        for i in 0..<100 {
            filter.insert("sequential_\(i)")
        }
        
        let stats = filter.statistics()
        
        // Good hash distribution should set a reasonable number of bits
        // Not too few (would indicate collisions) and not too many (would waste space)
        let expectedBitsSet = stats.elementCount * stats.hashFunctionCount
        let actualBitsSet = stats.bitsSet
        
        // Allow 50% variance due to probability
        XCTAssertGreaterThan(actualBitsSet, expectedBitsSet / 2)
    }
    
    // MARK: - Duplicate Handling Tests
    
    func testDuplicateInsertions() {
        let filter = BloomFilter(expectedElements: 100)
        
        // Insert same element multiple times
        for _ in 0..<10 {
            filter.insert("duplicate")
        }
        
        let stats = filter.statistics()
        // Element count should reflect all insertions
        XCTAssertEqual(stats.elementCount, 10)
        
        // But the element should still be findable
        XCTAssertTrue(filter.mightContain("duplicate"))
    }
    
    func testSimilarStrings() {
        let filter = BloomFilter(expectedElements: 100)
        
        filter.insert("test")
        filter.insert("test1")
        filter.insert("test2")
        filter.insert("Test")
        filter.insert("TEST")
        
        // All should be present
        XCTAssertTrue(filter.mightContain("test"))
        XCTAssertTrue(filter.mightContain("test1"))
        XCTAssertTrue(filter.mightContain("test2"))
        XCTAssertTrue(filter.mightContain("Test"))
        XCTAssertTrue(filter.mightContain("TEST"))
        
        // Non-existent should (probably) be absent
        XCTAssertFalse(filter.mightContain("test3"))
    }
}

