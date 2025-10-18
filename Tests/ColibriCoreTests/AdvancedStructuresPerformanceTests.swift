//
//  AdvancedStructuresPerformanceTests.swift
//  ColibrDBTests
//
//  Performance and benchmark tests for all advanced data structures
//
// ColibrDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

import XCTest
@testable import ColibriCore

final class AdvancedStructuresPerformanceTests: XCTestCase {
    
    // MARK: - BloomFilter Performance
    
    func testBloomFilterInsertPerformance() {
        let filter = BloomFilter(expectedElements: 100_000)
        
        measure {
            for i in 0..<100_000 {
                filter.insert(i)
            }
        }
    }
    
    func testBloomFilterQueryPerformance() {
        let filter = BloomFilter(expectedElements: 100_000)
        
        // Pre-populate
        for i in 0..<100_000 {
            filter.insert(i)
        }
        
        measure {
            for i in 0..<100_000 {
                _ = filter.mightContain(i)
            }
        }
    }
    
    func testBloomFilterClearPerformance() {
        let filter = BloomFilter(expectedElements: 100_000)
        
        for i in 0..<100_000 {
            filter.insert(i)
        }
        
        measure {
            filter.clear()
        }
    }
    
    // MARK: - SkipList Performance
    
    func testSkipListSequentialInsert() {
        measure {
            let skipList = SkipList<Int, String>()
            
            for i in 0..<10_000 {
                skipList.insert(key: i, value: "value\(i)")
            }
        }
    }
    
    func testSkipListRandomInsert() {
        var keys = Array(0..<10_000)
        keys.shuffle()
        
        measure {
            let skipList = SkipList<Int, String>()
            
            for key in keys {
                skipList.insert(key: key, value: "value\(key)")
            }
        }
    }
    
    func testSkipListSearch() {
        let skipList = SkipList<Int, String>()
        
        for i in 0..<10_000 {
            skipList.insert(key: i, value: "value\(i)")
        }
        
        measure {
            for i in 0..<10_000 {
                _ = skipList.search(key: i)
            }
        }
    }
    
    func testSkipListRangeQuery() {
        let skipList = SkipList<Int, String>()
        
        for i in 0..<10_000 {
            skipList.insert(key: i, value: "value\(i)")
        }
        
        measure {
            _ = skipList.range(from: 2000, to: 8000)
        }
    }
    
    func testSkipListDelete() {
        measure {
            let skipList = SkipList<Int, String>()
            
            for i in 0..<10_000 {
                skipList.insert(key: i, value: "value\(i)")
            }
            
            for i in stride(from: 0, to: 10_000, by: 2) {
                skipList.delete(key: i)
            }
        }
    }
    
    // MARK: - TTree Performance
    
    func testTTreeSequentialInsert() {
        measure {
            let ttree = TTree<Int, String>()
            
            for i in 0..<10_000 {
                ttree.insert(key: i, value: "value\(i)")
            }
        }
    }
    
    func testTTreeRandomInsert() {
        var keys = Array(0..<10_000)
        keys.shuffle()
        
        measure {
            let ttree = TTree<Int, String>()
            
            for key in keys {
                ttree.insert(key: key, value: "value\(key)")
            }
        }
    }
    
    func testTTreeSearch() {
        let ttree = TTree<Int, String>()
        
        for i in 0..<10_000 {
            ttree.insert(key: i, value: "value\(i)")
        }
        
        measure {
            for i in 0..<10_000 {
                _ = ttree.search(key: i)
            }
        }
    }
    
    func testTTreeRangeQuery() {
        let ttree = TTree<Int, String>()
        
        for i in 0..<10_000 {
            ttree.insert(key: i, value: "value\(i)")
        }
        
        measure {
            _ = ttree.range(from: 2000, to: 8000)
        }
    }
    
    func testTTreeAllElements() {
        let ttree = TTree<Int, String>()
        
        for i in 0..<10_000 {
            ttree.insert(key: i, value: "value\(i)")
        }
        
        measure {
            _ = ttree.all()
        }
    }
    
    // MARK: - RadixTree Performance
    
    func testRadixTreeInsert() {
        measure {
            let radix = RadixTree<Int>()
            
            for i in 0..<5000 {
                radix.insert(key: "prefix_common_\(i)", value: i)
            }
        }
    }
    
    func testRadixTreeSearch() {
        let radix = RadixTree<Int>()
        
        for i in 0..<5000 {
            radix.insert(key: "prefix_common_\(i)", value: i)
        }
        
        measure {
            for i in 0..<5000 {
                _ = radix.search(key: "prefix_common_\(i)")
            }
        }
    }
    
    func testRadixTreePrefixSearch() {
        let radix = RadixTree<Int>()
        
        for i in 0..<5000 {
            radix.insert(key: "prefix_\(i)", value: i)
        }
        
        measure {
            for i in 0..<100 {
                _ = radix.keysWithPrefix("prefix_\(i)")
            }
        }
    }
    
    func testRadixTreeAllElements() {
        let radix = RadixTree<Int>()
        
        for i in 0..<5000 {
            radix.insert(key: "key\(i)", value: i)
        }
        
        measure {
            _ = radix.all()
        }
    }
    
    // MARK: - Comparison Tests
    
    func testSkipListVsTTreeInsert() {
        print("\n=== SkipList vs TTree: Sequential Insert ===")
        
        // SkipList
        let skipListTime = measureTime {
            let skipList = SkipList<Int, String>()
            for i in 0..<10_000 {
                skipList.insert(key: i, value: "value\(i)")
            }
        }
        
        // TTree
        let ttreeTime = measureTime {
            let ttree = TTree<Int, String>()
            for i in 0..<10_000 {
                ttree.insert(key: i, value: "value\(i)")
            }
        }
        
        print("SkipList: \(skipListTime)s")
        print("TTree: \(ttreeTime)s")
        print("Winner: \(skipListTime < ttreeTime ? "SkipList" : "TTree")")
    }
    
    func testSkipListVsTTreeSearch() {
        print("\n=== SkipList vs TTree: Search ===")
        
        // Prepare data
        let skipList = SkipList<Int, String>()
        let ttree = TTree<Int, String>()
        
        for i in 0..<10_000 {
            skipList.insert(key: i, value: "value\(i)")
            ttree.insert(key: i, value: "value\(i)")
        }
        
        // SkipList search
        let skipListTime = measureTime {
            for i in 0..<10_000 {
                _ = skipList.search(key: i)
            }
        }
        
        // TTree search
        let ttreeTime = measureTime {
            for i in 0..<10_000 {
                _ = ttree.search(key: i)
            }
        }
        
        print("SkipList: \(skipListTime)s")
        print("TTree: \(ttreeTime)s")
        print("Winner: \(skipListTime < ttreeTime ? "SkipList" : "TTree")")
    }
    
    func testSkipListVsTTreeRangeQuery() {
        print("\n=== SkipList vs TTree: Range Query ===")
        
        // Prepare data
        let skipList = SkipList<Int, String>()
        let ttree = TTree<Int, String>()
        
        for i in 0..<10_000 {
            skipList.insert(key: i, value: "value\(i)")
            ttree.insert(key: i, value: "value\(i)")
        }
        
        // SkipList range query
        let skipListTime = measureTime {
            _ = skipList.range(from: 2000, to: 8000)
        }
        
        // TTree range query
        let ttreeTime = measureTime {
            _ = ttree.range(from: 2000, to: 8000)
        }
        
        print("SkipList: \(skipListTime)s")
        print("TTree: \(ttreeTime)s")
        print("Winner: \(skipListTime < ttreeTime ? "SkipList" : "TTree")")
    }
    
    // MARK: - Memory Efficiency Tests
    
    func testBloomFilterMemoryEfficiency() {
        let filter1 = BloomFilter(expectedElements: 1000, falsePositiveRate: 0.01)
        let filter2 = BloomFilter(expectedElements: 1000, falsePositiveRate: 0.001)
        
        for i in 0..<1000 {
            filter1.insert(i)
            filter2.insert(i)
        }
        
        let stats1 = filter1.statistics()
        let stats2 = filter2.statistics()
        
        print("\n=== BloomFilter Memory Efficiency ===")
        print("1% FP Rate - Bits: \(stats1.bitCount), Bits Set: \(stats1.bitsSet), Fill: \(stats1.fillRatio)")
        print("0.1% FP Rate - Bits: \(stats2.bitCount), Bits Set: \(stats2.bitsSet), Fill: \(stats2.fillRatio)")
    }
    
    func testSkipListMemoryOverhead() {
        let skipList = SkipList<Int, String>()
        
        for i in 0..<10_000 {
            skipList.insert(key: i, value: "value\(i)")
        }
        
        let stats = skipList.statistics()
        
        print("\n=== SkipList Memory Overhead ===")
        print("Elements: \(stats.elementCount)")
        print("Current Level: \(stats.currentLevel)")
        print("Average Level: \(stats.averageLevel)")
    }
    
    func testTTreeMemoryOverhead() {
        let ttree = TTree<Int, String>()
        
        for i in 0..<10_000 {
            ttree.insert(key: i, value: "value\(i)")
        }
        
        let stats = ttree.statistics()
        
        print("\n=== TTree Memory Overhead ===")
        print("Elements: \(stats.elementCount)")
        print("Nodes: \(stats.nodeCount)")
        print("Height: \(stats.height)")
        print("Avg Elements/Node: \(stats.averageElementsPerNode)")
    }
    
    func testRadixTreeCompressionEfficiency() {
        let radix = RadixTree<Int>()
        
        // Insert with common prefixes
        for i in 0..<5000 {
            radix.insert(key: "common_prefix_part_\(i)", value: i)
        }
        
        let stats = radix.statistics()
        
        print("\n=== RadixTree Compression ===")
        print("Elements: \(stats.elementCount)")
        print("Nodes: \(stats.nodeCount)")
        print("Compression Ratio: \(stats.compressionRatio)")
        print("Space Savings: \((1.0 - stats.compressionRatio) * 100)%")
    }
    
    // MARK: - Scalability Tests
    
    func testSkipListScalability() {
        print("\n=== SkipList Scalability ===")
        
        for size in [1000, 5000, 10_000, 50_000] {
            let skipList = SkipList<Int, String>()
            
            let insertTime = measureTime {
                for i in 0..<size {
                    skipList.insert(key: i, value: "value\(i)")
                }
            }
            
            let searchTime = measureTime {
                for i in 0..<size {
                    _ = skipList.search(key: i)
                }
            }
            
            print("Size: \(size) - Insert: \(insertTime)s, Search: \(searchTime)s")
        }
    }
    
    func testTTreeScalability() {
        print("\n=== TTree Scalability ===")
        
        for size in [1000, 5000, 10_000, 50_000] {
            let ttree = TTree<Int, String>()
            
            let insertTime = measureTime {
                for i in 0..<size {
                    ttree.insert(key: i, value: "value\(i)")
                }
            }
            
            let searchTime = measureTime {
                for i in 0..<size {
                    _ = ttree.search(key: i)
                }
            }
            
            print("Size: \(size) - Insert: \(insertTime)s, Search: \(searchTime)s")
        }
    }
    
    // MARK: - Workload-Specific Tests
    
    func testReadHeavyWorkload() {
        print("\n=== Read-Heavy Workload (90% reads, 10% writes) ===")
        
        let skipList = SkipList<Int, String>()
        let ttree = TTree<Int, String>()
        
        // Pre-populate
        for i in 0..<5000 {
            skipList.insert(key: i, value: "value\(i)")
            ttree.insert(key: i, value: "value\(i)")
        }
        
        // SkipList
        let skipListTime = measureTime {
            for i in 0..<10_000 {
                if i % 10 == 0 {
                    skipList.insert(key: 5000 + i, value: "new\(i)")
                } else {
                    _ = skipList.search(key: i % 5000)
                }
            }
        }
        
        // TTree
        let ttreeTime = measureTime {
            for i in 0..<10_000 {
                if i % 10 == 0 {
                    ttree.insert(key: 5000 + i, value: "new\(i)")
                } else {
                    _ = ttree.search(key: i % 5000)
                }
            }
        }
        
        print("SkipList: \(skipListTime)s")
        print("TTree: \(ttreeTime)s")
    }
    
    func testWriteHeavyWorkload() {
        print("\n=== Write-Heavy Workload (90% writes, 10% reads) ===")
        
        let skipList = SkipList<Int, String>()
        let ttree = TTree<Int, String>()
        
        // SkipList
        let skipListTime = measureTime {
            for i in 0..<10_000 {
                if i % 10 == 0 {
                    _ = skipList.search(key: i / 2)
                } else {
                    skipList.insert(key: i, value: "value\(i)")
                }
            }
        }
        
        // TTree
        let ttreeTime = measureTime {
            for i in 0..<10_000 {
                if i % 10 == 0 {
                    _ = ttree.search(key: i / 2)
                } else {
                    ttree.insert(key: i, value: "value\(i)")
                }
            }
        }
        
        print("SkipList: \(skipListTime)s")
        print("TTree: \(ttreeTime)s")
    }
    
    func testMixedWorkload() {
        print("\n=== Mixed Workload (50% reads, 30% writes, 20% range queries) ===")
        
        let skipList = SkipList<Int, String>()
        
        let time = measureTime {
            for i in 0..<10_000 {
                let op = i % 10
                
                if op < 5 {
                    // Read
                    _ = skipList.search(key: i % 5000)
                } else if op < 8 {
                    // Write
                    skipList.insert(key: i, value: "value\(i)")
                } else {
                    // Range query
                    let start = i % 4000
                    _ = skipList.range(from: start, to: start + 100)
                }
            }
        }
        
        print("Time: \(time)s")
    }
    
    // MARK: - Helper Methods
    
    private func measureTime(block: () -> Void) -> Double {
        let start = CFAbsoluteTimeGetCurrent()
        block()
        let end = CFAbsoluteTimeGetCurrent()
        return end - start
    }
}

