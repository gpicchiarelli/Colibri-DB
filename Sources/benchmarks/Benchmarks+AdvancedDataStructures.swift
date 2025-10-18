//
//  Benchmarks+AdvancedDataStructures.swift
//  ColibrDB Benchmarks
//
//  Created by AI Assistant on 2025-10-18.
//
// ColibrDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// 📊 Performance benchmarks for Issue #52: Advanced Data Structures

import Foundation
@testable import ColibriCore

extension Benchmarks {
    
    /// Runs all advanced data structures benchmarks
    public static func runAdvancedDataStructuresBenchmarks() {
        print("\n" + "═" * 80)
        print("🌸 ADVANCED DATA STRUCTURES BENCHMARKS")
        print("═" * 80 + "\n")
        
        benchmarkBloomFilter()
        benchmarkSkipList()
        benchmarkTTree()
        benchmarkRadixTree()
        benchmarkComparison()
    }
    
    // MARK: - Bloom Filter Benchmarks
    
    private static func benchmarkBloomFilter() {
        print("\n🌸 Bloom Filter Benchmarks\n")
        
        let sizes = [1_000, 10_000, 100_000]
        
        for size in sizes {
            let filter = BloomFilter(expectedElements: size, falsePositiveRate: 0.01)
            
            // Benchmark insertions
            let insertStart = Date()
            for i in 0..<size {
                filter.insert(i)
            }
            let insertTime = Date().timeIntervalSince(insertStart)
            
            // Benchmark lookups (positive)
            let lookupStart = Date()
            for i in 0..<size {
                _ = filter.mightContain(i)
            }
            let lookupTime = Date().timeIntervalSince(lookupStart)
            
            // Benchmark negative lookups
            let negativeStart = Date()
            for i in size..<(size * 2) {
                _ = filter.mightContain(i)
            }
            let negativeTime = Date().timeIntervalSince(negativeStart)
            
            // Count false positives
            var falsePositives = 0
            for i in size..<(size * 2) {
                if filter.mightContain(i) {
                    falsePositives += 1
                }
            }
            let actualFPRate = Double(falsePositives) / Double(size)
            
            let stats = filter.statistics()
            
            print("  Size: \(formatNumber(size))")
            print("    Insert: \(formatTime(insertTime)) (\(formatRate(size, insertTime))/sec)")
            print("    Lookup: \(formatTime(lookupTime)) (\(formatRate(size, lookupTime))/sec)")
            print("    Negative Lookup: \(formatTime(negativeTime)) (\(formatRate(size, negativeTime))/sec)")
            print("    False Positive Rate: \(String(format: "%.4f%%", actualFPRate * 100)) (expected ~1%)")
            print("    Fill Ratio: \(String(format: "%.2f%%", stats.fillRatio * 100))")
            print("    Memory: \(stats.bitCount / 8) bytes")
            print("")
        }
    }
    
    // MARK: - Skip List Benchmarks
    
    private static func benchmarkSkipList() {
        print("\n⛷️ Skip List Benchmarks\n")
        
        let sizes = [1_000, 10_000, 100_000]
        
        for size in sizes {
            let skipList = SkipList<Int, String>()
            
            // Benchmark insertions (random order)
            let insertStart = Date()
            for i in 0..<size {
                skipList.insert(key: i, value: "value\(i)")
            }
            let insertTime = Date().timeIntervalSince(insertStart)
            
            // Benchmark lookups
            let lookupStart = Date()
            for i in 0..<size {
                _ = skipList.search(key: i)
            }
            let lookupTime = Date().timeIntervalSince(lookupStart)
            
            // Benchmark range queries
            let rangeStart = Date()
            for _ in 0..<100 {
                let start = Int.random(in: 0..<(size - 100))
                _ = skipList.range(from: start, to: start + 100)
            }
            let rangeTime = Date().timeIntervalSince(rangeStart)
            
            // Benchmark deletions
            let deleteStart = Date()
            for i in 0..<min(1000, size) {
                skipList.delete(key: i)
            }
            let deleteTime = Date().timeIntervalSince(deleteStart)
            
            let stats = skipList.statistics()
            
            print("  Size: \(formatNumber(size))")
            print("    Insert: \(formatTime(insertTime)) (\(formatRate(size, insertTime))/sec)")
            print("    Lookup: \(formatTime(lookupTime)) (\(formatRate(size, lookupTime))/sec)")
            print("    Range Query (100 x 100 items): \(formatTime(rangeTime)) (\(formatRate(100, rangeTime))/sec)")
            print("    Delete: \(formatTime(deleteTime)) (\(formatRate(min(1000, size), deleteTime))/sec)")
            print("    Levels: \(stats.currentLevel)/\(stats.maxLevel)")
            print("    Avg Level: \(stats.averageLevel)")
            print("")
        }
    }
    
    // MARK: - T-Tree Benchmarks
    
    private static func benchmarkTTree() {
        print("\n🌳 T-Tree Benchmarks\n")
        
        let sizes = [1_000, 10_000, 100_000]
        
        for size in sizes {
            let ttree = TTree<Int, String>()
            
            // Benchmark insertions (worst case: sequential)
            let insertStart = Date()
            for i in 0..<size {
                ttree.insert(key: i, value: "value\(i)")
            }
            let insertTime = Date().timeIntervalSince(insertStart)
            
            // Benchmark lookups
            let lookupStart = Date()
            for i in 0..<size {
                _ = ttree.search(key: i)
            }
            let lookupTime = Date().timeIntervalSince(lookupStart)
            
            // Benchmark range queries
            let rangeStart = Date()
            for _ in 0..<100 {
                let start = Int.random(in: 0..<(size - 100))
                _ = ttree.range(from: start, to: start + 100)
            }
            let rangeTime = Date().timeIntervalSince(rangeStart)
            
            // Benchmark deletions
            let deleteStart = Date()
            for i in 0..<min(1000, size) {
                ttree.delete(key: i)
            }
            let deleteTime = Date().timeIntervalSince(deleteStart)
            
            let stats = ttree.statistics()
            
            print("  Size: \(formatNumber(size))")
            print("    Insert: \(formatTime(insertTime)) (\(formatRate(size, insertTime))/sec)")
            print("    Lookup: \(formatTime(lookupTime)) (\(formatRate(size, lookupTime))/sec)")
            print("    Range Query (100 x 100 items): \(formatTime(rangeTime)) (\(formatRate(100, rangeTime))/sec)")
            print("    Delete: \(formatTime(deleteTime)) (\(formatRate(min(1000, size), deleteTime))/sec)")
            print("    Height: \(stats.height)")
            print("    Nodes: \(stats.nodeCount)")
            print("    Avg Elements/Node: \(String(format: "%.1f", stats.averageElementsPerNode))")
            print("")
        }
    }
    
    // MARK: - Radix Tree Benchmarks
    
    private static func benchmarkRadixTree() {
        print("\n🌿 Radix Tree Benchmarks\n")
        
        let sizes = [1_000, 10_000, 100_000]
        
        for size in sizes {
            let radix = RadixTree<String>()
            
            // Generate keys with common prefixes for realistic scenario
            var keys: [String] = []
            for i in 0..<size {
                keys.append("prefix_\(i % 100)_key_\(i)")
            }
            
            // Benchmark insertions
            let insertStart = Date()
            for (index, key) in keys.enumerated() {
                radix.insert(key: key, value: "value\(index)")
            }
            let insertTime = Date().timeIntervalSince(insertStart)
            
            // Benchmark lookups
            let lookupStart = Date()
            for key in keys {
                _ = radix.search(key: key)
            }
            let lookupTime = Date().timeIntervalSince(lookupStart)
            
            // Benchmark prefix searches
            let prefixStart = Date()
            for i in 0..<100 {
                _ = radix.keysWithPrefix("prefix_\(i)")
            }
            let prefixTime = Date().timeIntervalSince(prefixStart)
            
            // Benchmark deletions
            let deleteStart = Date()
            for i in 0..<min(1000, size) {
                radix.delete(key: keys[i])
            }
            let deleteTime = Date().timeIntervalSince(deleteStart)
            
            let stats = radix.statistics()
            
            print("  Size: \(formatNumber(size))")
            print("    Insert: \(formatTime(insertTime)) (\(formatRate(size, insertTime))/sec)")
            print("    Lookup: \(formatTime(lookupTime)) (\(formatRate(size, lookupTime))/sec)")
            print("    Prefix Search (100 queries): \(formatTime(prefixTime)) (\(formatRate(100, prefixTime))/sec)")
            print("    Delete: \(formatTime(deleteTime)) (\(formatRate(min(1000, size), deleteTime))/sec)")
            print("    Nodes: \(stats.nodeCount)")
            print("    Max Depth: \(stats.maxDepth)")
            print("    Avg Label Length: \(String(format: "%.1f", stats.averageLabelLength))")
            print("    Compression Ratio: \(String(format: "%.2f", stats.compressionRatio))")
            print("")
        }
    }
    
    // MARK: - Comparison Benchmarks
    
    private static func benchmarkComparison() {
        print("\n📊 Structure Comparison (10,000 elements)\n")
        
        let size = 10_000
        
        // Skip List
        let skipList = SkipList<Int, String>()
        let skipListInsertStart = Date()
        for i in 0..<size {
            skipList.insert(key: i, value: "value\(i)")
        }
        let skipListInsertTime = Date().timeIntervalSince(skipListInsertStart)
        
        let skipListLookupStart = Date()
        for i in 0..<size {
            _ = skipList.search(key: i)
        }
        let skipListLookupTime = Date().timeIntervalSince(skipListLookupStart)
        
        // T-Tree
        let ttree = TTree<Int, String>()
        let ttreeInsertStart = Date()
        for i in 0..<size {
            ttree.insert(key: i, value: "value\(i)")
        }
        let ttreeInsertTime = Date().timeIntervalSince(ttreeInsertStart)
        
        let ttreeLookupStart = Date()
        for i in 0..<size {
            _ = ttree.search(key: i)
        }
        let ttreeLookupTime = Date().timeIntervalSince(ttreeLookupStart)
        
        // Dictionary (baseline)
        var dict: [Int: String] = [:]
        let dictInsertStart = Date()
        for i in 0..<size {
            dict[i] = "value\(i)"
        }
        let dictInsertTime = Date().timeIntervalSince(dictInsertStart)
        
        let dictLookupStart = Date()
        for i in 0..<size {
            _ = dict[i]
        }
        let dictLookupTime = Date().timeIntervalSince(dictLookupStart)
        
        print("  Insert Performance:")
        print("    Dictionary:  \(formatTime(dictInsertTime)) (baseline)")
        print("    Skip List:   \(formatTime(skipListInsertTime)) (\(String(format: "%.2f", skipListInsertTime / dictInsertTime))x)")
        print("    T-Tree:      \(formatTime(ttreeInsertTime)) (\(String(format: "%.2f", ttreeInsertTime / dictInsertTime))x)")
        print("")
        
        print("  Lookup Performance:")
        print("    Dictionary:  \(formatTime(dictLookupTime)) (baseline)")
        print("    Skip List:   \(formatTime(skipListLookupTime)) (\(String(format: "%.2f", skipListLookupTime / dictLookupTime))x)")
        print("    T-Tree:      \(formatTime(ttreeLookupTime)) (\(String(format: "%.2f", ttreeLookupTime / dictLookupTime))x)")
        print("")
    }
    
    // MARK: - Helper Functions
    
    private static func formatTime(_ time: TimeInterval) -> String {
        if time < 0.001 {
            return String(format: "%.2f µs", time * 1_000_000)
        } else if time < 1.0 {
            return String(format: "%.2f ms", time * 1000)
        } else {
            return String(format: "%.2f s", time)
        }
    }
    
    private static func formatRate(_ operations: Int, _ time: TimeInterval) -> String {
        let rate = Double(operations) / time
        if rate > 1_000_000 {
            return String(format: "%.2fM", rate / 1_000_000)
        } else if rate > 1_000 {
            return String(format: "%.2fK", rate / 1_000)
        } else {
            return String(format: "%.0f", rate)
        }
    }
    
    private static func formatNumber(_ number: Int) -> String {
        let formatter = NumberFormatter()
        formatter.numberStyle = .decimal
        return formatter.string(from: NSNumber(value: number)) ?? "\(number)"
    }
}

// MARK: - String Repetition

extension String {
    static func * (left: String, right: Int) -> String {
        return String(repeating: left, count: right)
    }
}

