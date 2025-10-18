//
//  FractalTreeIndexTests.swift
//  ColibrDB
//
//  Tests for advanced Fractal Tree Index implementation
//  Created for Issue #55
//

import Testing
@testable import ColibriCore

@Suite("Fractal Tree Index Tests")
struct FractalTreeIndexTests {
    
    // MARK: - Basic Operations
    
    @Test func basicInsertAndSearch() throws {
        var index = FractalTreeIndex<String, Int>()
        
        // Insert some values
        try index.insert("apple", 1)
        try index.insert("banana", 2)
        try index.insert("cherry", 3)
        
        // Search
        let results1 = try index.searchEquals("apple")
        #expect(results1.contains(1))
        
        let results2 = try index.searchEquals("banana")
        #expect(results2.contains(2))
        
        let results3 = try index.searchEquals("cherry")
        #expect(results3.contains(3))
    }
    
    @Test func rangeQuery() throws {
        var index = FractalTreeIndex<String, Int>()
        
        // Insert some values
        try index.insert("a", 1)
        try index.insert("b", 2)
        try index.insert("c", 3)
        try index.insert("d", 4)
        try index.insert("e", 5)
        
        // Range query
        let results = try index.range("b", "d")
        #expect(results.count >= 3) // b, c, d
        #expect(results.contains(2))
        #expect(results.contains(3))
        #expect(results.contains(4))
    }
    
    @Test func deleteOperation() throws {
        var index = FractalTreeIndex<String, Int>()
        
        // Insert and delete
        try index.insert("test", 42)
        let before = try index.searchEquals("test")
        #expect(before.contains(42))
        
        try index.remove("test", 42)
        let after = try index.searchEquals("test")
        #expect(after.isEmpty)
    }
    
    // MARK: - Bulk Operations
    
    @Test func bulkInsert() throws {
        var index = FractalTreeIndex<String, Int>()
        
        let keys = ["a", "b", "c", "d", "e"]
        let refs = [1, 2, 3, 4, 5]
        
        try index.bulkInsert(keys: keys, refs: refs)
        
        // Verify all inserted
        for (key, ref) in zip(keys, refs) {
            let results = try index.searchEquals(key)
            #expect(results.contains(ref))
        }
    }
    
    @Test func bulkDelete() throws {
        var index = FractalTreeIndex<String, Int>()
        
        // First insert
        let keys = ["a", "b", "c"]
        let refs = [1, 2, 3]
        try index.bulkInsert(keys: keys, refs: refs)
        
        // Then bulk delete
        try index.bulkDelete(keys: keys, refs: refs)
        
        // Verify all deleted
        for key in keys {
            let results = try index.searchEquals(key)
            #expect(results.isEmpty)
        }
    }
    
    @Test func bulkUpdate() throws {
        var index = FractalTreeIndex<String, Int>()
        
        // Insert initial values
        let keys = ["a", "b", "c"]
        let oldRefs = [1, 2, 3]
        let newRefs = [10, 20, 30]
        
        try index.bulkInsert(keys: keys, refs: oldRefs)
        
        // Bulk update
        try index.bulkUpdate(keys: keys, oldRefs: oldRefs, newRefs: newRefs)
        
        // Verify updated
        for (key, newRef) in zip(keys, newRefs) {
            let results = try index.searchEquals(key)
            #expect(results.contains(newRef))
        }
    }
    
    // MARK: - Buffer Management
    
    @Test func bufferFlush() throws {
        // Create index with small buffer to force flushes
        var config = FractalTreeIndex<String, Int>.Configuration()
        config.bufferCapacity = 4
        var index = FractalTreeIndex<String, Int>(config: config)
        
        // Insert enough to trigger flush
        for i in 0..<10 {
            try index.insert("key\(i)", i)
        }
        
        // Verify all values are still accessible
        for i in 0..<10 {
            let results = try index.searchEquals("key\(i)")
            #expect(results.contains(i))
        }
    }
    
    // MARK: - Hierarchical Merges
    
    @Test func hierarchicalMerge() throws {
        var config = FractalTreeIndex<String, Int>.Configuration()
        config.bufferCapacity = 2
        config.levelCount = 3
        var index = FractalTreeIndex<String, Int>(config: config)
        
        // Insert many values to trigger merges
        for i in 0..<20 {
            try index.insert("key\(i)", i)
        }
        
        // Verify all values
        for i in 0..<20 {
            let results = try index.searchEquals("key\(i)")
            #expect(results.contains(i))
        }
    }
    
    // MARK: - Optimization
    
    @Test func optimization() throws {
        var index = FractalTreeIndex<String, Int>()
        
        // Insert some values
        for i in 0..<50 {
            try index.insert("key\(i)", i)
        }
        
        // Run optimization
        try index.optimize()
        
        // Verify all values still accessible
        for i in 0..<50 {
            let results = try index.searchEquals("key\(i)")
            #expect(results.contains(i))
        }
    }
    
    // MARK: - Statistics
    
    @Test func statistics() throws {
        var index = FractalTreeIndex<String, Int>()
        
        // Perform operations
        try index.insert("a", 1)
        try index.insert("b", 2)
        try index.bulkInsert(keys: ["c", "d"], refs: [3, 4])
        try index.remove("a", 1)
        
        // Get statistics
        let stats = index.getStatistics()
        
        #expect(stats.totalInserts > 0)
        #expect(stats.totalBulkOperations > 0)
        #expect(stats.totalDeletes > 0)
    }
    
    @Test func memoryEstimate() throws {
        var index = FractalTreeIndex<String, Int>()
        
        // Insert some data
        for i in 0..<100 {
            try index.insert("key\(i)", i)
        }
        
        // Get memory estimate
        let memory = index.estimateMemoryUsage()
        
        #expect(memory > 0)
    }
    
    // MARK: - Partitioning
    
    @Test func partitioning() throws {
        var config = FractalTreeIndex<String, Int>.Configuration()
        config.partitionCount = 2
        var index = FractalTreeIndex<String, Int>(config: config)
        
        // Insert across partitions
        for i in 0..<20 {
            try index.insert("key\(i)", i)
        }
        
        // Verify all accessible
        for i in 0..<20 {
            let results = try index.searchEquals("key\(i)")
            #expect(results.contains(i))
        }
    }
    
    // MARK: - Merge Strategies
    
    @Test func lazyMergeStrategy() throws {
        var config = FractalTreeIndex<String, Int>.Configuration()
        config.mergeStrategy = .lazy
        config.bufferCapacity = 10
        var index = FractalTreeIndex<String, Int>(config: config)
        
        for i in 0..<5 {
            try index.insert("key\(i)", i)
        }
        
        // Verify
        for i in 0..<5 {
            let results = try index.searchEquals("key\(i)")
            #expect(results.contains(i))
        }
    }
    
    @Test func eagerMergeStrategy() throws {
        var config = FractalTreeIndex<String, Int>.Configuration()
        config.mergeStrategy = .eager
        config.bufferCapacity = 10
        var index = FractalTreeIndex<String, Int>(config: config)
        
        for i in 0..<5 {
            try index.insert("key\(i)", i)
        }
        
        // Verify
        for i in 0..<5 {
            let results = try index.searchEquals("key\(i)")
            #expect(results.contains(i))
        }
    }
    
    @Test func adaptiveMergeStrategy() throws {
        var config = FractalTreeIndex<String, Int>.Configuration()
        config.mergeStrategy = .adaptive
        config.bufferCapacity = 10
        var index = FractalTreeIndex<String, Int>(config: config)
        
        for i in 0..<5 {
            try index.insert("key\(i)", i)
        }
        
        // Verify
        for i in 0..<5 {
            let results = try index.searchEquals("key\(i)")
            #expect(results.contains(i))
        }
    }
    
    // MARK: - Stress Tests
    
    @Test func largeDataset() throws {
        var index = FractalTreeIndex<Int, Int>()
        
        // Insert 1000 items
        for i in 0..<1000 {
            try index.insert(i, i * 10)
        }
        
        // Verify random samples
        let samples = [0, 100, 500, 999]
        for sample in samples {
            let results = try index.searchEquals(sample)
            #expect(results.contains(sample * 10))
        }
    }
    
    @Test func duplicateValues() throws {
        var index = FractalTreeIndex<String, Int>()
        
        // Insert duplicate keys with different references
        try index.insert("duplicate", 1)
        try index.insert("duplicate", 2)
        try index.insert("duplicate", 3)
        
        let results = try index.searchEquals("duplicate")
        #expect(results.count == 3)
        #expect(results.contains(1))
        #expect(results.contains(2))
        #expect(results.contains(3))
    }
}

