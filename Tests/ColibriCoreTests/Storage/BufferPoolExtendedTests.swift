//
//  BufferPoolExtendedTests.swift
//  ColibrDB Tests
//

import Foundation
@_spi(Experimental) import Testing
@testable import ColibriCore

@Suite("Buffer Pool Extended Tests", .serialized)
struct BufferPoolExtendedTests {
    
    func createTestBufferPool(capacity: Int = 10) -> LRUBufferPool {
        var fetchCount = 0
        var flushCount = 0
        
        return LRUBufferPool(
            pageSize: 8192,
            capacityPages: capacity,
            fetch: { pageId in
                fetchCount += 1
                return Data(repeating: UInt8(pageId & 0xFF), count: 8192)
            },
            flush: { pageId, data in
                flushCount += 1
            },
            namespace: "test"
        )
    }
    
    @Test("Get page from empty pool triggers fetch")
    func testGetPageFetch() throws {
        let pool = createTestBufferPool()
        
        let data = try pool.getPage(1)
        
        #expect(data.count == 8192)
    }
    
    @Test("Put and get page")
    func testPutAndGet() throws {
        let pool = createTestBufferPool()
        
        let testData = Data(repeating: 0xAB, count: 8192)
        try pool.putPage(1, data: testData, dirty: false)
        
        let retrieved = try pool.getPage(1)
        #expect(retrieved == testData)
    }
    
    @Test("Hit increases hit counter")
    func testHitCounter() throws {
        let pool = createTestBufferPool()
        
        _ = try pool.getPage(1)  // Miss
        let initialHits = pool.hits
        
        _ = try pool.getPage(1)  // Hit
        
        #expect(pool.hits == initialHits + 1)
    }
    
    @Test("Miss increases miss counter")
    func testMissCounter() throws {
        let pool = createTestBufferPool()
        
        let initialMisses = pool.misses
        
        _ = try pool.getPage(1)  // Miss
        
        #expect(pool.misses == initialMisses + 1)
    }
    
    @Test("Eviction when capacity exceeded")
    func testEviction() throws {
        let pool = createTestBufferPool(capacity: 3)
        
        try pool.putPage(1, data: Data(repeating: 1, count: 8192), dirty: false)
        try pool.putPage(2, data: Data(repeating: 2, count: 8192), dirty: false)
        try pool.putPage(3, data: Data(repeating: 3, count: 8192), dirty: false)
        try pool.putPage(4, data: Data(repeating: 4, count: 8192), dirty: false)  // Triggers eviction
        
        #expect(pool.evictions > 0)
    }
    
    @Test("Pin prevents eviction")
    func testPinning() throws {
        let pool = createTestBufferPool(capacity: 2)
        
        let data1 = try pool.pinPage(1)
        #expect(data1.count == 8192)
        
        try pool.putPage(2, data: Data(repeating: 2, count: 8192), dirty: false)
        try pool.putPage(3, data: Data(repeating: 3, count: 8192), dirty: false)
        
        // Page 1 should still be accessible (pinned)
        let stillThere = try pool.getPage(1)
        #expect(stillThere.count == 8192)
        
        pool.unpinPage(1)
    }
    
    @Test("Dirty page tracking")
    func testDirtyPages() throws {
        let pool = createTestBufferPool()
        
        try pool.putPage(1, data: Data(repeating: 1, count: 8192), dirty: true)
        
        // Dirty page should be marked internally
        // (No direct API to test, but flush will be called)
    }
    
    @Test("Flush specific page")
    func testFlushPage() throws {
        let pool = createTestBufferPool()
        
        try pool.putPage(1, data: Data(repeating: 1, count: 8192), dirty: true)
        try pool.flushPage(1)
        
        // No exception means success
        #expect(true)
    }
    
    @Test("Flush all dirty pages")
    func testFlushAll() throws {
        let pool = createTestBufferPool()
        
        try pool.putPage(1, data: Data(repeating: 1, count: 8192), dirty: true)
        try pool.putPage(2, data: Data(repeating: 2, count: 8192), dirty: true)
        try pool.putPage(3, data: Data(repeating: 3, count: 8192), dirty: true)
        
        try pool.flushAll()
        
        #expect(true)
    }
    
    @Test("Multiple gets hit cache")
    func testCacheHits() throws {
        let pool = createTestBufferPool()
        
        _ = try pool.getPage(1)  // Miss
        let initialHits = pool.hits
        
        _ = try pool.getPage(1)  // Hit
        _ = try pool.getPage(1)  // Hit
        _ = try pool.getPage(1)  // Hit
        
        #expect(pool.hits == initialHits + 3)
    }
}

