//
//  BufferManagerTests.swift
//  ColibrìDB Buffer Manager Tests
//
//  Comprehensive tests for BufferManager including all eviction policies,
//  WAL integration, edge cases, and error handling
//

import Foundation
import XCTest
@testable import ColibriCore

/// Comprehensive tests for BufferManager
final class BufferManagerTests: XCTestCase {
    
    // MARK: - Test Setup
    
    func createBufferManager(poolSize: Int = 10, evictionPolicy: EvictionPolicy = .lru) throws -> BufferManager {
        let tempDir = try TestUtils.createTempDirectory()
        let dataPath = tempDir.appendingPathComponent("test.db")
        let diskManager = try FileDiskManager(filePath: dataPath)
        return BufferManager(diskManager: diskManager, poolSize: poolSize, evictionPolicy: evictionPolicy)
    }
    
    // MARK: - Initialization Tests
    
    func testBufferManagerInitialization() async throws {
        let bufferManager = try createBufferManager(poolSize: 10)
        
        let poolSize = await bufferManager.getBufferPoolSize()
        XCTAssertEqual(poolSize, 10, "Pool size should match")
        
        let freeFrames = await bufferManager.getFreeFrameCount()
        XCTAssertEqual(freeFrames, 10, "Should have 10 free frames initially")
        
        let dirtyCount = await bufferManager.getDirtyPageCount()
        XCTAssertEqual(dirtyCount, 0, "Should have no dirty pages initially")
        
        let metrics = await bufferManager.getBufferMetrics()
        XCTAssertEqual(metrics.totalFrames, 10, "Total frames should match pool size")
        XCTAssertEqual(metrics.usedFrames, 0, "Should have no used frames initially")
        XCTAssertEqual(metrics.freeFrames, 10, "Should have 10 free frames initially")
        XCTAssertEqual(metrics.dirtyFrames, 0, "Should have no dirty frames initially")
        XCTAssertEqual(metrics.pinnedFrames, 0, "Should have no pinned frames initially")
        XCTAssertEqual(metrics.evictionCount, 0, "Should have no evictions initially")
    }
    
    // MARK: - Basic Operations Tests
    
    func testGetPageCacheMiss() async throws {
        let bufferManager = try createBufferManager()
        
        let pageId: PageID = 1
        let page = try await bufferManager.getPage(pageId: pageId)
        
        XCTAssertEqual(page.pageId, pageId, "Page ID should match")
        XCTAssertFalse(page.isDirty, "New page should not be dirty")
        
        // Verify page is pinned
        let pinCount = await bufferManager.getPinCount(pageId: pageId)
        XCTAssertEqual(pinCount, 1, "Page should be pinned after getPage")
        
        // Verify page is in cache (use query method, doesn't pin)
        let isInCache = await bufferManager.isPageInCache(pageId: pageId)
        XCTAssertTrue(isInCache, "Page should be in cache")
        
        let stats = await bufferManager.getBufferMetrics()
        XCTAssertEqual(stats.pinnedFrames, 1, "Should have 1 pinned frame")
    }
    
    func testGetPageCacheHit() async throws {
        let bufferManager = try createBufferManager()
        
        let pageId: PageID = 1
        
        // First access (cache miss)
        let page1 = try await bufferManager.getPage(pageId: pageId)
        
        // Unpin to allow future eviction
        try await bufferManager.unpinPage(pageId: pageId)
        
        // Second access (cache hit)
        let page2 = try await bufferManager.getPage(pageId: pageId)
        
        XCTAssertEqual(page1.pageId, page2.pageId, "Page IDs should match")
        
        // Pin count should be 1 again
        let pinCount = await bufferManager.getPinCount(pageId: pageId)
        XCTAssertEqual(pinCount, 1, "Page should be pinned again")
        
        let metrics = await bufferManager.getBufferMetrics()
        XCTAssertGreaterThan(metrics.hitRate, 0.0, "Hit rate should be positive")
    }
    
    func testPinUnpinPage() async throws {
        let bufferManager = try createBufferManager()
        
        let pageId: PageID = 1
        _ = try await bufferManager.getPage(pageId: pageId)
        
        // Pin again
        try await bufferManager.pinPage(pageId: pageId)
        
        var pinCount = await bufferManager.getPinCount(pageId: pageId)
        XCTAssertEqual(pinCount, 2, "Pin count should be 2")
        
        // Unpin once
        try await bufferManager.unpinPage(pageId: pageId)
        
        pinCount = await bufferManager.getPinCount(pageId: pageId)
        XCTAssertEqual(pinCount, 1, "Pin count should be 1")
        
        // Unpin again
        try await bufferManager.unpinPage(pageId: pageId)
        
        pinCount = await bufferManager.getPinCount(pageId: pageId)
        XCTAssertEqual(pinCount, 0, "Pin count should be 0")
        
        // Try to unpin again (should fail)
        do {
            try await bufferManager.unpinPage(pageId: pageId)
            XCTFail("Should throw error when unpinning unpinned page")
        } catch BufferError.pageNotPinned {
            // Expected
        } catch {
            XCTFail("Unexpected error: \(error)")
        }
    }
    
    func testPutPage() async throws {
        let bufferManager = try createBufferManager()
        
        let pageId: PageID = 1
        let originalPage = try await bufferManager.getPage(pageId: pageId)
        
        // Modify page
        var modifiedData = originalPage.data
        modifiedData.append(contentsOf: [1, 2, 3, 4, 5])
        let modifiedPage = BufferPage(
            pageId: pageId,
            data: modifiedData,
            lsn: originalPage.lsn,
            isDirty: true,
            isPinned: false,
            timestamp: originalPage.timestamp
        )
        
        // Put page (mark as dirty)
        try await bufferManager.putPage(pageId: pageId, page: modifiedPage, isDirty: true)
        
        // Verify page is dirty
        let dirtyCount = await bufferManager.getDirtyPageCount()
        XCTAssertEqual(dirtyCount, 1, "Should have 1 dirty page")
        
        // Verify page was updated (use query method)
        let updatedPage = await bufferManager.getPageQuery(pageId: pageId)
        XCTAssertNotNil(updatedPage, "Page should exist")
        XCTAssertEqual(updatedPage?.data.count ?? 0, modifiedData.count, "Page data should be updated")
    }
    
    func testPutPageNotPinned() async throws {
        let bufferManager = try createBufferManager()
        
        let pageId: PageID = 1
        _ = try await bufferManager.getPage(pageId: pageId)
        try await bufferManager.unpinPage(pageId: pageId)
        
        let page = BufferPage(
            pageId: pageId,
            data: Data([1, 2, 3]),
            lsn: 0,
            isDirty: false,
            isPinned: false,
            timestamp: 0
        )
        
        // Try to put page when not pinned (should fail)
        do {
            try await bufferManager.putPage(pageId: pageId, page: page, isDirty: true)
            XCTFail("Should throw error when putting unpinned page")
        } catch BufferError.pageNotPinned {
            // Expected
        } catch {
            XCTFail("Unexpected error: \(error)")
        }
    }
    
    func testMarkPageDirty() async throws {
        let bufferManager = try createBufferManager()
        
        let pageId: PageID = 1
        _ = try await bufferManager.getPage(pageId: pageId)
        
        try await bufferManager.markPageDirty(pageId: pageId)
        
        let dirtyCount = await bufferManager.getDirtyPageCount()
        XCTAssertEqual(dirtyCount, 1, "Should have 1 dirty page")
        
        let dirtyPages = await bufferManager.getDirtyPages()
        XCTAssertTrue(dirtyPages.contains(pageId), "Page should be in dirty pages")
    }
    
    // MARK: - WAL Integration Tests
    
    func testUpdateFlushedLSN() async throws {
        let bufferManager = try createBufferManager()
        
        let initialLSN = await bufferManager.getFlushedLSN()
        XCTAssertEqual(initialLSN, 0, "Initial LSN should be 0")
        
        // Update to higher LSN
        await bufferManager.updateFlushedLSN(100)
        var flushedLSN = await bufferManager.getFlushedLSN()
        XCTAssertEqual(flushedLSN, 100, "Flushed LSN should be 100")
        
        // Update to even higher LSN
        await bufferManager.updateFlushedLSN(200)
        flushedLSN = await bufferManager.getFlushedLSN()
        XCTAssertEqual(flushedLSN, 200, "Flushed LSN should be 200")
        
        // Try to update to lower LSN (should be ignored)
        await bufferManager.updateFlushedLSN(150)
        flushedLSN = await bufferManager.getFlushedLSN()
        XCTAssertEqual(flushedLSN, 200, "Flushed LSN should remain 200")
    }
    
    func testFlushPageWALBeforeData() async throws {
        let bufferManager = try createBufferManager()
        
        let pageId: PageID = 1
        let page = try await bufferManager.getPage(pageId: pageId)
        
        // Update page with LSN
        let pageWithLSN = BufferPage(
            pageId: pageId,
            data: page.data,
            lsn: 150,  // Higher than flushedLSN
            isDirty: true,
            isPinned: false,
            timestamp: page.timestamp
        )
        
        try await bufferManager.putPage(pageId: pageId, page: pageWithLSN, isDirty: true)
        
        // Try to flush without updating flushedLSN (should fail)
        do {
            try await bufferManager.flushPage(pageId: pageId)
            XCTFail("Should throw error when page LSN > flushed LSN")
        } catch BufferError.flushFailed {
            // Expected
        } catch {
            XCTFail("Unexpected error: \(error)")
        }
        
        // Update flushedLSN
        await bufferManager.updateFlushedLSN(150)
        
        // Now flush should succeed
        try await bufferManager.flushPage(pageId: pageId)
        
        let dirtyCount = await bufferManager.getDirtyPageCount()
        XCTAssertEqual(dirtyCount, 0, "Should have no dirty pages after flush")
    }
    
    func testFlushAll() async throws {
        let bufferManager = try createBufferManager()
        
        // Create multiple dirty pages
        let pageIds: [PageID] = [1, 2, 3]
        
        for pageId in pageIds {
            let page = try await bufferManager.getPage(pageId: pageId)
            let dirtyPage = BufferPage(
                pageId: pageId,
                data: page.data,
                lsn: UInt64(pageId),
                isDirty: true,
                isPinned: false,
                timestamp: page.timestamp
            )
            try await bufferManager.putPage(pageId: pageId, page: dirtyPage, isDirty: true)
        }
        
        // Update flushedLSN to allow flush
        await bufferManager.updateFlushedLSN(10)
        
        let dirtyCountBefore = await bufferManager.getDirtyPageCount()
        XCTAssertEqual(dirtyCountBefore, 3, "Should have 3 dirty pages")
        
        // Flush all
        try await bufferManager.flushAll()
        
        let dirtyCountAfter = await bufferManager.getDirtyPageCount()
        XCTAssertEqual(dirtyCountAfter, 0, "Should have no dirty pages after flushAll")
    }
    
    // MARK: - Eviction Tests
    
    func testLRUEviction() async throws {
        let bufferManager = try createBufferManager(poolSize: 3, evictionPolicy: .lru)
        
        // Fill buffer pool
        let pageId1: PageID = 1
        let pageId2: PageID = 2
        let pageId3: PageID = 3
        
        _ = try await bufferManager.getPage(pageId: pageId1)
        try await bufferManager.unpinPage(pageId: pageId1)
        
        _ = try await bufferManager.getPage(pageId: pageId2)
        try await bufferManager.unpinPage(pageId: pageId2)
        
        _ = try await bufferManager.getPage(pageId: pageId3)
        try await bufferManager.unpinPage(pageId: pageId3)
        
        // Access pageId1 to make it MRU
        _ = try await bufferManager.getPage(pageId: pageId1)
        try await bufferManager.unpinPage(pageId: pageId1)
        
        // Add new page (should evict pageId2, least recently used)
        let pageId4: PageID = 4
        _ = try await bufferManager.getPage(pageId: pageId4)
        
        // Verify pageId2 is evicted (query method, doesn't pin)
        let page2InCache = await bufferManager.isPageInCache(pageId: pageId2)
        XCTAssertFalse(page2InCache, "Page 2 should be evicted")
        
        // Verify pageId1 and pageId3 are still in cache (query method)
        let page1InCache = await bufferManager.isPageInCache(pageId: pageId1)
        XCTAssertTrue(page1InCache, "Page 1 should still be in cache")
        
        let page3InCache = await bufferManager.isPageInCache(pageId: pageId3)
        XCTAssertTrue(page3InCache, "Page 3 should still be in cache")
    }
    
    func testClockEviction() async throws {
        let bufferManager = try createBufferManager(poolSize: 3, evictionPolicy: .clock)
        
        // Fill buffer pool
        let pageIds: [PageID] = [1, 2, 3]
        for pageId in pageIds {
            _ = try await bufferManager.getPage(pageId: pageId)
            try await bufferManager.unpinPage(pageId: pageId)
        }
        
        // Access pages to set reference bits
        _ = try await bufferManager.getPage(pageId: 1)
        try await bufferManager.unpinPage(pageId: 1)
        
        // Clock sweep should clear some reference bits
        try await bufferManager.clockSweep()
        
        // Add new page (should evict page with cleared reference bit)
        _ = try await bufferManager.getPage(pageId: 4)
        
        let metrics = await bufferManager.getBufferMetrics()
        XCTAssertGreaterThan(metrics.evictionCount, 0, "Should have evictions")
    }
    
    func testFIFOEviction() async throws {
        let bufferManager = try createBufferManager(poolSize: 3, evictionPolicy: .fifo)
        
        // Fill buffer pool in order
        let pageId1: PageID = 1
        let pageId2: PageID = 2
        let pageId3: PageID = 3
        
        _ = try await bufferManager.getPage(pageId: pageId1)
        try await bufferManager.unpinPage(pageId: pageId1)
        
        _ = try await bufferManager.getPage(pageId: pageId2)
        try await bufferManager.unpinPage(pageId: pageId2)
        
        _ = try await bufferManager.getPage(pageId: pageId3)
        try await bufferManager.unpinPage(pageId: pageId3)
        
        // Add new page (should evict pageId1, first in)
        let pageId4: PageID = 4
        _ = try await bufferManager.getPage(pageId: pageId4)
        
        // Verify pageId1 is evicted (query method)
        let page1InCache = await bufferManager.isPageInCache(pageId: pageId1)
        XCTAssertFalse(page1InCache, "Page 1 should be evicted (FIFO)")
    }
    
    func testRandomEviction() async throws {
        let bufferManager = try createBufferManager(poolSize: 3, evictionPolicy: .random)
        
        // Fill buffer pool
        for i in 1...3 {
            _ = try await bufferManager.getPage(pageId: PageID(i))
            try await bufferManager.unpinPage(pageId: PageID(i))
        }
        
        // Add new page (should evict a random unpinned page)
        _ = try await bufferManager.getPage(pageId: 4)
        
        let metrics = await bufferManager.getBufferMetrics()
        XCTAssertEqual(metrics.evictionCount, 1, "Should have 1 eviction")
        
        let poolSize = await bufferManager.getBufferPoolSize()
        let freeFrames = await bufferManager.getFreeFrameCount()
        let usedFrames = poolSize - freeFrames
        XCTAssertLessThanOrEqual(usedFrames, 3, "Should not exceed pool size")
    }
    
    func testEvictionPinnedPage() async throws {
        let bufferManager = try createBufferManager(poolSize: 2, evictionPolicy: .lru)
        
        // Fill buffer pool and keep pages pinned
        let pageId1: PageID = 1
        let pageId2: PageID = 2
        
        _ = try await bufferManager.getPage(pageId: pageId1)
        _ = try await bufferManager.getPage(pageId: pageId2)
        
        // Try to add new page (should fail because all pages are pinned)
        do {
            _ = try await bufferManager.getPage(pageId: 3)
            XCTFail("Should throw error when all pages are pinned")
        } catch BufferError.pagePinned {
            // Expected - eviction fails because pages are pinned
        } catch {
            // Other errors might occur, but we expect pagePinned or noPageToEvict
            if !(error is BufferError && (error as? BufferError) == .noPageToEvict) {
                XCTFail("Unexpected error: \(error)")
            }
        }
    }
    
    // MARK: - Invariant Tests
    
    func testInvariantsAfterOperations() async throws {
        let bufferManager = try createBufferManager()
        
        // Perform various operations
        for i in 1...5 {
            let pageId = PageID(i)
            let page = try await bufferManager.getPage(pageId: pageId)
            
            if i % 2 == 0 {
                try await bufferManager.markPageDirty(pageId: pageId)
            }
            
            if i % 3 == 0 {
                try await bufferManager.unpinPage(pageId: pageId)
            }
        }
        
        // Check all invariants
        let allInvariants = await bufferManager.checkAllInvariants()
        XCTAssertTrue(allInvariants, "All invariants should hold")
        
        let pinCountInv = await bufferManager.checkPinCountInvariant()
        XCTAssertTrue(pinCountInv, "Pin count invariant should hold")
        
        let dirtyConsistency = await bufferManager.checkDirtyPageConsistencyInvariant()
        XCTAssertTrue(dirtyConsistency, "Dirty page consistency should hold")
        
        let evictionPolicy = await bufferManager.checkEvictionPolicyInvariant()
        XCTAssertTrue(evictionPolicy, "Eviction policy invariant should hold")
        
        let walBeforeData = await bufferManager.checkWALBeforeDataInvariant()
        XCTAssertTrue(walBeforeData, "WAL before data invariant should hold")
    }
    
    // MARK: - Error Handling Tests
    
    func testErrorHandling() async throws {
        let bufferManager = try createBufferManager()
        
        // Test pinning non-existent page
        do {
            try await bufferManager.pinPage(pageId: 999)
            XCTFail("Should throw error for non-existent page")
        } catch BufferError.pageNotFound {
            // Expected
        } catch {
            XCTFail("Unexpected error: \(error)")
        }
        
        // Test marking non-existent page dirty
        do {
            try await bufferManager.markPageDirty(pageId: 999)
            XCTFail("Should throw error for non-existent page")
        } catch BufferError.pageNotFound {
            // Expected
        } catch {
            XCTFail("Unexpected error: \(error)")
        }
        
        // Test putting non-existent page
        let fakePage = BufferPage(
            pageId: 999,
            data: Data(),
            lsn: 0,
            isDirty: false,
            isPinned: false,
            timestamp: 0
        )
        do {
            try await bufferManager.putPage(pageId: 999, page: fakePage, isDirty: true)
            XCTFail("Should throw error for non-existent page")
        } catch BufferError.pageNotFound {
            // Expected
        } catch {
            XCTFail("Unexpected error: \(error)")
        }
        
        // Test flushing non-existent page (should succeed silently if not dirty)
        try await bufferManager.flushPage(pageId: 999)  // Should not throw
        
        // Test flushing non-dirty page (should succeed silently)
        _ = try await bufferManager.getPage(pageId: 1)
        try await bufferManager.flushPage(pageId: 1)  // Should not throw (not dirty)
    }
    
    // MARK: - Metrics Tests
    
    func testMetrics() async throws {
        let bufferManager = try createBufferManager(poolSize: 10)
        
        var metrics = await bufferManager.getBufferMetrics()
        XCTAssertEqual(metrics.hitRate, 0.0, "Initial hit rate should be 0")
        XCTAssertEqual(metrics.missRate, 0.0, "Initial miss rate should be 0")
        
        // Cause cache misses
        for i in 1...5 {
            _ = try await bufferManager.getPage(pageId: PageID(i))
        }
        
        metrics = await bufferManager.getBufferMetrics()
        XCTAssertGreaterThan(metrics.missRate, 0.0, "Should have misses")
        
        // Cause cache hits
        for i in 1...3 {
            _ = try await bufferManager.getPage(pageId: PageID(i))
        }
        
        metrics = await bufferManager.getBufferMetrics()
        XCTAssertGreaterThan(metrics.hitRate, 0.0, "Hit rate should be positive")
        
        let totalAccesses = metrics.hitRate + metrics.missRate
        XCTAssertTrue(totalAccesses <= 1.01, "Hit rate + miss rate should be <= 1.0 (with tolerance)")
    }
    
    // MARK: - Concurrent Access Tests
    
    func testConcurrentAccess() async throws {
        let bufferManager = try createBufferManager(poolSize: 20)
        
        let taskCount = 10
        var tasks: [Task<Void, Never>] = []
        
        for i in 0..<taskCount {
            let task = Task {
                do {
            let pageId = PageID(i + 1)
            let page = try await bufferManager.getPage(pageId: pageId)
                    let modifiedPage = BufferPage(
                        pageId: pageId,
                        data: TestUtils.generateRandomData(size: 512),
                        lsn: page.lsn,
                        isDirty: true,
                        isPinned: false,
                        timestamp: page.timestamp
                    )
                    try await bufferManager.putPage(pageId: pageId, page: modifiedPage, isDirty: true)
                    
                    // Unpin
                    try await bufferManager.unpinPage(pageId: pageId)
                    try await bufferManager.unpinPage(pageId: pageId)
                } catch {
                    // Handle errors
                }
            }
            tasks.append(task)
        }
        
        // Wait for all tasks
        for task in tasks {
            await task.value
        }
        
        // Verify invariants hold
        let allInvariants = await bufferManager.checkAllInvariants()
        XCTAssertTrue(allInvariants, "All invariants should hold after concurrent access")
        
        let metrics = await bufferManager.getBufferMetrics()
        XCTAssertLessThanOrEqual(metrics.usedFrames, 20, "Should not exceed pool size")
    }
    
    // MARK: - Edge Cases Tests
    
    func testEmptyBufferFlushAll() async throws {
        let bufferManager = try createBufferManager()
        
        // Flush all when no dirty pages (should succeed)
        try await bufferManager.flushAll()
        
        let dirtyCount = await bufferManager.getDirtyPageCount()
        XCTAssertEqual(dirtyCount, 0, "Should have no dirty pages")
    }
    
    func testSinglePageBuffer() async throws {
        let bufferManager = try createBufferManager(poolSize: 1)
        
        let pageId1: PageID = 1
        _ = try await bufferManager.getPage(pageId: pageId1)
        try await bufferManager.unpinPage(pageId: pageId1)
        
        // Add second page (should evict first)
        let pageId2: PageID = 2
        _ = try await bufferManager.getPage(pageId: pageId2)
        
        let page1InCache = await bufferManager.isPageInCache(pageId: pageId1)
        XCTAssertFalse(page1InCache, "Page 1 should be evicted")
        
        let page2InCache = await bufferManager.isPageInCache(pageId: pageId2)
        XCTAssertTrue(page2InCache, "Page 2 should be in cache")
    }
    
    func testClockSweepEmpty() async throws {
        let bufferManager = try createBufferManager()
        
        // Clock sweep on empty buffer (should succeed)
        try await bufferManager.clockSweep()
    }
    
    func testClearBuffer() async throws {
        let bufferManager = try createBufferManager()
        
        // Add pages and mark dirty
        for i in 1...5 {
            let pageId = PageID(i)
            _ = try await bufferManager.getPage(pageId: pageId)
            try await bufferManager.markPageDirty(pageId: pageId)
        }
        
        // Update flushedLSN to allow flush
        await bufferManager.updateFlushedLSN(10)
        
        // Clear buffer
        try await bufferManager.clearBuffer()
        
        let metrics = await bufferManager.getBufferMetrics()
        XCTAssertEqual(metrics.usedFrames, 0, "Should have no used frames after clear")
        XCTAssertEqual(metrics.dirtyFrames, 0, "Should have no dirty frames after clear")
        XCTAssertEqual(metrics.pinnedFrames, 0, "Should have no pinned frames after clear")
    }
    
    // MARK: - Query Operations Tests
    
    func testQueryOperations() async throws {
        let bufferManager = try createBufferManager()
        
        // Add pages
        let pageId1: PageID = 1
        let pageId2: PageID = 2
        
        _ = try await bufferManager.getPage(pageId: pageId1)
        try await bufferManager.markPageDirty(pageId: pageId1)
        
        _ = try await bufferManager.getPage(pageId: pageId2)
        
        // Test query operations
        let pinnedPages = await bufferManager.getPinnedPages()
        XCTAssertTrue(pinnedPages.contains(pageId2), "Page 2 should be pinned")
        
        let dirtyPages = await bufferManager.getDirtyPages()
        XCTAssertTrue(dirtyPages.contains(pageId1), "Page 1 should be dirty")
        
        let evictionList = await bufferManager.getEvictionList()
        XCTAssertTrue(evictionList.contains(pageId1), "Page 1 should be in eviction list")
        XCTAssertTrue(evictionList.contains(pageId2), "Page 2 should be in eviction list")
        
        let pageTable = await bufferManager.getPageTable()
        XCTAssertNotNil(pageTable[pageId1], "Page 1 should be in page table")
        XCTAssertNotNil(pageTable[pageId2], "Page 2 should be in page table")
        
        let bufferPool = await bufferManager.getBufferPool()
        XCTAssertGreaterThan(bufferPool.count, 0, "Buffer pool should have pages")
    }
}

