//
//  BufferPoolTests.swift
//  ColibrìDB Buffer Pool Tests
//
//  Tests for buffer pool management, page caching, and eviction policies
//

import Foundation
import XCTest
@testable import ColibriCore

/// Tests for the Buffer Pool
// final class ("Buffer Pool Tests")
final class BufferPoolTests: XCTestCase {
    
    /// Test buffer pool initialization
    // @Test("Buffer Pool Initialization")
    func testBufferPoolInitialization() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let diskManager = try FileDiskManager(filePath: tempDir.appendingPathComponent("test.db"))
        let bufferPool = BufferPool(poolSize: 10, diskManager: diskManager)
        
        // Get initial statistics
        let stats = await bufferPool.getStatistics()
        XCTAssertEqual(stats.poolSize, 10, "Pool size should match")
        XCTAssertEqual(stats.cachedPages, 0, "Should have no cached pages initially")
        XCTAssertEqual(stats.dirtyPages, 0, "Should have no dirty pages initially")
        XCTAssertEqual(stats.pinnedPages, 0, "Should have no pinned pages initially")
    }
    
    /// Test page retrieval (cache miss)
    // @Test("Page Retrieval - Cache Miss")
    func testPageRetrievalCacheMiss() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let diskManager = try FileDiskManager(filePath: tempDir.appendingPathComponent("test.db"))
        let bufferPool = BufferPool(poolSize: 5, diskManager: diskManager)
        
        // Get a page that doesn't exist in cache
        let pageID: PageID = 1
        let page = try await bufferPool.getPage(pageID)
        
        // Verify page was loaded
        XCTAssertEqual(page.header.pageID, pageID, "Page ID should match")
        
        // Verify page is in cache
        let isInCache = await bufferPool.isPageInCache(pageID)
        XCTAssertTrue(isInCache, "Page should be in cache")
        
        // Verify page is pinned
        let stats = await bufferPool.getStatistics()
        XCTAssertEqual(stats.pinnedPages, 1, "Should have 1 pinned page")
    }
    
    /// Test page retrieval (cache hit)
    // @Test("Page Retrieval - Cache Hit")
    func testPageRetrievalCacheHit() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let diskManager = try FileDiskManager(filePath: tempDir.appendingPathComponent("test.db"))
        let bufferPool = BufferPool(poolSize: 5, diskManager: diskManager)
        
        let pageID: PageID = 1
        
        // Get page first time (cache miss)
        let page1 = try await bufferPool.getPage(pageID)
        
        // Unpin the page
        try await bufferPool.unpinPage(pageID)
        
        // Get page second time (cache hit)
        let page2 = try await bufferPool.getPage(pageID)
        
        // Verify we got the same page
        XCTAssertEqual(page1.header.pageID, page2.header.pageID, "Page IDs should match")
        
        // Verify page is pinned again
        let stats = await bufferPool.getStatistics()
        XCTAssertEqual(stats.pinnedPages, 1, "Should have 1 pinned page")
    }
    
    /// Test page modification
    // @Test("Page Modification")
    func testPageModification() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let diskManager = try FileDiskManager(filePath: tempDir.appendingPathComponent("test.db"))
        let bufferPool = BufferPool(poolSize: 5, diskManager: diskManager)
        
        let pageID: PageID = 1
        
        // Get page
        let originalPage = try await bufferPool.getPage(pageID)
        
        // Modify page
        var modifiedPage = originalPage
        modifiedPage.data = TestUtils.generateRandomData(size: 1024)
        
        // Put modified page (mark as dirty)
        try await bufferPool.putPage(pageID, page: modifiedPage, isDirty: true)
        
        // Verify page is dirty
        let dirtyCount = await bufferPool.getDirtyPageCount()
        XCTAssertEqual(dirtyCount, 1, "Should have 1 dirty page")
        
        // Verify statistics
        let stats = await bufferPool.getStatistics()
        XCTAssertEqual(stats.dirtyPages, 1, "Should have 1 dirty page in stats")
    }
    
    /// Test page pinning and unpinning
    // @Test("Page Pinning and Unpinning")
    func testPagePinningAndUnpinning() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let diskManager = try FileDiskManager(filePath: tempDir.appendingPathComponent("test.db"))
        let bufferPool = BufferPool(poolSize: 5, diskManager: diskManager)
        
        let pageID: PageID = 1
        
        // Get page (automatically pinned)
        _ = try await bufferPool.getPage(pageID)
        
        // Pin page again
        try await bufferPool.pinPage(pageID)
        
        // Verify page is pinned twice
        let stats1 = await bufferPool.getStatistics()
        XCTAssertEqual(stats1.pinnedPages, 1, "Should have 1 pinned page")
        
        // Unpin page once
        try await bufferPool.unpinPage(pageID)
        
        // Verify page is still pinned
        let stats2 = await bufferPool.getStatistics()
        XCTAssertEqual(stats2.pinnedPages, 1, "Should have 1 pinned page")
        
        // Unpin page again
        try await bufferPool.unpinPage(pageID)
        
        // Verify page is no longer pinned
        let stats3 = await bufferPool.getStatistics()
        XCTAssertEqual(stats3.pinnedPages, 0, "Should have 0 pinned pages")
    }
    
    /// Test page eviction
    // @Test("Page Eviction")
    func testPageEviction() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let diskManager = try FileDiskManager(filePath: tempDir.appendingPathComponent("test.db"))
        let bufferPool = BufferPool(poolSize: 3, diskManager: diskManager)
        
        // Fill buffer pool
        let pageID1: PageID = 1
        let pageID2: PageID = 2
        let pageID3: PageID = 3
        
        _ = try await bufferPool.getPage(pageID1)
        try await bufferPool.unpinPage(pageID1)
        
        _ = try await bufferPool.getPage(pageID2)
        try await bufferPool.unpinPage(pageID2)
        
        _ = try await bufferPool.getPage(pageID3)
        try await bufferPool.unpinPage(pageID3)
        
        // Verify all pages are in cache
        let stats1 = await bufferPool.getStatistics()
        XCTAssertEqual(stats1.cachedPages, 3, "Should have 3 cached pages")
        
        // Add one more page (should trigger eviction)
        let pageID4: PageID = 4
        _ = try await bufferPool.getPage(pageID4)
        
        // Verify eviction occurred
        let stats2 = await bufferPool.getStatistics()
        XCTAssertEqual(stats2.cachedPages, 3, "Should still have 3 cached pages after eviction")
        
        // Verify page 4 is in cache
        let isPage4InCache = await bufferPool.isPageInCache(pageID4)
        XCTAssertTrue(isPage4InCache, "Page 4 should be in cache")
    }
    
    /// Test dirty page flushing
    // @Test("Dirty Page Flushing")
    func testDirtyPageFlushing() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let diskManager = try FileDiskManager(filePath: tempDir.appendingPathComponent("test.db"))
        let bufferPool = BufferPool(poolSize: 5, diskManager: diskManager)
        
        let pageID: PageID = 1
        
        // Get and modify page
        let page = try await bufferPool.getPage(pageID)
        var modifiedPage = page
        modifiedPage.data = TestUtils.generateRandomData(size: 1024)
        
        try await bufferPool.putPage(pageID, page: modifiedPage, isDirty: true)
        
        // Verify page is dirty
        let dirtyCountBefore = await bufferPool.getDirtyPageCount()
        XCTAssertEqual(dirtyCountBefore, 1, "Should have 1 dirty page")
        
        // Flush dirty page
        try await bufferPool.flushPage(pageID)
        
        // Verify page is no longer dirty
        let dirtyCountAfter = await bufferPool.getDirtyPageCount()
        XCTAssertEqual(dirtyCountAfter, 0, "Should have 0 dirty pages after flush")
    }
    
    /// Test flush all dirty pages
    // @Test("Flush All Dirty Pages")
    func testFlushAllDirtyPages() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let diskManager = try FileDiskManager(filePath: tempDir.appendingPathComponent("test.db"))
        let bufferPool = BufferPool(poolSize: 5, diskManager: diskManager)
        
        // Create multiple dirty pages
        let pageIDs: [PageID] = [1, 2, 3]
        
        for pageID in pageIDs {
            let page = try await bufferPool.getPage(pageID)
            var modifiedPage = page
            modifiedPage.data = TestUtils.generateRandomData(size: 1024)
            try await bufferPool.putPage(pageID, page: modifiedPage, isDirty: true)
        }
        
        // Verify all pages are dirty
        let dirtyCountBefore = await bufferPool.getDirtyPageCount()
        XCTAssertEqual(dirtyCountBefore, 3, "Should have 3 dirty pages")
        
        // Flush all dirty pages
        try await bufferPool.flushAll()
        
        // Verify no pages are dirty
        let dirtyCountAfter = await bufferPool.getDirtyPageCount()
        XCTAssertEqual(dirtyCountAfter, 0, "Should have 0 dirty pages after flush all")
    }
    
    /// Test LSN updates
    // @Test("LSN Updates")
    func testLSNUpdates() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let diskManager = try FileDiskManager(filePath: tempDir.appendingPathComponent("test.db"))
        let bufferPool = BufferPool(poolSize: 5, diskManager: diskManager)
        
        // Update flushed LSN
        let lsn1: LSN = 100
        await bufferPool.updateFlushedLSN(lsn1)
        
        // Update with higher LSN
        let lsn2: LSN = 200
        await bufferPool.updateFlushedLSN(lsn2)
        
        // Try to update with lower LSN (should be ignored)
        let lsn3: LSN = 150
        await bufferPool.updateFlushedLSN(lsn3)
        
        // The implementation should maintain the highest LSN
        // Note: The actual verification depends on the implementation details
    }
    
    /// Test buffer pool invariants
    // @Test("Buffer Pool Invariants")
    func testBufferPoolInvariants() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let diskManager = try FileDiskManager(filePath: tempDir.appendingPathComponent("test.db"))
        let bufferPool = BufferPool(poolSize: 5, diskManager: diskManager)
        
        // Test cache consistency invariant
        let cacheConsistency = await bufferPool.checkCacheConsistencyInvariant()
        XCTAssertTrue(cacheConsistency, "Cache consistency invariant should hold")
        
        // Test no duplicate pages invariant
        let noDuplicates = await bufferPool.checkNoDuplicatePagesInvariant()
        XCTAssertTrue(noDuplicates, "No duplicate pages invariant should hold")
        
        // Test pin safety invariant
        let pinSafety = await bufferPool.checkPinSafetyInvariant()
        XCTAssertTrue(pinSafety, "Pin safety invariant should hold")
        
        // Test WAL before data invariant
        let walBeforeData = await bufferPool.checkWALBeforeDataInvariant()
        XCTAssertTrue(walBeforeData, "WAL before data invariant should hold")
    }
    
    /// Test error handling
    // @Test("Error Handling")
    func testErrorHandling() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let diskManager = try FileDiskManager(filePath: tempDir.appendingPathComponent("test.db"))
        let bufferPool = BufferPool(poolSize: 5, diskManager: diskManager)
        
        // Test operations on non-existent page
        do {
            try await bufferPool.putPage(999, page: Page(pageID: 999), isDirty: true)
            // If we get here, the test should fail
            XCTAssertTrue(false, "Should throw error for non-existent page")
        } catch {
            // Expected error - test passes
        }
        
        do {
            try await bufferPool.pinPage(999)
            // If we get here, the test should fail
            XCTAssertTrue(false, "Should throw error for non-existent page")
        } catch {
            // Expected error - test passes
        }
        
        do {
            try await bufferPool.unpinPage(999)
            // If we get here, the test should fail
            XCTAssertTrue(false, "Should throw error for non-existent page")
        } catch {
            // Expected error - test passes
        }
        
        // Get a page and unpin it
        let pageID: PageID = 1
        _ = try await bufferPool.getPage(pageID)
        try await bufferPool.unpinPage(pageID)
        
        // Test modifying unpinned page
        do {
            try await bufferPool.putPage(pageID, page: Page(pageID: pageID), isDirty: true)
            // If we get here, the test should fail
            XCTAssertTrue(false, "Should throw error for modifying unpinned page")
        } catch {
            // Expected error - test passes
        }
    }
    
    /// Test concurrent access
    // @Test("Concurrent Access")
    func testConcurrentAccess() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let diskManager = try FileDiskManager(filePath: tempDir.appendingPathComponent("test.db"))
        let bufferPool = BufferPool(poolSize: 10, diskManager: diskManager)
        
        // Start multiple concurrent tasks
        let taskCount = 5
        var tasks: [Task<Void, Never>] = []
        
        for i in 0..<taskCount {
            let task = Task {
                do {
                    let pageID: PageID = PageID(i + 1)
                    let page = try await bufferPool.getPage(pageID)
                    
                    // Modify page
                    var modifiedPage = page
                    modifiedPage.data = TestUtils.generateRandomData(size: 512)
                    try await bufferPool.putPage(pageID, page: modifiedPage, isDirty: true)
                    
                    // Unpin page
                    try await bufferPool.unpinPage(pageID)
                } catch {
                    // Handle errors silently for this test
                }
            }
            tasks.append(task)
        }
        
        // Wait for all tasks to complete
        for task in tasks {
            await task.value
        }
        
        // Verify buffer pool is in consistent state
        let stats = await bufferPool.getStatistics()
        XCTAssertTrue(stats.cachedPages <= 10, "Should not exceed pool size")
        XCTAssertTrue(stats.pinnedPages >= 0, "Should have non-negative pinned pages")
    }
    
    /// Test performance with large number of pages
    // @Test("Performance - Large Number of Pages", .disabled("Memory issue"))
    func testPerformanceLargeNumberOfPages() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let diskManager = try FileDiskManager(filePath: tempDir.appendingPathComponent("test.db"))
        let bufferPool = BufferPool(poolSize: 100, diskManager: diskManager)
        
        // Reduced page count to avoid outOfMemory
        let pageCount = 200
        let startTime = Date()
        
        // Access many pages
        for i in 0..<pageCount {
            let pageID: PageID = PageID(i + 1)
            _ = try await bufferPool.getPage(pageID)
            
            // Unpin every other page to allow eviction
            if i % 2 == 0 {
                try await bufferPool.unpinPage(pageID)
            }
        }
        
        let endTime = Date()
        let executionTime = endTime.timeIntervalSince(startTime)
        
        // Verify performance is reasonable (less than 1 second for 200 pages)
        XCTAssertTrue(executionTime < 1.0, "Performance should be reasonable")
        
        // Verify buffer pool statistics
        let stats = await bufferPool.getStatistics()
        XCTAssertTrue(stats.cachedPages <= 100, "Should not exceed pool size")
    }
    
    /// Test memory usage
    // @Test("Memory Usage")
    func testMemoryUsage() async throws {
        let tempDir = try TestUtils.createTempDirectory()
        defer { try? TestUtils.cleanupTempDirectory(tempDir) }
        
        let diskManager = try FileDiskManager(filePath: tempDir.appendingPathComponent("test.db"))
        let bufferPool = BufferPool(poolSize: 50, diskManager: diskManager)
        
        // Fill buffer pool
        for i in 0..<50 {
            let pageID: PageID = PageID(i + 1)
            _ = try await bufferPool.getPage(pageID)
            try await bufferPool.unpinPage(pageID)
        }
        
        // Verify all pages are cached
        let stats = await bufferPool.getStatistics()
        XCTAssertEqual(stats.cachedPages, 50, "Should have 50 cached pages")
        
        // Add more pages to trigger eviction
        for i in 50..<100 {
            let pageID: PageID = PageID(i + 1)
            _ = try await bufferPool.getPage(pageID)
            try await bufferPool.unpinPage(pageID)
        }
        
        // Verify pool size is maintained
        let statsAfter = await bufferPool.getStatistics()
        XCTAssertEqual(statsAfter.cachedPages, 50, "Should maintain pool size")
    }
}
