//
//  BufferPoolManagerImpl.swift
//  ColibrìDB Buffer Pool Manager Implementation
//
//  Concrete implementation of BufferPoolManager protocol
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//

import Foundation

/// Concrete implementation of BufferPoolManager protocol
public actor BufferPoolManagerImpl: BufferPoolManager {
    // MARK: - Properties
    
    private let bufferPool: BufferPool
    
    // MARK: - Initialization
    
    /// Initialize buffer pool manager
    /// - Parameter bufferPool: Buffer pool instance to use
    public init(bufferPool: BufferPool) {
        self.bufferPool = bufferPool
    }
    
    // MARK: - Protocol Implementation
    
    /// Get a page from the buffer pool
    /// - Parameter pageID: Page ID to retrieve
    /// - Returns: Heap page
    public func getPage(pageID: PageID) async throws -> HeapPage {
        let page = try await bufferPool.getPage(pageID)
        // Convert BufferPool.Page to HeapPage
        var heapPage = HeapPage(pageID: page.header.pageID)
        heapPage.header = page.header
        heapPage.slots = page.slots
        heapPage.data = page.data
        heapPage.lsn = page.header.pageLSN
        return heapPage
    }
    
    /// Write a page back to the buffer pool
    /// - Parameter page: Heap page to write
    public func putPage(page: HeapPage) async throws {
        // Convert HeapPage to BufferPool.Page and write back
        var bufferPage = Page(pageID: page.pageID)
        bufferPage.header = page.header
        bufferPage.slots = page.slots
        bufferPage.data = page.data
        try await bufferPool.putPage(page.pageID, page: bufferPage, isDirty: page.isDirty)
    }
    
    /// Pin a page in the buffer pool
    /// - Parameter pageID: Page ID to pin
    public func pinPage(pageID: PageID) async throws {
        // Pin is handled by BufferPool internally
    }
    
    /// Unpin a page in the buffer pool
    /// - Parameter pageID: Page ID to unpin
    public func unpinPage(pageID: PageID) async throws {
        // Unpin is handled by BufferPool internally
    }
}

