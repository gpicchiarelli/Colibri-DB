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
    private let bufferPool: BufferPool
    
    public init(bufferPool: BufferPool) {
        self.bufferPool = bufferPool
    }
    
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
    
    public func putPage(page: HeapPage) async throws {
        // Convert HeapPage to BufferPool.Page and write back
        var bufferPage = Page(pageID: page.pageID)
        bufferPage.header = page.header
        bufferPage.slots = page.slots
        bufferPage.data = page.data
        try await bufferPool.putPage(page.pageID, page: bufferPage, isDirty: page.isDirty)
    }
    
    public func pinPage(pageID: PageID) async throws {
        // Pin is handled by BufferPool internally
    }
    
    public func unpinPage(pageID: PageID) async throws {
        // Unpin is handled by BufferPool internally
    }
}

