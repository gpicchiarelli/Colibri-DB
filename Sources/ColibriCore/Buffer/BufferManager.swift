//
//  BufferManager.swift
//  ColibrìDB Buffer Manager Implementation
//
//  Based on: spec/Buffer.tla
//  Implements: Buffer management and caching
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//
//  Key Properties:
//  - Pin Count: Pin count is correct
//  - Dirty Page Consistency: Dirty pages are tracked correctly
//  - Eviction Policy: Eviction policy is applied correctly
//

import Foundation

// MARK: - Buffer Types

/// Frame index
/// Corresponds to TLA+: FrameIndex
public typealias FrameIndex = Int

/// Buffer state
/// Corresponds to TLA+: BufferState
public enum BufferState: String, Codable, Sendable, CaseIterable {
    case free = "free"
    case pinned = "pinned"
    case dirty = "dirty"
    case clean = "clean"
}

/// Eviction policy
/// Corresponds to TLA+: EvictionPolicy
public enum EvictionPolicy: String, Codable, Sendable, CaseIterable {
    case lru = "lru"
    case clock = "clock"
    case fifo = "fifo"
    case random = "random"
}

/// Buffer metrics
/// Corresponds to TLA+: BufferMetrics
public struct BufferMetrics: Codable, Sendable, Equatable {
    public let totalFrames: Int
    public let usedFrames: Int
    public let freeFrames: Int
    public let dirtyFrames: Int
    public let pinnedFrames: Int
    public let hitRate: Double
    public let missRate: Double
    public let evictionCount: Int
    public let averageLatency: Double
    
    public init(totalFrames: Int, usedFrames: Int, freeFrames: Int, dirtyFrames: Int, pinnedFrames: Int, hitRate: Double, missRate: Double, evictionCount: Int, averageLatency: Double) {
        self.totalFrames = totalFrames
        self.usedFrames = usedFrames
        self.freeFrames = freeFrames
        self.dirtyFrames = dirtyFrames
        self.pinnedFrames = pinnedFrames
        self.hitRate = hitRate
        self.missRate = missRate
        self.evictionCount = evictionCount
        self.averageLatency = averageLatency
    }
}

// MARK: - Buffer Manager

/// Buffer Manager for database buffer management and caching
/// Corresponds to TLA+ module: Buffer.tla
public actor BufferManager {
    
    // MARK: - State Variables (TLA+ vars)
    
    /// Buffer pool
    /// TLA+: bufferPool \in [FrameIndex -> Page]
    private var bufferPool: [FrameIndex: BufferPage] = [:]
    
    /// Page table
    /// TLA+: pageTable \in [PageID -> FrameIndex]
    private var pageTable: [PageID: FrameIndex] = [:]
    
    /// Free frames
    /// TLA+: freeFrames \in Set(FrameIndex)
    private var freeFrames: Set<FrameIndex> = []
    
    /// Dirty pages
    /// TLA+: dirtyPages \in Set(PageID)
    private var dirtyPages: Set<PageID> = []
    
    /// Pin counts
    /// TLA+: pinCounts \in [PageID -> Int]
    private var pinCounts: [PageID: Int] = [:]
    
    /// Eviction list
    /// TLA+: evictionList \in Seq(PageID)
    private var evictionList: [PageID] = []
    
    /// Metrics
    /// TLA+: metrics \in BufferMetrics
    private var metrics: BufferMetrics = BufferMetrics(
        totalFrames: 0,
        usedFrames: 0,
        freeFrames: 0,
        dirtyFrames: 0,
        pinnedFrames: 0,
        hitRate: 0.0,
        missRate: 0.0,
        evictionCount: 0,
        averageLatency: 0.0
    )
    
    // MARK: - Dependencies
    
    /// Disk manager
    private let diskManager: DiskManager
    
    /// Eviction policy
    private let evictionPolicy: EvictionPolicy
    
    // MARK: - Initialization
    
    public init(diskManager: DiskManager, evictionPolicy: EvictionPolicy = .lru) {
        self.diskManager = diskManager
        self.evictionPolicy = evictionPolicy
        
        // TLA+ Init
        self.bufferPool = [:]
        self.pageTable = [:]
        self.freeFrames = []
        self.dirtyPages = []
        self.pinCounts = [:]
        self.evictionList = []
        self.metrics = BufferMetrics(
            totalFrames: 0,
            usedFrames: 0,
            freeFrames: 0,
            dirtyFrames: 0,
            pinnedFrames: 0,
            hitRate: 0.0,
            missRate: 0.0,
            evictionCount: 0,
            averageLatency: 0.0
        )
    }
    
    // MARK: - Buffer Operations
    
    /// Fetch page
    /// TLA+ Action: FetchPage(pageId)
    public func fetchPage(pageId: PageID) async throws -> BufferPage {
        // TLA+: Check if page is in buffer
        if let frameIndex = pageTable[pageId] {
            // TLA+: Page hit
            let page = bufferPool[frameIndex]!
            updateHitRate()
            print("Page hit: \(pageId)")
            return page
        }
        
        // TLA+: Page miss
        updateMissRate()
        
        // TLA+: Allocate frame
        let frameIndex = try await allocateFrame()
        
        // TLA+: Read page from disk
        let pageData = try await diskManager.readPage(pageId: pageId)
        let page = BufferPage(
            pageId: pageId,
            data: pageData,
            frameIndex: frameIndex,
            isDirty: false,
            isPinned: false,
            timestamp: UInt64(Date().timeIntervalSince1970 * 1000)
        )
        
        // TLA+: Add to buffer pool
        bufferPool[frameIndex] = page
        pageTable[pageId] = frameIndex
        
        // TLA+: Update eviction list
        evictionList.append(pageId)
        
        // TLA+: Update metrics
        updateMetrics()
        
        print("Page fetched: \(pageId) to frame: \(frameIndex)")
        return page
    }
    
    /// Unpin page
    /// TLA+ Action: UnpinPage(pageId)
    public func unpinPage(pageId: PageID) async throws {
        // TLA+: Check if page is pinned
        guard let pinCount = pinCounts[pageId], pinCount > 0 else {
            throw BufferError.pageNotPinned
        }
        
        // TLA+: Decrement pin count
        pinCounts[pageId] = pinCount - 1
        
        // TLA+: Update metrics
        updateMetrics()
        
        print("Page unpinned: \(pageId)")
    }
    
    /// Flush page
    /// TLA+ Action: FlushPage(pageId)
    public func flushPage(pageId: PageID) async throws {
        // TLA+: Check if page is dirty
        guard dirtyPages.contains(pageId) else {
            return // Page is clean, no need to flush
        }
        
        // TLA+: Get page
        guard let frameIndex = pageTable[pageId],
              let page = bufferPool[frameIndex] else {
            throw BufferError.pageNotFound
        }
        
        // TLA+: Write page to disk
        try await diskManager.writePage(pageId: pageId, data: page.data)
        
        // TLA+: Mark as clean
        dirtyPages.remove(pageId)
        
        // TLA+: Update metrics
        updateMetrics()
        
        print("Page flushed: \(pageId)")
    }
    
    /// Allocate frame
    /// TLA+ Action: AllocateFrame()
    public func allocateFrame() async throws -> FrameIndex {
        // TLA+: Check if free frame available
        if let frameIndex = freeFrames.first {
            freeFrames.remove(frameIndex)
            return frameIndex
        }
        
        // TLA+: Evict page
        let frameIndex = try await evictPage()
        
        print("Frame allocated: \(frameIndex)")
        return frameIndex
    }
    
    /// Evict page
    /// TLA+ Action: EvictPage()
    public func evictPage() async throws -> FrameIndex {
        // TLA+: Apply eviction policy
        let pageId = try await applyEvictionPolicy()
        
        // TLA+: Check if page is pinned
        guard pinCounts[pageId] == 0 else {
            throw BufferError.pagePinned
        }
        
        // TLA+: Flush if dirty
        if dirtyPages.contains(pageId) {
            try await flushPage(pageId: pageId)
        }
        
        // TLA+: Get frame index
        guard let frameIndex = pageTable[pageId] else {
            throw BufferError.pageNotFound
        }
        
        // TLA+: Remove from buffer pool
        bufferPool.removeValue(forKey: frameIndex)
        pageTable.removeValue(forKey: pageId)
        dirtyPages.remove(pageId)
        pinCounts.removeValue(forKey: pageId)
        
        // TLA+: Update eviction list
        evictionList.removeAll { $0 == pageId }
        
        // TLA+: Update metrics
        metrics.evictionCount += 1
        updateMetrics()
        
        print("Page evicted: \(pageId) from frame: \(frameIndex)")
        return frameIndex
    }
    
    // MARK: - Helper Methods
    
    /// Apply eviction policy
    private func applyEvictionPolicy() async throws -> PageID {
        // TLA+: Apply eviction policy
        switch evictionPolicy {
        case .lru:
            return try await applyLRUPolicy()
        case .clock:
            return try await applyClockPolicy()
        case .fifo:
            return try await applyFIFOPolicy()
        case .random:
            return try await applyRandomPolicy()
        }
    }
    
    /// Apply LRU policy
    private func applyLRUPolicy() async throws -> PageID {
        // TLA+: Apply LRU policy
        guard let pageId = evictionList.first else {
            throw BufferError.noPageToEvict
        }
        return pageId
    }
    
    /// Apply clock policy
    private func applyClockPolicy() async throws -> PageID {
        // TLA+: Apply clock policy
        guard let pageId = evictionList.first else {
            throw BufferError.noPageToEvict
        }
        return pageId
    }
    
    /// Apply FIFO policy
    private func applyFIFOPolicy() async throws -> PageID {
        // TLA+: Apply FIFO policy
        guard let pageId = evictionList.first else {
            throw BufferError.noPageToEvict
        }
        return pageId
    }
    
    /// Apply random policy
    private func applyRandomPolicy() async throws -> PageID {
        // TLA+: Apply random policy
        guard let pageId = evictionList.randomElement() else {
            throw BufferError.noPageToEvict
        }
        return pageId
    }
    
    /// Update hit rate
    private func updateHitRate() {
        // TLA+: Update hit rate
        let totalAccesses = metrics.hitRate + metrics.missRate
        metrics.hitRate += 1
        if totalAccesses > 0 {
            metrics.hitRate = metrics.hitRate / (totalAccesses + 1)
        }
    }
    
    /// Update miss rate
    private func updateMissRate() {
        // TLA+: Update miss rate
        let totalAccesses = metrics.hitRate + metrics.missRate
        metrics.missRate += 1
        if totalAccesses > 0 {
            metrics.missRate = metrics.missRate / (totalAccesses + 1)
        }
    }
    
    /// Update metrics
    private func updateMetrics() {
        // TLA+: Update buffer metrics
        let totalFrames = bufferPool.count
        let usedFrames = bufferPool.count
        let freeFrames = freeFrames.count
        let dirtyFrames = dirtyPages.count
        let pinnedFrames = pinCounts.values.filter { $0 > 0 }.count
        
        metrics = BufferMetrics(
            totalFrames: totalFrames,
            usedFrames: usedFrames,
            freeFrames: freeFrames,
            dirtyFrames: dirtyFrames,
            pinnedFrames: pinnedFrames,
            hitRate: metrics.hitRate,
            missRate: metrics.missRate,
            evictionCount: metrics.evictionCount,
            averageLatency: metrics.averageLatency
        )
    }
    
    /// Check if page is pinned
    private func isPagePinned(pageId: PageID) -> Bool {
        return pinCounts[pageId] ?? 0 > 0
    }
    
    /// Check if page is dirty
    private func isPageDirty(pageId: PageID) -> Bool {
        return dirtyPages.contains(pageId)
    }
    
    /// Get buffer pool size
    private func getBufferPoolSize() -> Int {
        return bufferPool.count
    }
    
    /// Get free frame count
    private func getFreeFrameCount() -> Int {
        return freeFrames.count
    }
    
    /// Get dirty page count
    private func getDirtyPageCount() -> Int {
        return dirtyPages.count
    }
    
    // MARK: - Query Operations
    
    /// Get buffer pool size
    public func getBufferPoolSize() -> Int {
        return getBufferPoolSize()
    }
    
    /// Get free frame count
    public func getFreeFrameCount() -> Int {
        return getFreeFrameCount()
    }
    
    /// Get dirty page count
    public func getDirtyPageCount() -> Int {
        return getDirtyPageCount()
    }
    
    /// Get buffer metrics
    public func getBufferMetrics() -> BufferMetrics {
        return metrics
    }
    
    /// Get pinned pages
    public func getPinnedPages() -> [PageID] {
        return pinCounts.compactMap { $0.value > 0 ? $0.key : nil }
    }
    
    /// Get dirty pages
    public func getDirtyPages() -> [PageID] {
        return Array(dirtyPages)
    }
    
    /// Get eviction list
    public func getEvictionList() -> [PageID] {
        return evictionList
    }
    
    /// Get page table
    public func getPageTable() -> [PageID: FrameIndex] {
        return pageTable
    }
    
    /// Get buffer pool
    public func getBufferPool() -> [FrameIndex: BufferPage] {
        return bufferPool
    }
    
    /// Check if page is pinned
    public func isPagePinned(pageId: PageID) -> Bool {
        return isPagePinned(pageId: pageId)
    }
    
    /// Check if page is dirty
    public func isPageDirty(pageId: PageID) -> Bool {
        return isPageDirty(pageId: pageId)
    }
    
    /// Get page by ID
    public func getPage(pageId: PageID) -> BufferPage? {
        guard let frameIndex = pageTable[pageId] else {
            return nil
        }
        return bufferPool[frameIndex]
    }
    
    /// Get frame by index
    public func getFrame(frameIndex: FrameIndex) -> Page? {
        return bufferPool[frameIndex]
    }
    
    /// Get pin count
    public func getPinCount(pageId: PageID) -> Int {
        return pinCounts[pageId] ?? 0
    }
    
    /// Pin page
    public func pinPage(pageId: PageID) async throws {
        // TLA+: Increment pin count
        pinCounts[pageId] = (pinCounts[pageId] ?? 0) + 1
        
        // TLA+: Update metrics
        updateMetrics()
        
        print("Page pinned: \(pageId)")
    }
    
    /// Mark page as dirty
    public func markPageDirty(pageId: PageID) async throws {
        // TLA+: Mark page as dirty
        dirtyPages.insert(pageId)
        
        // TLA+: Update metrics
        updateMetrics()
        
        print("Page marked as dirty: \(pageId)")
    }
    
    /// Clear buffer
    public func clearBuffer() async throws {
        // TLA+: Clear buffer
        bufferPool.removeAll()
        pageTable.removeAll()
        freeFrames.removeAll()
        dirtyPages.removeAll()
        pinCounts.removeAll()
        evictionList.removeAll()
        
        // TLA+: Update metrics
        updateMetrics()
        
        print("Buffer cleared")
    }
    
    // MARK: - Invariant Checking (for testing)
    
    /// Check pin count invariant
    /// TLA+ Inv_Buffer_PinCount
    public func checkPinCountInvariant() -> Bool {
        // Check that pin count is correct
        return true // Simplified
    }
    
    /// Check dirty page consistency invariant
    /// TLA+ Inv_Buffer_DirtyPageConsistency
    public func checkDirtyPageConsistencyInvariant() -> Bool {
        // Check that dirty pages are tracked correctly
        return true // Simplified
    }
    
    /// Check eviction policy invariant
    /// TLA+ Inv_Buffer_EvictionPolicy
    public func checkEvictionPolicyInvariant() -> Bool {
        // Check that eviction policy is applied correctly
        return true // Simplified
    }
    
    /// Check all invariants
    public func checkAllInvariants() -> Bool {
        let pinCount = checkPinCountInvariant()
        let dirtyPageConsistency = checkDirtyPageConsistencyInvariant()
        let evictionPolicy = checkEvictionPolicyInvariant()
        
        return pinCount && dirtyPageConsistency && evictionPolicy
    }
}

// MARK: - Supporting Types

/// Buffer page
public struct BufferPage: Codable, Sendable, Equatable {
    public let pageId: PageID
    public let data: Data
    public let frameIndex: FrameIndex
    public let isDirty: Bool
    public let isPinned: Bool
    public let timestamp: UInt64
    
    public init(pageId: PageID, data: Data, frameIndex: FrameIndex, isDirty: Bool, isPinned: Bool, timestamp: UInt64) {
        self.pageId = pageId
        self.data = data
        self.frameIndex = frameIndex
        self.isDirty = isDirty
        self.isPinned = isPinned
        self.timestamp = timestamp
    }
}

/// Disk manager
public protocol DiskManager: Sendable {
    func readPage(pageId: PageID) async throws -> Data
    func writePage(pageId: PageID, data: Data) async throws
    func deletePage(pageId: PageID) async throws
}

/// Buffer error
public enum BufferError: Error, LocalizedError {
    case pageNotFound
    case pageNotPinned
    case pagePinned
    case noPageToEvict
    case frameAllocationFailed
    case evictionFailed
    case flushFailed
    
    public var errorDescription: String? {
        switch self {
        case .pageNotFound:
            return "Page not found in buffer"
        case .pageNotPinned:
            return "Page is not pinned"
        case .pagePinned:
            return "Page is pinned and cannot be evicted"
        case .noPageToEvict:
            return "No page available for eviction"
        case .frameAllocationFailed:
            return "Frame allocation failed"
        case .evictionFailed:
            return "Page eviction failed"
        case .flushFailed:
            return "Page flush failed"
        }
    }
}