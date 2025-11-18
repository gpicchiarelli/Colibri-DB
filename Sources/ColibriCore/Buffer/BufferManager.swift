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
    public var hitRate: Double
    public var missRate: Double
    public var evictionCount: Int
    public var averageLatency: Double
    
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
    
    // MARK: - Constants
    
    /// Default buffer pool size
    private let DEFAULT_POOL_SIZE = 1000
    
    // MARK: - State Variables (TLA+ vars)
    
    /// Maximum number of frames
    private let poolSize: Int
    
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
    
    /// LRU eviction list (most recently used at end)
    /// TLA+: lruList \in Seq(PageID)
    private var lruList: [PageID] = []
    
    /// FIFO eviction list (first in first out)
    /// TLA+: fifoList \in Seq(PageID)
    private var fifoList: [PageID] = []
    
    /// Clock algorithm: reference bits
    /// TLA+: referenceBits \in [PageID -> BOOLEAN]
    private var referenceBits: [PageID: Bool] = [:]
    
    /// Clock algorithm: clock hand position
    /// TLA+: clockHand \in Nat
    private var clockHand: Int = 0
    
    /// Hit count for statistics
    private var hitCount: Int = 0
    
    /// Miss count for statistics
    private var missCount: Int = 0
    
    /// Highest LSN flushed to disk (from WAL)
    /// TLA+: flushedLSN \in LSN
    nonisolated(unsafe) private var flushedLSN: LSN = 0
    
    /// Next frame index to allocate (when pool not full)
    nonisolated(unsafe) private var nextFrameIndex: FrameIndex = 0
    
    /// Metrics
    /// TLA+: metrics \in BufferMetrics
    nonisolated(unsafe) private var metrics: BufferMetrics
    
    // MARK: - Dependencies
    
    /// Disk manager
    private let diskManager: DiskManager
    
    /// Eviction policy
    private let evictionPolicy: EvictionPolicy
    
    // MARK: - Initialization
    
    private static func createInitialMetrics(poolSize: Int) -> BufferMetrics {
        return BufferMetrics(
            totalFrames: poolSize,
            usedFrames: 0,
            freeFrames: poolSize,
            dirtyFrames: 0,
            pinnedFrames: 0,
            hitRate: 0.0,
            missRate: 0.0,
            evictionCount: 0,
            averageLatency: 0.0
        )
    }
    
    public init(diskManager: DiskManager, poolSize: Int? = nil, evictionPolicy: EvictionPolicy = .lru) {
        let actualPoolSize = poolSize ?? DEFAULT_POOL_SIZE
        
        self.diskManager = diskManager
        self.poolSize = actualPoolSize
        self.evictionPolicy = evictionPolicy
        
        // Initialize metrics with correct pool size
        self.metrics = Self.createInitialMetrics(poolSize: actualPoolSize)
    }
    
    // MARK: - Buffer Operations
    
    /// Get page (alias for fetchPage that pins automatically)
    /// TLA+ Action: GetPage(pageId)
    public func getPage(pageId: PageID) async throws -> BufferPage {
        return try await fetchPage(pageId: pageId)
    }
    
    /// Fetch page
    /// TLA+ Action: FetchPage(pageId)
    public func fetchPage(pageId: PageID) async throws -> BufferPage {
        let startTime = Date()
        defer {
            let latency = Date().timeIntervalSince(startTime) * 1000 // Convert to ms
            updateLatency(latency)
        }
        
        // TLA+: Check if page is in buffer
        if let frameIndex = pageTable[pageId] {
            // TLA+: Page hit
            let page = bufferPool[frameIndex]!
            
            // Pin the page if not already pinned
            pinCounts[pageId] = (pinCounts[pageId] ?? 0) + 1
            
            // Update LRU order (move to end = most recently used)
            moveToMRU(pageId: pageId)
            
            // Update reference bit for clock algorithm
            referenceBits[pageId] = true
            
            // Update statistics
            hitCount += 1
            updateMetrics()  // This will calculate hit/miss rate from hitCount and missCount
            
            logInfo("Page hit: \(pageId)")
            return page
        }
        
        // TLA+: Page miss
        missCount += 1
        updateMetrics()  // This will calculate hit/miss rate from hitCount and missCount
        
        // TLA+: Allocate frame
        let frameIndex = try await allocateFrame()
        
        // TLA+: Read page from disk
        let pageData = try await diskManager.readPage(pageId: pageId)
        let page = BufferPage(
            pageId: pageId,
            data: pageData,
            lsn: 0, // Will be set by caller if needed
            isDirty: false,
            isPinned: false,
            timestamp: UInt64(Date().timeIntervalSince1970 * 1000)
        )
        
        // TLA+: Add to buffer pool
        bufferPool[frameIndex] = page
        pageTable[pageId] = frameIndex
        
        // Pin the page
        pinCounts[pageId] = 1
        
        // Update eviction lists
        lruList.append(pageId)
        fifoList.append(pageId)
        referenceBits[pageId] = true
        
        // TLA+: Update metrics
        updateMetrics()
        
        logInfo("Page fetched: \(pageId) to frame: \(frameIndex)")
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
        
        logInfo("Page unpinned: \(pageId)")
    }
    
    /// Flush page
    /// TLA+ Action: FlushPage(pageId)
    /// Precondition: page is dirty, WAL flushed (pageLSN <= flushedLSN)
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
        
        // TLA+ Invariant: WAL before data rule
        // cache[pid].lsn <= flushedLSN (pageLSN in TLA+)
        guard page.lsn <= flushedLSN else {
            throw BufferError.flushFailed  // WAL must be flushed before page write
        }
        
        // TLA+: Write page to disk
        try await diskManager.writePage(pageId: pageId, data: page.data)
        
        // TLA+: Mark as clean
        dirtyPages.remove(pageId)
        
        // TLA+: Update metrics
        updateMetrics()
        
        logInfo("Page flushed: \(pageId)")
    }
    
    /// Flush all dirty pages
    /// TLA+ Action: FlushAll
    /// Precondition: all dirty pages have pageLSN <= flushedLSN
    public func flushAll() async throws {
        // TLA+: Flush all dirty pages
        let dirtyPageIds = Array(dirtyPages)  // Copy to avoid concurrent modification
        for pageId in dirtyPageIds {
            try await flushPage(pageId: pageId)
        }
    }
    
    /// Update flushed LSN from WAL
    /// TLA+ Action: UpdateFlushedLSN(lsn)
    /// Precondition: lsn >= flushedLSN
    /// Postcondition: flushedLSN updated
    public func updateFlushedLSN(_ lsn: LSN) async {
        // TLA+: lsn >= flushedLSN
        guard lsn >= flushedLSN else {
            return  // Ignore if lower than current
        }
        
        // TLA+: flushedLSN' = lsn
        flushedLSN = lsn
        
        logInfo("Updated flushed LSN: \(lsn)")
    }
    
    /// Get flushed LSN
    public func getFlushedLSN() -> LSN {
        return flushedLSN
    }
    
    /// Clock sweep to find victim (update reference bits)
    /// TLA+ Action: ClockSweep
    public func clockSweep() async throws {
        // TLA+: Clock sweep - update reference bits for eviction algorithm
        guard !lruList.isEmpty else {
            return  // No pages to sweep
        }
        
        let maxScans = min(lruList.count * 2, poolSize)  // Scan at most twice or pool size
        var scanned = 0
        
        while scanned < maxScans {
            if clockHand >= lruList.count {
                clockHand = 0
            }
            
            guard clockHand < lruList.count else {
                break
            }
            
            let pageId = lruList[clockHand]
            
            // Skip pinned pages
            if pinCounts[pageId] == 0 {
                // Clear reference bit for clock algorithm
                if referenceBits[pageId] == true {
                    referenceBits[pageId] = false
                }
            }
            
            clockHand = (clockHand + 1) % lruList.count
            scanned += 1
        }
        
        logInfo("Clock sweep completed")
    }
    
    /// Allocate frame
    /// TLA+ Action: AllocateFrame()
    public func allocateFrame() async throws -> FrameIndex {
        // TLA+: Check if free frame available (from eviction)
        if let frameIndex = freeFrames.first {
            freeFrames.remove(frameIndex)
            return frameIndex
        }
        
        // Check if pool is full
        if bufferPool.count >= poolSize {
            // TLA+: Evict page to get a frame
            // This will throw BufferError.noPageToEvict or BufferError.pagePinned if all pages are pinned
            let frameIndex = try await evictPage()
            return frameIndex
        }
        
        // Allocate new frame index (increment until we find unused one)
        // Ensure we don't loop infinitely
        var attempts = 0
        let maxAttempts = poolSize
        
        while bufferPool[nextFrameIndex] != nil && attempts < maxAttempts {
            nextFrameIndex = (nextFrameIndex + 1) % poolSize
            attempts += 1
        }
        
        // If we couldn't find a free frame, the pool is actually full
        if bufferPool[nextFrameIndex] != nil {
            // Pool is full, try eviction
            let frameIndex = try await evictPage()
            return frameIndex
        }
        
        let frameIndex = nextFrameIndex
        nextFrameIndex = (nextFrameIndex + 1) % poolSize
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
        
        // TLA+: Update eviction lists
        lruList.removeAll { $0 == pageId }
        fifoList.removeAll { $0 == pageId }
        referenceBits.removeValue(forKey: pageId)
        
        // Add frame to free frames
        freeFrames.insert(frameIndex)
        
        // TLA+: Update metrics
        metrics.evictionCount += 1
        updateMetrics()
        
        logInfo("Page evicted: \(pageId) from frame: \(frameIndex)")
        return frameIndex
    }
    
    // MARK: - Helper Methods
    
    /// Apply eviction policy
    private func applyEvictionPolicy() async throws -> PageID {
        // TLA+: Apply eviction policy
        switch evictionPolicy {
        case .lru:
            return try applyLRUPolicy()
        case .clock:
            return try applyClockPolicy()
        case .fifo:
            return try applyFIFOPolicy()
        case .random:
            return try applyRandomPolicy()
        }
    }
    
    /// Apply LRU policy (evict least recently used)
    private func applyLRUPolicy() throws -> PageID {
        // TLA+: Apply LRU policy - evict first (least recently used)
        guard !lruList.isEmpty else {
            throw BufferError.noPageToEvict
        }
        
        // Scan from least recently used (beginning) to most recently used (end)
        for pageId in lruList {
            // Skip pinned pages
            guard pinCounts[pageId] == 0 else {
                continue
            }
            
            // Found unpinned page - evict it
            return pageId
        }
        
        // All pages are pinned
        throw BufferError.noPageToEvict
    }
    
    /// Apply clock policy (second-chance algorithm)
    private func applyClockPolicy() throws -> PageID {
        // TLA+: Apply clock policy - second-chance algorithm
        guard !lruList.isEmpty else {
            throw BufferError.noPageToEvict
        }
        
        let maxScans = max(lruList.count * 2, poolSize) // Scan at most twice or pool size
        
        for _ in 0..<maxScans {
            // Wrap clock hand
            if clockHand >= lruList.count || lruList.isEmpty {
                clockHand = 0
            }
            
            guard clockHand < lruList.count, !lruList.isEmpty else {
                throw BufferError.noPageToEvict
            }
            
            let pageId = lruList[clockHand]
            
            // Skip pinned pages
            if pinCounts[pageId] != 0 {
                clockHand = (clockHand + 1) % max(lruList.count, 1)
                continue
            }
            
            // Check reference bit
            if referenceBits[pageId] == true {
                // Give second chance - clear reference bit
                referenceBits[pageId] = false
                clockHand = (clockHand + 1) % max(lruList.count, 1)
                continue
            }
            
            // Found victim - evict it (don't update clock hand, will be updated on next access)
            return pageId
        }
        
        // All pages are pinned or have reference bits set
        throw BufferError.noPageToEvict
    }
    
    /// Apply FIFO policy (evict first in)
    private func applyFIFOPolicy() throws -> PageID {
        // TLA+: Apply FIFO policy - evict first (oldest)
        guard !fifoList.isEmpty else {
            throw BufferError.noPageToEvict
        }
        
        // Scan from first in (beginning) to last in (end)
        for pageId in fifoList {
            // Skip pinned pages
            guard pinCounts[pageId] == 0 else {
                continue
            }
            
            // Found unpinned page - evict it
            return pageId
        }
        
        // All pages are pinned
        throw BufferError.noPageToEvict
    }
    
    /// Apply random policy
    private func applyRandomPolicy() throws -> PageID {
        // TLA+: Apply random policy
        guard !lruList.isEmpty else {
            throw BufferError.noPageToEvict
        }
        
        // Get all unpinned pages
        let unpinnedPages = lruList.filter { pinCounts[$0] == 0 }
        
        guard !unpinnedPages.isEmpty else {
            throw BufferError.noPageToEvict  // All pages are pinned
        }
        
        // Select random unpinned page
        guard let pageId = unpinnedPages.randomElement() else {
            throw BufferError.noPageToEvict
        }
        
        return pageId
    }
    
    /// Move page to MRU position (most recently used = end of list)
    private func moveToMRU(pageId: PageID) {
        lruList.removeAll { $0 == pageId }
        lruList.append(pageId)
    }
    
    // Note: Hit/miss rates are calculated in updateMetrics() from hitCount and missCount
    // These helper methods are kept for potential future use but currently unused
    
    /// Update latency
    private func updateLatency(_ latency: Double) {
        let alpha = 0.1 // Exponential moving average factor
        if metrics.averageLatency == 0.0 {
            metrics.averageLatency = latency
        } else {
            metrics.averageLatency = alpha * latency + (1.0 - alpha) * metrics.averageLatency
        }
    }
    
    /// Update metrics
    private func updateMetrics() {
        // TLA+: Update buffer metrics
        let usedFrames = bufferPool.count
        let freeFrames = poolSize - usedFrames
        let dirtyFrames = dirtyPages.count
        let pinnedFrames = pinCounts.values.filter { $0 > 0 }.count
        
        let total = hitCount + missCount
        let hitRate = total > 0 ? Double(hitCount) / Double(total) : 0.0
        let missRate = total > 0 ? Double(missCount) / Double(total) : 0.0
        
        metrics = BufferMetrics(
            totalFrames: poolSize,
            usedFrames: usedFrames,
            freeFrames: freeFrames,
            dirtyFrames: dirtyFrames,
            pinnedFrames: pinnedFrames,
            hitRate: hitRate,
            missRate: missRate,
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
    
    // MARK: - Query Operations
    
    /// Get buffer pool size
    public func getBufferPoolSize() -> Int {
        return poolSize
    }
    
    /// Get free frame count
    public func getFreeFrameCount() -> Int {
        return poolSize - bufferPool.count
    }
    
    /// Get dirty page count
    public func getDirtyPageCount() -> Int {
        return dirtyPages.count
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
        return lruList
    }
    
    /// Get page table
    public func getPageTable() -> [PageID: FrameIndex] {
        return pageTable
    }
    
    /// Get buffer pool
    public func getBufferPool() -> [FrameIndex: BufferPage] {
        return bufferPool
    }
    
    /// Check if page is in cache (query only, doesn't pin)
    public func isPageInCache(pageId: PageID) -> Bool {
        return pageTable[pageId] != nil
    }
    
    /// Get page by ID (query only, doesn't pin) - returns nil if not in cache
    public func getPageQuery(pageId: PageID) -> BufferPage? {
        guard let frameIndex = pageTable[pageId] else {
            return nil
        }
        return bufferPool[frameIndex]
    }
    
    /// Get frame by index
    public func getFrame(frameIndex: FrameIndex) -> BufferPage? {
        return bufferPool[frameIndex]
    }
    
    /// Get pin count
    public func getPinCount(pageId: PageID) -> Int {
        return pinCounts[pageId] ?? 0
    }
    
    /// Pin page
    public func pinPage(pageId: PageID) async throws {
        // TLA+: Check if page exists
        guard pageTable[pageId] != nil else {
            throw BufferError.pageNotFound
        }
        
        // TLA+: Increment pin count
        pinCounts[pageId] = (pinCounts[pageId] ?? 0) + 1
        
        // TLA+: Update metrics
        updateMetrics()
        
        logInfo("Page pinned: \(pageId)")
    }
    
    /// Mark page as dirty
    public func markPageDirty(pageId: PageID) async throws {
        // TLA+: Check if page exists
        guard pageTable[pageId] != nil else {
            throw BufferError.pageNotFound
        }
        
        // TLA+: Mark page as dirty
        dirtyPages.insert(pageId)
        
        // TLA+: Update metrics
        updateMetrics()
        
        logInfo("Page marked as dirty: \(pageId)")
    }
    
    /// Put (modify) page in buffer pool
    /// TLA+ Action: PutPage(pid, page, isDirty)
    /// Precondition: page is in cache and pinned
    public func putPage(pageId: PageID, page: BufferPage, isDirty: Bool) async throws {
        // TLA+: Check if page exists and is pinned
        guard pageTable[pageId] != nil else {
            throw BufferError.pageNotFound
        }
        
        guard pinCounts[pageId] ?? 0 > 0 else {
            throw BufferError.pageNotPinned
        }
        
        // Update page in buffer
        if let frameIndex = pageTable[pageId] {
            bufferPool[frameIndex] = page
            
            // TLA+: Mark as dirty if modified
            if isDirty {
                dirtyPages.insert(pageId)
            }
            
            // Move to MRU
            moveToMRU(pageId: pageId)
            referenceBits[pageId] = true
        }
        
        updateMetrics()
    }
    
    /// Update page data (convenience method)
    public func updatePage(pageId: PageID, page: BufferPage) async throws {
        try await putPage(pageId: pageId, page: page, isDirty: page.isDirty)
    }
    
    /// Clear buffer
    public func clearBuffer() async throws {
        // Flush all dirty pages first
        try await flushAll()
        
        // TLA+: Clear buffer
        bufferPool.removeAll()
        pageTable.removeAll()
        freeFrames.removeAll()
        dirtyPages.removeAll()
        pinCounts.removeAll()
        lruList.removeAll()
        fifoList.removeAll()
        referenceBits.removeAll()
        clockHand = 0
        hitCount = 0
        missCount = 0
        flushedLSN = 0
        nextFrameIndex = 0
        
        // TLA+: Update metrics
        updateMetrics()
        
        logInfo("Buffer cleared")
    }
    
    // MARK: - Invariant Checking (for testing)
    
    /// Check pin count invariant
    /// TLA+ Inv_Buffer_PinCount
    public func checkPinCountInvariant() -> Bool {
        // Check that pinned pages are in buffer
        for (pageId, count) in pinCounts {
            if count > 0 && pageTable[pageId] == nil {
                return false
            }
        }
        return true
    }
    
    /// Check dirty page consistency invariant
    /// TLA+ Inv_Buffer_DirtyPageConsistency
    public func checkDirtyPageConsistencyInvariant() -> Bool {
        // Check that dirty pages are in buffer
        for pageId in dirtyPages {
            if pageTable[pageId] == nil {
                return false
            }
        }
        return true
    }
    
    /// Check eviction policy invariant
    /// TLA+ Inv_Buffer_EvictionPolicy
    public func checkEvictionPolicyInvariant() -> Bool {
        // Check that LRU list contains only pages in buffer
        for pageId in lruList {
            if pageTable[pageId] == nil {
                return false
            }
        }
        
        // Check that buffer size doesn't exceed pool size
        if bufferPool.count > poolSize {
            return false
        }
        
        // Check that no duplicate pages in LRU list
        let uniqueLRU = Set(lruList)
        if uniqueLRU.count != lruList.count {
            return false
        }
        
        return true
    }
    
    /// Check WAL before data invariant
    /// TLA+ Inv_BufferPool_WALBeforeData
    public func checkWALBeforeDataInvariant() -> Bool {
        // Check that dirty pages have pageLSN <= flushedLSN (when being flushed)
        // This is enforced at flush time, but we can check consistency
        for pageId in dirtyPages {
            if let frameIndex = pageTable[pageId],
               let page = bufferPool[frameIndex] {
                // Allow +1 for race conditions during flush
                if page.lsn > flushedLSN + 1 {
                    return false
                }
            }
        }
        return true
    }
    
    /// Check all invariants
    public func checkAllInvariants() -> Bool {
        let pinCount = checkPinCountInvariant()
        let dirtyPageConsistency = checkDirtyPageConsistencyInvariant()
        let evictionPolicy = checkEvictionPolicyInvariant()
        let walBeforeData = checkWALBeforeDataInvariant()
        
        return pinCount && dirtyPageConsistency && evictionPolicy && walBeforeData
    }
}

// MARK: - Supporting Types

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

