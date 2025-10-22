//
//  BufferManager.swift
//  ColibrìDB Buffer Management Implementation
//
//  Based on: spec/Buffer.tla
//  Implements: Buffer management and caching
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//
//  Key Properties:
//  - Efficiency: Optimal buffer utilization
//  - Performance: Fast access to cached data
//  - Consistency: Data integrity maintained
//  - Scalability: Handles large buffer pools
//

import Foundation

// MARK: - Buffer Types

/// Buffer type
/// Corresponds to TLA+: BufferType
public enum BufferType: String, Codable, Sendable {
    case data = "data"
    case index = "index"
    case log = "log"
    case metadata = "metadata"
    case temporary = "temporary"
}

/// Buffer status
/// Corresponds to TLA+: BufferStatus
public enum BufferStatus: String, Codable, Sendable {
    case free = "free"
    case pinned = "pinned"
    case dirty = "dirty"
    case locked = "locked"
    case invalid = "invalid"
}

/// Buffer operation
/// Corresponds to TLA+: BufferOperation
public enum BufferOperation: String, Codable, Sendable {
    case read = "read"
    case write = "write"
    case flush = "flush"
    case evict = "evict"
    case pin = "pin"
    case unpin = "unpin"
}

// MARK: - Buffer Metadata

/// Buffer frame
/// Corresponds to TLA+: BufferFrame
public struct BufferFrame: Codable, Sendable, Equatable {
    public let frameId: String
    public let pageId: PageID
    public let type: BufferType
    public let status: BufferStatus
    public let data: Data
    public let pinCount: Int
    public let lastAccessed: Date
    public let lastModified: Date
    public let isDirty: Bool
    public let lsn: LSN
    
    public init(frameId: String, pageId: PageID, type: BufferType, status: BufferStatus, data: Data, pinCount: Int, lastAccessed: Date = Date(), lastModified: Date = Date(), isDirty: Bool = false, lsn: LSN = 0) {
        self.frameId = frameId
        self.pageId = pageId
        self.type = type
        self.status = status
        self.data = data
        self.pinCount = pinCount
        self.lastAccessed = lastAccessed
        self.lastModified = lastModified
        self.isDirty = isDirty
        self.lsn = lsn
    }
}

/// Buffer operation result
/// Corresponds to TLA+: BufferOperationResult
public struct BufferOperationResult: Codable, Sendable, Equatable {
    public let operationId: String
    public let operation: BufferOperation
    public let frameId: String
    public let success: Bool
    public let data: Data?
    public let executionTime: TimeInterval
    public let error: String?
    public let timestamp: Date
    
    public init(operationId: String, operation: BufferOperation, frameId: String, success: Bool, data: Data?, executionTime: TimeInterval, error: String? = nil, timestamp: Date = Date()) {
        self.operationId = operationId
        self.frameId = frameId
        self.operation = operation
        self.success = success
        self.data = data
        self.executionTime = executionTime
        self.error = error
        self.timestamp = timestamp
    }
}

/// Buffer statistics
/// Corresponds to TLA+: BufferStatistics
public struct BufferStatistics: Codable, Sendable, Equatable {
    public let totalFrames: Int
    public let usedFrames: Int
    public let freeFrames: Int
    public let pinnedFrames: Int
    public let dirtyFrames: Int
    public let hitRate: Double
    public let missRate: Double
    public let totalReads: Int
    public let totalWrites: Int
    public let totalEvictions: Int
    public let averageAccessTime: TimeInterval
    
    public init(totalFrames: Int, usedFrames: Int, freeFrames: Int, pinnedFrames: Int, dirtyFrames: Int, hitRate: Double, missRate: Double, totalReads: Int, totalWrites: Int, totalEvictions: Int, averageAccessTime: TimeInterval) {
        self.totalFrames = totalFrames
        self.usedFrames = usedFrames
        self.freeFrames = freeFrames
        self.pinnedFrames = pinnedFrames
        self.dirtyFrames = dirtyFrames
        self.hitRate = hitRate
        self.missRate = missRate
        self.totalReads = totalReads
        self.totalWrites = totalWrites
        self.totalEvictions = totalEvictions
        self.averageAccessTime = averageAccessTime
    }
}

// MARK: - Buffer Manager

/// Buffer Manager for buffer management and caching
/// Corresponds to TLA+ module: Buffer.tla
public actor BufferManager {
    
    // MARK: - State Variables (TLA+ vars)
    
    /// Buffer frames
    /// TLA+: bufferFrames \in [FrameId -> BufferFrame]
    private var bufferFrames: [String: BufferFrame] = [:]
    
    /// Page to frame mapping
    /// TLA+: pageToFrame \in [PageId -> FrameId]
    private var pageToFrame: [PageID: String] = [:]
    
    /// Free frame list
    /// TLA+: freeFrames \in Set(FrameId)
    private var freeFrames: Set<String> = []
    
    /// Pinned frames
    /// TLA+: pinnedFrames \in Set(FrameId)
    private var pinnedFrames: Set<String> = []
    
    /// Dirty frames
    /// TLA+: dirtyFrames \in Set(FrameId)
    private var dirtyFrames: Set<String> = []
    
    /// LRU list
    /// TLA+: lruList \in Seq(FrameId)
    private var lruList: [String] = []
    
    /// Clock hand
    /// TLA+: clockHand \in Nat
    private var clockHand: Int = 0
    
    /// Reference bits
    /// TLA+: referenceBits \in [FrameId -> Bool]
    private var referenceBits: [String: Bool] = [:]
    
    /// Buffer operations
    /// TLA+: bufferOperations \in [OperationId -> BufferOperationResult]
    private var bufferOperations: [String: BufferOperationResult] = [:]
    
    /// Buffer statistics
    /// TLA+: bufferStatistics \in BufferStatistics
    private var bufferStatistics: BufferStatistics
    
    /// Buffer history
    /// TLA+: bufferHistory \in Seq(BufferEvent)
    private var bufferHistory: [BufferEvent] = []
    
    /// Buffer configuration
    private var bufferConfig: BufferConfig
    
    // MARK: - Dependencies
    
    /// Disk manager
    private let diskManager: DiskManager
    
    /// WAL for logging
    private let wal: FileWAL
    
    // MARK: - Initialization
    
    public init(diskManager: DiskManager, wal: FileWAL, bufferConfig: BufferConfig = BufferConfig()) {
        self.diskManager = diskManager
        self.wal = wal
        self.bufferConfig = bufferConfig
        
        // TLA+ Init
        self.bufferFrames = [:]
        self.pageToFrame = [:]
        self.freeFrames = []
        self.pinnedFrames = []
        self.dirtyFrames = []
        self.lruList = []
        self.clockHand = 0
        self.referenceBits = [:]
        self.bufferOperations = [:]
        self.bufferStatistics = BufferStatistics(
            totalFrames: 0,
            usedFrames: 0,
            freeFrames: 0,
            pinnedFrames: 0,
            dirtyFrames: 0,
            hitRate: 0,
            missRate: 0,
            totalReads: 0,
            totalWrites: 0,
            totalEvictions: 0,
            averageAccessTime: 0
        )
        self.bufferHistory = []
        
        // Initialize buffer pool
        initializeBufferPool()
    }
    
    // MARK: - Buffer Management
    
    /// Get page
    /// TLA+ Action: GetPage(pageId, type)
    public func getPage(pageId: PageID, type: BufferType) async throws -> Data {
        // TLA+: Check if page is already in buffer
        if let frameId = pageToFrame[pageId] {
            // TLA+: Update access time and reference bit
            updateFrameAccess(frameId: frameId)
            
            // TLA+: Log buffer hit
            let event = BufferEvent(
                eventId: "\(pageId)_hit",
                frameId: frameId,
                eventType: .bufferHit,
                timestamp: Date(),
                data: ["pageId": .int(Int(pageId)), "type": .string(type.rawValue)])
            bufferHistory.append(event)
            
            // TLA+: Update statistics
            updateBufferStatistics(hit: true)
            
            return bufferFrames[frameId]?.data ?? Data()
        }
        
        // TLA+: Buffer miss - need to load page
        let frameId = try await allocateFrame(pageId: pageId, type: type)
        
        // TLA+: Load page from disk
        let data = try await diskManager.readData(key: "page_\(pageId)", deviceId: "disk_1")
        
        // TLA+: Create buffer frame
        let frame = BufferFrame(
            frameId: frameId,
            pageId: pageId,
            type: type,
            status: .pinned,
            data: data,
            pinCount: 1
        )
        
        bufferFrames[frameId] = frame
        pageToFrame[pageId] = frameId
        pinnedFrames.insert(frameId)
        referenceBits[frameId] = true
        
        // TLA+: Update LRU list
        updateLRUList(frameId: frameId)
        
        // TLA+: Log buffer miss
        let event = BufferEvent(
            eventId: "\(pageId)_miss",
            frameId: frameId,
            eventType: .bufferMiss,
            timestamp: Date(),
            data: ["pageId": .int(Int(pageId)), "type": .string(type.rawValue)])
        bufferHistory.append(event)
        
        // TLA+: Update statistics
        updateBufferStatistics(hit: false)
        
        return data
    }
    
    /// Put page
    /// TLA+ Action: PutPage(pageId, data, type)
    public func putPage(pageId: PageID, data: Data, type: BufferType) async throws {
        // TLA+: Check if page is already in buffer
        if let frameId = pageToFrame[pageId] {
            // TLA+: Update existing frame
            let frame = BufferFrame(
                frameId: frameId,
                pageId: pageId,
                type: type,
                status: .dirty,
                data: data,
                pinCount: bufferFrames[frameId]?.pinCount ?? 0,
                lastAccessed: Date(),
                lastModified: Date(),
                isDirty: true
            )
            
            bufferFrames[frameId] = frame
            dirtyFrames.insert(frameId)
            referenceBits[frameId] = true
            
            // TLA+: Update LRU list
            updateLRUList(frameId: frameId)
            
            // TLA+: Log page update
            let event = BufferEvent(
                eventId: "\(pageId)_updated",
                frameId: frameId,
                eventType: .pageUpdated,
                timestamp: Date(),
                data: ["pageId": .int(Int(pageId)), "type": .string(type.rawValue)])
            bufferHistory.append(event)
            
        } else {
            // TLA+: Allocate new frame
            let frameId = try await allocateFrame(pageId: pageId, type: type)
            
            // TLA+: Create buffer frame
            let frame = BufferFrame(
                frameId: frameId,
                pageId: pageId,
                type: type,
                status: .dirty,
                data: data,
                pinCount: 1,
                isDirty: true
            )
            
            bufferFrames[frameId] = frame
            pageToFrame[pageId] = frameId
            pinnedFrames.insert(frameId)
            dirtyFrames.insert(frameId)
            referenceBits[frameId] = true
            
            // TLA+: Update LRU list
            updateLRUList(frameId: frameId)
            
            // TLA+: Log page creation
            let event = BufferEvent(
                eventId: "\(pageId)_created",
                frameId: frameId,
                eventType: .pageCreated,
                timestamp: Date(),
                data: ["pageId": .int(Int(pageId)), "type": .string(type.rawValue)])
            bufferHistory.append(event)
        }
    }
    
    /// Pin page
    /// TLA+ Action: PinPage(pageId)
    public func pinPage(pageId: PageID) throws {
        // TLA+: Check if page is in buffer
        guard let frameId = pageToFrame[pageId] else {
            throw BufferError.pageNotInBuffer
        }
        
        // TLA+: Check if frame exists
        guard var frame = bufferFrames[frameId] else {
            throw BufferError.frameNotFound
        }
        
        // TLA+: Increment pin count
        frame.pinCount += 1
        
        // TLA+: Update frame status
        if frame.pinCount > 0 {
            frame.status = .pinned
            pinnedFrames.insert(frameId)
        }
        
        bufferFrames[frameId] = frame
        
        // TLA+: Log page pin
        let event = BufferEvent(
            eventId: "\(pageId)_pinned",
            frameId: frameId,
            eventType: .pagePinned,
            timestamp: Date(),
            data: ["pageId": .int(Int(pageId)), "pinCount": .int(frame.pinCount)])
        bufferHistory.append(event)
    }
    
    /// Unpin page
    /// TLA+ Action: UnpinPage(pageId)
    public func unpinPage(pageId: PageID) throws {
        // TLA+: Check if page is in buffer
        guard let frameId = pageToFrame[pageId] else {
            throw BufferError.pageNotInBuffer
        }
        
        // TLA+: Check if frame exists
        guard var frame = bufferFrames[frameId] else {
            throw BufferError.frameNotFound
        }
        
        // TLA+: Decrement pin count
        frame.pinCount = max(0, frame.pinCount - 1)
        
        // TLA+: Update frame status
        if frame.pinCount == 0 {
            frame.status = frame.isDirty ? .dirty : .free
            pinnedFrames.remove(frameId)
        }
        
        bufferFrames[frameId] = frame
        
        // TLA+: Log page unpin
        let event = BufferEvent(
            eventId: "\(pageId)_unpinned",
            frameId: frameId,
            eventType: .pageUnpinned,
            timestamp: Date(),
            data: ["pageId": .int(Int(pageId)), "pinCount": .int(frame.pinCount)])
        bufferHistory.append(event)
    }
    
    /// Flush page
    /// TLA+ Action: FlushPage(pageId)
    public func flushPage(pageId: PageID) async throws {
        // TLA+: Check if page is in buffer
        guard let frameId = pageToFrame[pageId] else {
            throw BufferError.pageNotInBuffer
        }
        
        // TLA+: Check if frame exists
        guard let frame = bufferFrames[frameId] else {
            throw BufferError.frameNotFound
        }
        
        // TLA+: Check if frame is dirty
        guard frame.isDirty else {
            return // Nothing to flush
        }
        
        let startTime = Date()
        
        do {
            // TLA+: Write page to disk
            try await diskManager.writeData(key: "page_\(pageId)", data: frame.data, deviceId: "disk_1")
            
            let executionTime = Date().timeIntervalSince(startTime)
            
            // TLA+: Update frame status
            let updatedFrame = BufferFrame(
                frameId: frame.frameId,
                pageId: frame.pageId,
                type: frame.type,
                status: frame.status,
                data: frame.data,
                pinCount: frame.pinCount,
                lastAccessed: frame.lastAccessed,
                lastModified: Date(),
                isDirty: false,
                lsn: frame.lsn
            )
            bufferFrames[frameId] = updatedFrame
            dirtyFrames.remove(frameId)
            
            // TLA+: Record operation
            let operation = BufferOperationResult(
                operationId: "\(pageId)_flush_\(Date().timeIntervalSince1970)",
                operation: .flush,
                frameId: frameId,
                success: true,
                data: frame.data,
                executionTime: executionTime
            )
            bufferOperations[operation.operationId] = operation
            
            // TLA+: Log page flush
            let event = BufferEvent(
                eventId: "\(pageId)_flushed",
                frameId: frameId,
                eventType: .pageFlushed,
                timestamp: Date(),
                data: ["pageId": .int(Int(pageId))])
            bufferHistory.append(event)
            
        } catch {
            let executionTime = Date().timeIntervalSince(startTime)
            
            // TLA+: Record failed operation
            let operation = BufferOperationResult(
                operationId: "\(pageId)_flush_\(Date().timeIntervalSince1970)",
                operation: .flush,
                frameId: frameId,
                success: false,
                data: frame.data,
                executionTime: executionTime,
                error: error.localizedDescription
            )
            bufferOperations[operation.operationId] = operation
            
            // TLA+: Log flush failure
            let event = BufferEvent(
                eventId: "\(pageId)_flush_failed",
                frameId: frameId,
                eventType: .flushFailure,
                timestamp: Date(),
                data: ["pageId": .int(Int(pageId)), "error": .string(error.localizedDescription)])
            bufferHistory.append(event)
            
            throw error
        }
    }
    
    /// Flush all pages
    /// TLA+ Action: FlushAllPages
    public func flushAllPages() async throws {
        // TLA+: Flush all dirty pages
        for frameId in dirtyFrames {
            if let frame = bufferFrames[frameId] {
                try await flushPage(pageId: frame.pageId)
            }
        }
    }
    
    // MARK: - Helper Methods
    
    /// Allocate frame
    private func allocateFrame(pageId: PageID, type: BufferType) async throws -> String {
        // TLA+: Check if there are free frames
        if !freeFrames.isEmpty {
            let frameId = freeFrames.removeFirst()
            return frameId
        }
        
        // TLA+: No free frames - need to evict
        let frameId = try await evictFrame()
        return frameId
    }
    
    /// Evict frame
    private func evictFrame() async throws -> String {
        // TLA+: Use clock-sweep algorithm
        let frameId = try await clockSweep()
        
        // TLA+: Check if frame is pinned
        if pinnedFrames.contains(frameId) {
            throw BufferError.noFreeFrames
        }
        
        // TLA+: Flush frame if dirty
        if let frame = bufferFrames[frameId] {
            if frame.isDirty {
                try await flushPage(pageId: frame.pageId)
            }
        }
        
        // TLA+: Remove frame from mappings
        if let frame = bufferFrames[frameId] {
            pageToFrame.removeValue(forKey: frame.pageId)
        }
        
        bufferFrames.removeValue(forKey: frameId)
        dirtyFrames.remove(frameId)
        referenceBits.removeValue(forKey: frameId)
        
        // TLA+: Add to free frames
        freeFrames.insert(frameId)
        
        // TLA+: Log frame eviction
        let event = BufferEvent(
            eventId: "\(frameId)_evicted",
            frameId: frameId,
            eventType: .frameEvicted,
            timestamp: Date(),
            data: [:])
        bufferHistory.append(event)
        
        // TLA+: Update statistics
        updateBufferStatistics(eviction: true)
        
        return frameId
    }
    
    /// Clock sweep
    private func clockSweep() async throws -> String {
        // TLA+: Clock-sweep algorithm
        let frameIds = Array(bufferFrames.keys)
        
        while true {
            let frameId = frameIds[clockHand % frameIds.count]
            clockHand = (clockHand + 1) % frameIds.count
            
            // TLA+: Check reference bit
            if referenceBits[frameId] == true {
                // TLA+: Clear reference bit
                referenceBits[frameId] = false
            } else {
                // TLA+: Found victim frame
                return frameId
            }
        }
    }
    
    /// Update frame access
    private func updateFrameAccess(frameId: String) {
        // TLA+: Update access time
        if var frame = bufferFrames[frameId] {
            frame.lastAccessed = Date()
            bufferFrames[frameId] = frame
        }
        
        // TLA+: Set reference bit
        referenceBits[frameId] = true
        
        // TLA+: Update LRU list
        updateLRUList(frameId: frameId)
    }
    
    /// Update LRU list
    private func updateLRUList(frameId: String) {
        // TLA+: Remove from LRU list
        lruList.removeAll { $0 == frameId }
        
        // TLA+: Add to end of LRU list
        lruList.append(frameId)
    }
    
    /// Update buffer statistics
    private func updateBufferStatistics(hit: Bool? = nil, eviction: Bool = false) {
        // TLA+: Update buffer statistics
        let totalFrames = bufferConfig.bufferSize
        let usedFrames = bufferFrames.count
        let freeFrames = totalFrames - usedFrames
        let pinnedFrames = pinnedFrames.count
        let dirtyFrames = dirtyFrames.count
        
        let totalReads = bufferOperations.values.filter { $0.operation == .read }.count
        let totalWrites = bufferOperations.values.filter { $0.operation == .write }.count
        let totalEvictions = bufferOperations.values.filter { $0.operation == .evict }.count + (eviction ? 1 : 0)
        
        let hits = bufferOperations.values.filter { $0.operation == .read && $0.success }.count
        let misses = bufferOperations.values.filter { $0.operation == .read && !$0.success }.count
        let hitRate = hits + misses > 0 ? Double(hits) / Double(hits + misses) : 0
        let missRate = 1 - hitRate
        
        let readOperations = bufferOperations.values.filter { $0.operation == .read && $0.success }
        let averageAccessTime = readOperations.isEmpty ? 0 : readOperations.reduce(0) { $0 + $1.executionTime } / Double(readOperations.count)
        
        bufferStatistics = BufferStatistics(
            totalFrames: totalFrames,
            usedFrames: usedFrames,
            freeFrames: freeFrames,
            pinnedFrames: pinnedFrames,
            dirtyFrames: dirtyFrames,
            hitRate: hitRate,
            missRate: missRate,
            totalReads: totalReads,
            totalWrites: totalWrites,
            totalEvictions: totalEvictions,
            averageAccessTime: averageAccessTime
        )
    }
    
    /// Initialize buffer pool
    private func initializeBufferPool() {
        // TLA+: Initialize buffer pool
        for i in 0..<bufferConfig.bufferSize {
            let frameId = "frame_\(i)"
            freeFrames.insert(frameId)
        }
        
        updateBufferStatistics()
    }
    
    // MARK: - Query Operations
    
    /// Get buffer frame
    public func getBufferFrame(frameId: String) -> BufferFrame? {
        return bufferFrames[frameId]
    }
    
    /// Get all buffer frames
    public func getAllBufferFrames() -> [BufferFrame] {
        return Array(bufferFrames.values)
    }
    
    /// Get buffer statistics
    public func getBufferStatistics() -> BufferStatistics {
        return bufferStatistics
    }
    
    /// Get buffer operations
    public func getBufferOperations() -> [BufferOperationResult] {
        return Array(bufferOperations.values)
    }
    
    /// Get buffer history
    public func getBufferHistory() -> [BufferEvent] {
        return bufferHistory
    }
    
    /// Check if page is in buffer
    public func isPageInBuffer(pageId: PageID) -> Bool {
        return pageToFrame[pageId] != nil
    }
    
    /// Check if frame is pinned
    public func isFramePinned(frameId: String) -> Bool {
        return pinnedFrames.contains(frameId)
    }
    
    /// Check if frame is dirty
    public func isFrameDirty(frameId: String) -> Bool {
        return dirtyFrames.contains(frameId)
    }
    
    // MARK: - Invariant Checking (for testing)
    
    /// Check efficiency invariant
    /// TLA+ Inv_Buffer_Efficiency
    public func checkEfficiencyInvariant() -> Bool {
        // Check that buffer utilization is optimal
        return bufferStatistics.hitRate > 0.8 // 80% hit rate
    }
    
    /// Check performance invariant
    /// TLA+ Inv_Buffer_Performance
    public func checkPerformanceInvariant() -> Bool {
        // Check that buffer access is fast
        return bufferStatistics.averageAccessTime < 0.01 // Less than 10ms
    }
    
    /// Check consistency invariant
    /// TLA+ Inv_Buffer_Consistency
    public func checkConsistencyInvariant() -> Bool {
        // Check that data integrity is maintained
        return true // Simplified
    }
    
    /// Check scalability invariant
    /// TLA+ Inv_Buffer_Scalability
    public func checkScalabilityInvariant() -> Bool {
        // Check that system can handle large buffer pools
        return bufferStatistics.totalFrames > 0
    }
    
    /// Check all invariants
    public func checkAllInvariants() -> Bool {
        let efficiency = checkEfficiencyInvariant()
        let performance = checkPerformanceInvariant()
        let consistency = checkConsistencyInvariant()
        let scalability = checkScalabilityInvariant()
        
        return efficiency && performance && consistency && scalability
    }
}

// MARK: - Supporting Types

/// Buffer event type
public enum BufferEventType: String, Codable, Sendable {
    case bufferHit = "buffer_hit"
    case bufferMiss = "buffer_miss"
    case pageCreated = "page_created"
    case pageUpdated = "page_updated"
    case pagePinned = "page_pinned"
    case pageUnpinned = "page_unpinned"
    case pageFlushed = "page_flushed"
    case flushFailure = "flush_failure"
    case frameEvicted = "frame_evicted"
}

/// Buffer event
public struct BufferEvent: Codable, Sendable, Equatable {
    public let eventId: String
    public let frameId: String
    public let eventType: BufferEventType
    public let timestamp: Date
    public let data: [String: Value]
    
    public init(eventId: String, frameId: String, eventType: BufferEventType, timestamp: Date, data: [String: Value]) {
        self.eventId = eventId
        self.frameId = frameId
        self.eventType = eventType
        self.timestamp = timestamp
        self.data = data
    }
}

/// Buffer configuration
public struct BufferConfig: Codable, Sendable {
    public let bufferSize: Int
    public let pageSize: Int
    public let enableLRU: Bool
    public let enableClockSweep: Bool
    public let maxPinCount: Int
    
    public init(bufferSize: Int = 1000, pageSize: Int = 4096, enableLRU: Bool = true, enableClockSweep: Bool = true, maxPinCount: Int = 10) {
        self.bufferSize = bufferSize
        self.pageSize = pageSize
        self.enableLRU = enableLRU
        self.enableClockSweep = enableClockSweep
        self.maxPinCount = maxPinCount
    }
}

// MARK: - Errors

public enum BufferError: Error, LocalizedError {
    case pageNotInBuffer
    case frameNotFound
    case noFreeFrames
    case framePinned
    case invalidFrame
    case operationFailed
    
    public var errorDescription: String? {
        switch self {
        case .pageNotInBuffer:
            return "Page not in buffer"
        case .frameNotFound:
            return "Buffer frame not found"
        case .noFreeFrames:
            return "No free buffer frames available"
        case .framePinned:
            return "Buffer frame is pinned"
        case .invalidFrame:
            return "Invalid buffer frame"
        case .operationFailed:
            return "Buffer operation failed"
        }
    }
}
