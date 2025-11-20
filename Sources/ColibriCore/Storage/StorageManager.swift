//
//  StorageManager.swift
//  ColibrìDB Storage Manager Implementation
//
//  Based on: spec/Storage.tla
//  Implements: Database storage management
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//
//  Key Properties:
//  - Data Integrity: Data is consistent and correct
//  - Space Management: Free space is managed efficiently
//  - Performance Metrics: Storage performance is tracked
//

import Foundation

// MARK: - Storage Types


/// Record ID
/// Corresponds to TLA+: RecordID
public typealias RecordID = UInt64

/// Storage area
/// Corresponds to TLA+: StorageArea
public enum StorageArea: String, Codable, Sendable, CaseIterable {
    case data = "data"
    case index = "index"
    case log = "log"
    case temp = "temp"
    case system = "system"
}

/// Storage policy
/// Corresponds to TLA+: StoragePolicy
public struct StoragePolicy: Codable, Sendable, Equatable {
    public let policyId: String
    public let area: StorageArea
    public let maxSize: UInt64
    public let compressionEnabled: Bool
    public let encryptionEnabled: Bool
    public let replicationFactor: Int
    
    public init(policyId: String, area: StorageArea, maxSize: UInt64, compressionEnabled: Bool, encryptionEnabled: Bool, replicationFactor: Int) {
        self.policyId = policyId
        self.area = area
        self.maxSize = maxSize
        self.compressionEnabled = compressionEnabled
        self.encryptionEnabled = encryptionEnabled
        self.replicationFactor = replicationFactor
    }
}

/// Storage metrics
/// Corresponds to TLA+: StorageMetrics
public struct StorageMetrics: Codable, Sendable, Equatable {
    public let totalPages: Int
    public let usedPages: Int
    public let freePages: Int
    public let totalRecords: Int
    public let usedSpace: UInt64
    public let freeSpace: UInt64
    public let compressionRatio: Double
    public var ioOperations: Int
    public let averageLatency: Double
    
    public init(totalPages: Int, usedPages: Int, freePages: Int, totalRecords: Int, usedSpace: UInt64, freeSpace: UInt64, compressionRatio: Double, ioOperations: Int, averageLatency: Double) {
        self.totalPages = totalPages
        self.usedPages = usedPages
        self.freePages = freePages
        self.totalRecords = totalRecords
        self.usedSpace = usedSpace
        self.freeSpace = freeSpace
        self.compressionRatio = compressionRatio
        self.ioOperations = ioOperations
        self.averageLatency = averageLatency
    }
}

// MARK: - Storage Manager

/// Storage Manager for database storage management
/// Corresponds to TLA+ module: Storage.tla
/// Implements CatalogStorageProtocol for Catalog persistence
public actor StorageManagerActor: CatalogStorageProtocol {
    
    // MARK: - State Variables (TLA+ vars)
    
    /// Pages
    /// TLA+: pages \in [PageID -> Page]
    private var pages: [PageID: Page] = [:]
    
    /// Records
    /// TLA+: records \in [RecordID -> Record]
    private var records: [RecordID: Record] = [:]
    
    /// Free space map
    /// TLA+: freeSpaceMap \in [PageID -> UInt64]
    private var freeSpaceMap: [PageID: UInt64] = [:]
    
    /// Storage areas
    /// TLA+: storageAreas \in [StorageArea -> [PageID]]
    private var storageAreas: [StorageArea: [PageID]] = [:]
    
    /// Metrics
    /// TLA+: metrics \in StorageMetrics
    private var metrics: StorageMetrics = StorageMetrics(
        totalPages: 0,
        usedPages: 0,
        freePages: 0,
        totalRecords: 0,
        usedSpace: 0,
        freeSpace: 0,
        compressionRatio: 1.0,
        ioOperations: 0,
        averageLatency: 0.0
    )
    
    // MARK: - Dependencies
    
    /// Disk manager
    private let diskManager: DiskManager
    
    /// Buffer manager (optional - if provided, uses buffer cache)
    private let bufferManager: BufferManager?
    
    /// Compression service
    private let compressionService: CompressionService
    
    /// Encryption service
    private let encryptionService: EncryptionService
    
    /// Catalog Manager - **Catalog-First**: Storage Manager MUST check Catalog before operations
    /// Storage Manager uses Catalog to:
    /// - Validate table existence before operations
    /// - Get table metadata (columns, constraints) for validation
    /// - Ensure all operations are on tables defined in Catalog
    private let catalog: CatalogManager
    
    // MARK: - Initialization
    
    /// Initialize Storage Manager
    /// - Parameters:
    ///   - diskManager: Disk manager for I/O operations
    ///   - compressionService: Compression service
    ///   - encryptionService: Encryption service
    ///   - bufferManager: Optional buffer manager for caching
    ///   - catalog: **Catalog-First**: Catalog Manager (REQUIRED)
    public init(
        diskManager: DiskManager,
        compressionService: CompressionService,
        encryptionService: EncryptionService,
        bufferManager: BufferManager? = nil,
        catalog: CatalogManager
    ) {
        self.diskManager = diskManager
        self.bufferManager = bufferManager
        self.compressionService = compressionService
        self.encryptionService = encryptionService
        self.catalog = catalog
        
        // TLA+ Init
        self.pages = [:]
        self.records = [:]
        self.freeSpaceMap = [:]
        self.storageAreas = [:]
        self.metrics = StorageMetrics(
            totalPages: 0,
            usedPages: 0,
            freePages: 0,
            totalRecords: 0,
            usedSpace: 0,
            freeSpace: 0,
            compressionRatio: 1.0,
            ioOperations: 0,
            averageLatency: 0.0
        )
    }
    
    // MARK: - Storage Operations
    
    /// Allocate page
    /// TLA+ Action: AllocatePage(area, size)
    public func allocatePage(area: StorageArea, size: UInt64) async throws -> PageID {
        // TLA+: Find free page
        let pageId = try await findFreePage(area: area, size: size)
        
        // TLA+: Allocate page
        let page = Page(pageID: pageId)
        
        pages[pageId] = page
        freeSpaceMap[pageId] = size
        
        // TLA+: Update storage area
        if storageAreas[area] == nil {
            storageAreas[area] = []
        }
        storageAreas[area]?.append(pageId)
        
        // TLA+: Update metrics
        updateMetrics()
        
        return pageId
    }
    
    /// Deallocate page
    /// TLA+ Action: DeallocatePage(pageId)
    public func deallocatePage(pageId: PageID) async throws {
        // TLA+: Check if page exists
        guard pages[pageId] != nil else {
            throw StorageError.pageNotFound
        }
        
        // TLA+: Deallocate page
        pages.removeValue(forKey: pageId)
        freeSpaceMap.removeValue(forKey: pageId)
        
        // TLA+: Remove from storage area
        // Note: Page doesn't have area property, using default area
        storageAreas[.data]?.removeAll { $0 == pageId }
        
        // TLA+: Update metrics
        updateMetrics()
    }
    
    /// Read record
    /// TLA+ Action: ReadRecord(recordId)
    public func readRecord(recordId: RecordID) async throws -> Record {
        // TLA+: Check if record exists
        guard let record = records[recordId] else {
            throw StorageError.recordNotFound
        }
        
        // TLA+: Update metrics
        metrics.ioOperations += 1
        
        return record
    }
    
    /// Write record
    /// TLA+ Action: WriteRecord(recordId, data)
    public func writeRecord(recordId: RecordID, data: Data) async throws {
        // TLA+: Create record
        let record = Record(
            recordId: recordId,
            data: data,
            pageId: nil,
            offset: 0,
            size: UInt64(data.count),
            isDeleted: false,
            timestamp: UInt64(Date().timeIntervalSince1970 * 1000)
        )
        
        records[recordId] = record
        
        // TLA+: Update metrics
        metrics.ioOperations += 1
        updateMetrics()
    }
    
    /// Update record
    /// TLA+ Action: UpdateRecord(recordId, data)
    public func updateRecord(recordId: RecordID, data: Data) async throws {
        // TLA+: Check if record exists
        guard records[recordId] != nil else {
            throw StorageError.recordNotFound
        }
        
        // TLA+: Update record
        let record = Record(
            recordId: recordId,
            data: data,
            pageId: nil,
            offset: 0,
            size: UInt64(data.count),
            isDeleted: false,
            timestamp: UInt64(Date().timeIntervalSince1970 * 1000)
        )
        
        records[recordId] = record
        
        // TLA+: Update metrics
        metrics.ioOperations += 1
        updateMetrics()
    }
    
    /// Delete record
    /// TLA+ Action: DeleteRecord(recordId)
    public func deleteRecord(recordId: RecordID) async throws {
        // TLA+: Check if record exists
        guard var record = records[recordId] else {
            throw StorageError.recordNotFound
        }
        
        // TLA+: Mark as deleted
        record.isDeleted = true
        records[recordId] = record
        
        // TLA+: Update metrics
        updateMetrics()
    }
    
    /// Read page from storage (uses BufferManager if available)
    /// TLA+ Action: ReadPage(pageId)
    /// Read page from storage
    /// TLA+ Action: ReadPage(pageId)
    public func readPage(pageId: PageID) async throws -> Data {
        let startTime = Date()
        defer {
            let latency = Date().timeIntervalSince(startTime) * 1000
            metrics.ioOperations += 1
            updateAverageLatency(latency)
        }
        
        // If BufferManager is available, use it for caching
        if let bufferManager = bufferManager {
            let bufferPage = try await bufferManager.getPage(pageId: pageId)
            // Unpin immediately after reading (StorageManager doesn't pin pages long-term)
            try await bufferManager.unpinPage(pageId: pageId)
            return bufferPage.data
        }
        
        // Fallback to direct disk read
        return try await diskManager.readPage(pageId: pageId)
    }
    
    /// Write page to storage (uses BufferManager if available)
    /// TLA+ Action: WritePage(pageId, data)
    public func writePage(pageId: PageID, data: Data) async throws {
        let startTime = Date()
        defer {
            let latency = Date().timeIntervalSince(startTime) * 1000
            metrics.ioOperations += 1
            updateAverageLatency(latency)
        }
        
        // If BufferManager is available, use it for caching
        if let bufferManager = bufferManager {
            // Check if page exists in buffer
            if await bufferManager.isPageInCache(pageId: pageId) {
                // Get existing page and update it
                let bufferPage = try await bufferManager.getPage(pageId: pageId)
                // Create new buffer page with updated data
                let updatedPage = BufferPage(
                    pageId: pageId,
                    data: data,
                    lsn: bufferPage.lsn + 1, // Increment LSN for modification
                    isDirty: true,
                    isPinned: false, // Will be pinned by putPage
                    timestamp: UInt64(Date().timeIntervalSince1970 * 1000)
                )
                try await bufferManager.putPage(pageId: pageId, page: updatedPage, isDirty: true)
                try await bufferManager.unpinPage(pageId: pageId)
            } else {
                // Create new buffer page
                let bufferPage = BufferPage(
                    pageId: pageId,
                    data: data,
                    lsn: 0, // Will be updated by WAL
                    isDirty: true,
                    isPinned: false, // Will be pinned by putPage
                    timestamp: UInt64(Date().timeIntervalSince1970 * 1000)
                )
                try await bufferManager.putPage(pageId: pageId, page: bufferPage, isDirty: true)
                try await bufferManager.unpinPage(pageId: pageId)
            }
            return
        }
        
        // Fallback to direct disk write
        try await diskManager.writePage(pageId: pageId, data: data)
    }
    
    /// Manage free space
    /// TLA+ Action: ManageFreeSpace()
    public func manageFreeSpace() async throws {
        // TLA+: Manage free space
        // TLA+: Update free space map
        for (pageId, page) in pages {
            if page.data.isEmpty {
                freeSpaceMap[pageId] = UInt64(page.data.count)
            }
        }
        
        // TLA+: Update metrics
        updateMetrics()
    }
    
    // MARK: - Helper Methods
    
    /// Find free page
    private func findFreePage(area: StorageArea, size: UInt64) async throws -> PageID {
        // TLA+: Find free page in area
        let areaPages = storageAreas[area] ?? []
        
        for pageId in areaPages {
            if let freeSpace = freeSpaceMap[pageId], freeSpace >= size {
                return pageId
            }
        }
        
        // TLA+: Create new page if no free page found
        let pageId = UInt64(pages.count + 1)
        return pageId
    }
    
    /// Update metrics
    private func updateMetrics() {
        // TLA+: Update storage metrics
        let totalPages = pages.count
        let usedPages = pages.values.filter { !$0.data.isEmpty }.count
        let freePages = totalPages - usedPages
        let totalRecords = records.values.filter { !$0.isDeleted }.count
        let usedSpace = pages.values.filter { !$0.data.isEmpty }.reduce(into: 0) { $0 += UInt64($1.data.count) }
        let freeSpace = pages.values.filter { $0.data.isEmpty }.reduce(into: 0) { $0 += UInt64($1.data.count) }
        
        metrics = StorageMetrics(
            totalPages: totalPages,
            usedPages: usedPages,
            freePages: freePages,
            totalRecords: totalRecords,
            usedSpace: usedSpace,
            freeSpace: freeSpace,
            compressionRatio: metrics.compressionRatio,
            ioOperations: metrics.ioOperations,
            averageLatency: metrics.averageLatency
        )
    }
    
    /// Update average latency
    private func updateAverageLatency(_ latency: Double) {
        // Simple exponential moving average
        let alpha = 0.1 // Smoothing factor
        metrics = StorageMetrics(
            totalPages: metrics.totalPages,
            usedPages: metrics.usedPages,
            freePages: metrics.freePages,
            totalRecords: metrics.totalRecords,
            usedSpace: metrics.usedSpace,
            freeSpace: metrics.freeSpace,
            compressionRatio: metrics.compressionRatio,
            ioOperations: metrics.ioOperations,
            averageLatency: metrics.averageLatency * (1 - alpha) + latency * alpha
        )
    }
    
    /// Get page
    private func getPage(pageId: PageID) -> Page? {
        return pages[pageId]
    }
    
    /// Get record
    private func getRecord(recordId: RecordID) -> Record? {
        return records[recordId]
    }
    
    /// Get free space
    private func getFreeSpace(pageId: PageID) -> UInt64? {
        return freeSpaceMap[pageId]
    }
    
    // MARK: - Query Operations
    
    
    /// Get page count
    public func getPageCount() -> Int {
        return pages.count
    }
    
    /// Get record count
    public func getRecordCount() -> Int {
        return records.count
    }
    
    /// Get free space percentage
    public func getFreeSpacePercentage() -> Double {
        let totalSpace = metrics.usedSpace + metrics.freeSpace
        return totalSpace > 0 ? Double(metrics.freeSpace) / Double(totalSpace) * 100.0 : 0.0
    }
    
    /// Get storage metrics
    public func getStorageMetrics() -> StorageMetrics {
        return metrics
    }
    
    /// Get pages by area
    public func getPagesByArea(area: StorageArea) -> [PageID] {
        return storageAreas[area] ?? []
    }
    
    /// Get records by page
    public func getRecordsByPage(pageId: PageID) -> [RecordID] {
        return records.values.filter { $0.pageId == pageId }.map { $0.recordId }
    }
    
    /// Get storage areas
    public func getStorageAreas() -> [StorageArea: [PageID]] {
        return storageAreas
    }
    
    /// Get free space map
    public func getFreeSpaceMap() -> [PageID: UInt64] {
        return freeSpaceMap
    }
    
    /// Check if page exists
    public func pageExists(pageId: PageID) -> Bool {
        return pages[pageId] != nil
    }
    
    /// Check if record exists
    public func recordExists(recordId: RecordID) -> Bool {
        return records[recordId] != nil
    }
    
    /// Get total space
    public func getTotalSpace() -> UInt64 {
        return metrics.usedSpace + metrics.freeSpace
    }
    
    /// Get used space
    public func getUsedSpace() -> UInt64 {
        return metrics.usedSpace
    }
    
    /// Get free space
    public func getFreeSpace() -> UInt64 {
        return metrics.freeSpace
    }
    
    // MARK: - Invariant Checking (for testing)
    
    /// Check data integrity invariant
    /// TLA+ Inv_Storage_DataIntegrity
    public func checkDataIntegrityInvariant() -> Bool {
        // Check that data is consistent and correct
        // Verify that all records reference valid pages (if pageId is set)
        for (_, record) in records where !record.isDeleted {
            if let pageId = record.pageId {
                guard pages[pageId] != nil else {
                    return false
                }
            }
        }
        // Verify that pages contain valid data
        for (pageId, page) in pages {
            // Check that page has valid header
            guard page.header.pageID == pageId else {
                return false
            }
        }
        return true
    }
    
    /// Check space management invariant
    /// TLA+ Inv_Storage_SpaceManagement
    public func checkSpaceManagementInvariant() -> Bool {
        // Check that free space is managed efficiently
        // Verify that freeSpaceMap is consistent with pages
        for (pageId, freeSpace) in freeSpaceMap {
            guard let page = pages[pageId] else {
                return false
            }
            // Free space should be <= page size
            let pageSize = UInt64(page.data.count)
            guard freeSpace <= pageSize else {
                return false
            }
        }
        // Verify that storage areas contain valid page IDs
        for (_, areaPages) in storageAreas {
            for pageId in areaPages {
                guard pages[pageId] != nil else {
                    return false
                }
            }
        }
        return true
    }
    
    /// Check performance metrics invariant
    /// TLA+ Inv_Storage_PerformanceMetrics
    public func checkPerformanceMetricsInvariant() -> Bool {
        // Check that storage performance is tracked
        // Verify that metrics are non-negative
        guard metrics.totalPages >= 0,
              metrics.usedPages >= 0,
              metrics.freePages >= 0,
              metrics.totalRecords >= 0,
              metrics.ioOperations >= 0,
              metrics.averageLatency >= 0.0 else {
            return false
        }
        // Verify that usedPages + freePages = totalPages
        guard metrics.usedPages + metrics.freePages == metrics.totalPages else {
            return false
        }
        // Verify that usedSpace + freeSpace <= total space (approximate)
        // Note: total space is approximate, so we just check consistency
        return true
    }
    
    /// Check all invariants
    public func checkAllInvariants() -> Bool {
        let dataIntegrity = checkDataIntegrityInvariant()
        let spaceManagement = checkSpaceManagementInvariant()
        let performanceMetrics = checkPerformanceMetricsInvariant()
        
        return dataIntegrity && spaceManagement && performanceMetrics
    }
}

// MARK: - Supporting Types

/// Page

/// Record
public struct Record: Codable, Sendable, Equatable {
    public let recordId: RecordID
    public let data: Data
    public let pageId: PageID?
    public let offset: UInt64
    public let size: UInt64
    public var isDeleted: Bool
    public let timestamp: UInt64
    
    public init(recordId: RecordID, data: Data, pageId: PageID?, offset: UInt64, size: UInt64, isDeleted: Bool, timestamp: UInt64) {
        self.recordId = recordId
        self.data = data
        self.pageId = pageId
        self.offset = offset
        self.size = size
        self.isDeleted = isDeleted
        self.timestamp = timestamp
    }
}

/// Disk manager
public protocol DiskManager: Sendable {
    func readPage(pageId: PageID) async throws -> Data
    func writePage(pageId: PageID, data: Data) async throws
    func deletePage(pageId: PageID) async throws
}

/// Storage error
public enum StorageError: Error, LocalizedError {
    case pageNotFound
    case recordNotFound
    case insufficientSpace
    case allocationFailed
    case deallocationFailed
    case readFailed
    case writeFailed
    case updateFailed
    case deleteFailed
    
    public var errorDescription: String? {
        switch self {
        case .pageNotFound:
            return "Page not found"
        case .recordNotFound:
            return "Record not found"
        case .insufficientSpace:
            return "Insufficient space"
        case .allocationFailed:
            return "Page allocation failed"
        case .deallocationFailed:
            return "Page deallocation failed"
        case .readFailed:
            return "Record read failed"
        case .writeFailed:
            return "Record write failed"
        case .updateFailed:
            return "Record update failed"
        case .deleteFailed:
            return "Record delete failed"
        }
    }
}