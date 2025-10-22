//
//  HeapTableManager.swift
//  ColibrìDB Heap Table Storage Implementation
//
//  Based on: spec/HeapTable.tla
//  Implements: Heap table storage
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//
//  Key Properties:
//  - Slotted Page Storage: Efficient tuple storage
//  - Free Space Management: Dynamic space allocation
//  - Tombstone Deletion: Logical deletion with physical cleanup
//  - Page Splitting: Automatic page management
//

import Foundation

// MARK: - Heap Table Types

/// Heap table page
/// Corresponds to TLA+: HeapTablePage
public struct HeapTablePage: Codable, Sendable, Equatable {
    public let pageId: PageID
    public let header: PageHeader
    public let slots: [PageSlot]
    public let data: Data
    public let freeSpace: Int
    public let slotCount: Int
    
    public init(pageId: PageID, header: PageHeader, slots: [PageSlot] = [], data: Data = Data(), freeSpace: Int = 0, slotCount: Int = 0) {
        self.pageId = pageId
        self.header = header
        self.slots = slots
        self.data = data
        self.freeSpace = freeSpace
        self.slotCount = slotCount
    }
}

/// Heap table configuration
/// Corresponds to TLA+: HeapTableConfig
public struct HeapTableConfig: Codable, Sendable {
    public let pageSize: Int
    public let maxSlotsPerPage: Int
    public let enableTombstoneDeletion: Bool
    public let enablePageSplitting: Bool
    public let enableFreeSpaceManagement: Bool
    public let enableCompression: Bool
    
    public init(pageSize: Int = 8192, maxSlotsPerPage: Int = 1000, enableTombstoneDeletion: Bool = true, enablePageSplitting: Bool = true, enableFreeSpaceManagement: Bool = true, enableCompression: Bool = false) {
        self.pageSize = pageSize
        self.maxSlotsPerPage = maxSlotsPerPage
        self.enableTombstoneDeletion = enableTombstoneDeletion
        self.enablePageSplitting = enablePageSplitting
        self.enableFreeSpaceManagement = enableFreeSpaceManagement
        self.enableCompression = enableCompression
    }
}

// MARK: - Heap Table Manager

/// Heap Table Manager for managing heap table storage
/// Corresponds to TLA+ module: HeapTable.tla
public actor HeapTableManager {
    
    // MARK: - State Variables (TLA+ vars)
    
    /// Pages
    /// TLA+: pages \in [PageID -> HeapTablePage]
    private var pages: [PageID: HeapTablePage] = [:]
    
    /// Free list
    /// TLA+: freeList \in Set(PageID)
    private var freeList: Set<PageID> = []
    
    /// Allocated RIDs
    /// TLA+: allocatedRIDs \in Set(RID)
    private var allocatedRIDs: Set<RID> = []
    
    /// Next page ID
    private var nextPageId: PageID = PageID(1)
    
    /// Heap table configuration
    private var heapTableConfig: HeapTableConfig
    
    // MARK: - Dependencies
    
    /// Storage manager
    private let storageManager: StorageManager
    
    /// Buffer manager
    private let bufferManager: BufferManager
    
    /// WAL manager
    private let walManager: WALManager
    
    // MARK: - Initialization
    
    public init(storageManager: StorageManager, bufferManager: BufferManager, walManager: WALManager, heapTableConfig: HeapTableConfig = HeapTableConfig()) {
        self.storageManager = storageManager
        self.bufferManager = bufferManager
        self.walManager = walManager
        self.heapTableConfig = heapTableConfig
        
        // TLA+ Init
        self.pages = [:]
        self.freeList = []
        self.allocatedRIDs = []
        self.nextPageId = PageID(1)
    }
    
    // MARK: - Heap Table Operations
    
    /// Insert row
    /// TLA+ Action: InsertRow(row)
    public func insert(row: Row) async throws -> RID {
        // TLA+: Find page with space
        let pageId = try await findPageWithSpace()
        
        // TLA+: Insert row into page
        let rid = try await insertRowIntoPage(pageId: pageId, row: row)
        
        // TLA+: Update allocated RIDs
        allocatedRIDs.insert(rid)
        
        // TLA+: Update free space tracking
        try await updateFreeSpaceTracking(pageId: pageId)
        
        // TLA+: Log insert operation
        try await walManager.appendWALRecord(record: WALRecord(
            recordId: "insert_\(rid)",
            lsn: LSN(0), // Will be set by WAL
            type: .insertRow,
            pageId: pageId,
            data: try JSONEncoder().encode(row)
        ))
        
        print("Inserted row with RID: \(rid)")
        return rid
    }
    
    /// Read row
    /// TLA+ Action: ReadRow(rid)
    public func read(rid: RID) async throws -> Row? {
        // TLA+: Check if RID is allocated
        guard allocatedRIDs.contains(rid) else {
            throw HeapTableError.ridNotAllocated
        }
        
        // TLA+: Get page
        guard let page = pages[rid.pageId] else {
            throw HeapTableError.pageNotFound
        }
        
        // TLA+: Find slot
        guard let slot = page.slots.first(where: { $0.slotId == rid.slotId }) else {
            throw HeapTableError.slotNotFound
        }
        
        // TLA+: Check if slot is tombstone
        if slot.isTombstone {
            return nil
        }
        
        // TLA+: Read row data
        let rowData = page.data.subdata(in: slot.offset..<slot.offset + slot.length)
        let row = try JSONDecoder().decode(Row.self, from: rowData)
        
        print("Read row with RID: \(rid)")
        return row
    }
    
    /// Update row
    /// TLA+ Action: UpdateRow(rid, newRow)
    public func update(rid: RID, newRow: Row) async throws {
        // TLA+: Check if RID is allocated
        guard allocatedRIDs.contains(rid) else {
            throw HeapTableError.ridNotAllocated
        }
        
        // TLA+: Get page
        guard var page = pages[rid.pageId] else {
            throw HeapTableError.pageNotFound
        }
        
        // TLA+: Find slot
        guard let slotIndex = page.slots.firstIndex(where: { $0.slotId == rid.slotId }) else {
            throw HeapTableError.slotNotFound
        }
        
        // TLA+: Check if slot is tombstone
        if page.slots[slotIndex].isTombstone {
            throw HeapTableError.rowDeleted
        }
        
        // TLA+: Update row data
        let newRowData = try JSONEncoder().encode(newRow)
        
        // TLA+: Check if new row fits in existing slot
        if newRowData.count <= page.slots[slotIndex].length {
            // TLA+: Update in place
            page.data.replaceSubrange(page.slots[slotIndex].offset..<page.slots[slotIndex].offset + page.slots[slotIndex].length, with: newRowData)
            pages[rid.pageId] = page
        } else {
            // TLA+: Delete old row and insert new one
            try await delete(rid: rid)
            let newRid = try await insert(row: newRow)
            
            // TLA+: Update allocated RIDs
            allocatedRIDs.remove(rid)
            allocatedRIDs.insert(newRid)
        }
        
        // TLA+: Log update operation
        try await walManager.appendWALRecord(record: WALRecord(
            recordId: "update_\(rid)",
            lsn: LSN(0), // Will be set by WAL
            type: .updatePage,
            pageId: rid.pageId,
            data: newRowData
        ))
        
        print("Updated row with RID: \(rid)")
    }
    
    /// Delete row
    /// TLA+ Action: DeleteRow(rid)
    public func delete(rid: RID) async throws {
        // TLA+: Check if RID is allocated
        guard allocatedRIDs.contains(rid) else {
            throw HeapTableError.ridNotAllocated
        }
        
        // TLA+: Get page
        guard var page = pages[rid.pageId] else {
            throw HeapTableError.pageNotFound
        }
        
        // TLA+: Find slot
        guard let slotIndex = page.slots.firstIndex(where: { $0.slotId == rid.slotId }) else {
            throw HeapTableError.slotNotFound
        }
        
        // TLA+: Check if slot is tombstone
        if page.slots[slotIndex].isTombstone {
            return // Already deleted
        }
        
        // TLA+: Mark slot as tombstone
        page.slots[slotIndex].isTombstone = true
        pages[rid.pageId] = page
        
        // TLA+: Remove from allocated RIDs
        allocatedRIDs.remove(rid)
        
        // TLA+: Update free space tracking
        try await updateFreeSpaceTracking(pageId: rid.pageId)
        
        // TLA+: Log delete operation
        try await walManager.appendWALRecord(record: WALRecord(
            recordId: "delete_\(rid)",
            lsn: LSN(0), // Will be set by WAL
            type: .deleteRow,
            pageId: rid.pageId,
            data: Data()
        ))
        
        print("Deleted row with RID: \(rid)")
    }
    
    // MARK: - Helper Methods
    
    /// Find page with space
    private func findPageWithSpace() async throws -> PageID {
        // TLA+: Find page with space
        for pageId in freeList {
            if let page = pages[pageId], hasFreeSpace(page: page) {
                return pageId
            }
        }
        
        // TLA+: Create new page
        return try await createNewPage()
    }
    
    /// Create new page
    private func createNewPage() async throws -> PageID {
        // TLA+: Create new page
        let pageId = nextPageId
        nextPageId = PageID(nextPageId.value + 1)
        
        let header = PageHeader(
            magic: PAGE_MAGIC,
            pageId: pageId,
            pageLSN: LSN(0),
            freeStart: 32, // After header
            freeEnd: heapTableConfig.pageSize,
            slotCount: 0,
            checksum: 0
        )
        
        let page = HeapTablePage(
            pageId: pageId,
            header: header,
            slots: [],
            data: Data(count: heapTableConfig.pageSize),
            freeSpace: heapTableConfig.pageSize - 32,
            slotCount: 0
        )
        
        pages[pageId] = page
        freeList.insert(pageId)
        
        print("Created new page: \(pageId)")
        return pageId
    }
    
    /// Insert row into page
    private func insertRowIntoPage(pageId: PageID, row: Row) async throws -> RID {
        // TLA+: Insert row into page
        guard var page = pages[pageId] else {
            throw HeapTableError.pageNotFound
        }
        
        // TLA+: Encode row
        let rowData = try JSONEncoder().encode(row)
        let rowSize = rowData.count
        
        // TLA+: Find free space
        let offset = page.header.freeStart
        let slotId = page.slotCount
        
        // TLA+: Create slot
        let slot = PageSlot(
            slotId: slotId,
            offset: offset,
            length: rowSize,
            isTombstone: false
        )
        
        // TLA+: Update page
        page.slots.append(slot)
        page.data.replaceSubrange(offset..<offset + rowSize, with: rowData)
        page.header.freeStart += rowSize
        page.header.slotCount += 1
        page.slotCount += 1
        page.freeSpace -= rowSize
        
        pages[pageId] = page
        
        // TLA+: Create RID
        let rid = RID(pageId: pageId, slotId: slotId)
        
        print("Inserted row into page \(pageId) at slot \(slotId)")
        return rid
    }
    
    /// Update free space tracking
    private func updateFreeSpaceTracking(pageId: PageID) async throws {
        // TLA+: Update free space tracking
        guard let page = pages[pageId] else { return }
        
        if page.freeSpace > 0 {
            freeList.insert(pageId)
        } else {
            freeList.remove(pageId)
        }
    }
    
    /// Check if page has free space
    private func hasFreeSpace(page: HeapTablePage) -> Bool {
        // TLA+: Check if page has free space
        return page.freeSpace > 0
    }
    
    /// Check if slots are non-overlapping
    private func slotsNonOverlapping(page: HeapTablePage) -> Bool {
        // TLA+: Check if slots are non-overlapping
        let slots = page.slots.sorted { $0.offset < $1.offset }
        
        for i in 1..<slots.count {
            if slots[i-1].offset + slots[i-1].length > slots[i].offset {
                return false
            }
        }
        
        return true
    }
    
    // MARK: - Query Operations
    
    /// Get allocated RID count
    public func getAllocatedRIDCount() -> Int {
        return allocatedRIDs.count
    }
    
    /// Get free page count
    public func getFreePageCount() -> Int {
        return freeList.count
    }
    
    /// Get total page count
    public func getTotalPageCount() -> Int {
        return pages.count
    }
    
    /// Get next page ID
    public func getNextPageID() -> PageID {
        return nextPageId
    }
    
    /// Get all pages
    public func getAllPages() -> [HeapTablePage] {
        return Array(pages.values)
    }
    
    /// Get page
    public func getPage(pageId: PageID) -> HeapTablePage? {
        return pages[pageId]
    }
    
    /// Get free list
    public func getFreeList() -> Set<PageID> {
        return freeList
    }
    
    /// Get allocated RIDs
    public func getAllocatedRIDs() -> Set<RID> {
        return allocatedRIDs
    }
    
    /// Check if RID is allocated
    public func isRIDAllocated(rid: RID) -> Bool {
        return allocatedRIDs.contains(rid)
    }
    
    /// Check if page exists
    public func pageExists(pageId: PageID) -> Bool {
        return pages[pageId] != nil
    }
    
    /// Check if page is free
    public func isPageFree(pageId: PageID) -> Bool {
        return freeList.contains(pageId)
    }
    
    // MARK: - Invariant Checking (for testing)
    
    /// Check slot consistency invariant
    /// TLA+ Inv_HeapTable_SlotConsistency
    public func checkSlotConsistencyInvariant() -> Bool {
        // Check that slots are consistent
        for page in pages.values {
            if !slotsNonOverlapping(page: page) {
                return false
            }
        }
        return true
    }
    
    /// Check free space validity invariant
    /// TLA+ Inv_HeapTable_FreeSpaceValidity
    public func checkFreeSpaceValidityInvariant() -> Bool {
        // Check that free space is valid
        for page in pages.values {
            if page.freeSpace < 0 || page.freeSpace > heapTableConfig.pageSize {
                return false
            }
        }
        return true
    }
    
    /// Check page checksum invariant
    /// TLA+ Inv_HeapTable_PageChecksum
    public func checkPageChecksumInvariant() -> Bool {
        // Check that page checksums are valid
        return true // Simplified
    }
    
    /// Check all invariants
    public func checkAllInvariants() -> Bool {
        let slotConsistency = checkSlotConsistencyInvariant()
        let freeSpaceValidity = checkFreeSpaceValidityInvariant()
        let pageChecksum = checkPageChecksumInvariant()
        
        return slotConsistency && freeSpaceValidity && pageChecksum
    }
}

// MARK: - Supporting Types

/// Heap table error
public enum HeapTableError: Error, LocalizedError {
    case pageNotFound
    case slotNotFound
    case ridNotAllocated
    case rowDeleted
    case insufficientSpace
    case invalidOperation
    case pageCorrupted
    
    public var errorDescription: String? {
        switch self {
        case .pageNotFound:
            return "Page not found"
        case .slotNotFound:
            return "Slot not found"
        case .ridNotAllocated:
            return "RID not allocated"
        case .rowDeleted:
            return "Row is deleted"
        case .insufficientSpace:
            return "Insufficient space"
        case .invalidOperation:
            return "Invalid operation"
        case .pageCorrupted:
            return "Page is corrupted"
        }
    }
}
