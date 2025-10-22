//
//  HeapTableManager.swift
//  ColibrìDB Heap Table Manager Implementation
//
//  Based on: spec/HeapTable.tla
//  Implements: Slotted page heap storage
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//
//  Key Properties:
//  - Slot Consistency: Slots are consistent
//  - Free Space Validity: Free space is valid
//  - Page Checksum: Page checksum is valid
//

import Foundation

// MARK: - Heap Table Types

/// Row
/// Corresponds to TLA+: Row
public typealias Row = [Value]

/// Page
/// Corresponds to TLA+: Page
public struct Page: Codable, Sendable, Equatable {
    public let pageId: PageID
    public let header: PageHeader
    public let slots: [PageSlot]
    public let data: Data
    public let lsn: LSN
    public let isDirty: Bool
    public let isPinned: Bool
    public let timestamp: UInt64
    
    public init(pageId: PageID, header: PageHeader, slots: [PageSlot], data: Data, lsn: LSN, isDirty: Bool, isPinned: Bool, timestamp: UInt64) {
        self.pageId = pageId
        self.header = header
        self.slots = slots
        self.data = data
        self.lsn = lsn
        self.isDirty = isDirty
        self.isPinned = isPinned
        self.timestamp = timestamp
    }
}

/// Page header
/// Corresponds to TLA+: PageHeader
public struct PageHeader: Codable, Sendable, Equatable {
    public let pageId: PageID
    public let slotCount: Int
    public let freeStart: Int
    public let freeEnd: Int
    public let checksum: UInt32
    public let timestamp: UInt64
    
    public init(pageId: PageID, slotCount: Int, freeStart: Int, freeEnd: Int, checksum: UInt32, timestamp: UInt64) {
        self.pageId = pageId
        self.slotCount = slotCount
        self.freeStart = freeStart
        self.freeEnd = freeEnd
        self.checksum = checksum
        self.timestamp = timestamp
    }
}

/// Page slot
/// Corresponds to TLA+: PageSlot
public struct PageSlot: Codable, Sendable, Equatable {
    public let offset: Int
    public let length: Int
    public let isTombstone: Bool
    public let timestamp: UInt64
    
    public init(offset: Int, length: Int, isTombstone: Bool, timestamp: UInt64) {
        self.offset = offset
        self.length = length
        self.isTombstone = isTombstone
        self.timestamp = timestamp
    }
}

// MARK: - Heap Table Manager

/// Heap Table Manager for database storage
/// Corresponds to TLA+ module: HeapTable.tla
public actor HeapTableManager {
    
    // MARK: - State Variables (TLA+ vars)
    
    /// Pages
    /// TLA+: pages \in [PageID -> Page]
    private var pages: [PageID: Page] = [:]
    
    /// Free list
    /// TLA+: freeList \in Set(PageID)
    private var freeList: Set<PageID> = []
    
    /// Allocated RIDs
    /// TLA+: allocatedRIDs \in Set(RID)
    private var allocatedRIDs: Set<RID> = []
    
    // MARK: - Dependencies
    
    /// Buffer pool manager
    private let bufferPoolManager: BufferPoolManager
    
    /// WAL manager
    private let walManager: WALManager
    
    // MARK: - Initialization
    
    public init(bufferPoolManager: BufferPoolManager, walManager: WALManager) {
        self.bufferPoolManager = bufferPoolManager
        self.walManager = walManager
        
        // TLA+ Init_Heap
        self.pages = [:]
        self.freeList = []
        self.allocatedRIDs = []
    }
    
    // MARK: - Core Operations
    
    /// Insert row
    /// TLA+ Action: InsertRow(rid, row)
    public func insertRow(rid: RID, row: Row) async throws {
        // TLA+: Check if RID is already allocated
        guard !allocatedRIDs.contains(rid) else {
            throw HeapTableManagerError.ridAlreadyAllocated
        }
        
        // TLA+: Find page with space
        let pageId = try await findPageWithSpace(rowSize: calculateRowSize(row))
        
        // TLA+: Get page
        guard var page = pages[pageId] else {
            throw HeapTableManagerError.pageNotFound
        }
        
        // TLA+: Calculate offset
        let offset = page.header.freeEnd - calculateRowSize(row)
        
        // TLA+: Create slot
        let slot = PageSlot(
            offset: offset,
            length: calculateRowSize(row),
            isTombstone: false,
            timestamp: UInt64(Date().timeIntervalSince1970 * 1000)
        )
        
        // TLA+: Update page
        var newSlots = page.slots
        newSlots.append(slot)
        
        let newHeader = PageHeader(
            pageId: pageId,
            slotCount: page.header.slotCount + 1,
            freeStart: page.header.freeStart,
            freeEnd: offset,
            checksum: calculatePageChecksum(page: page),
            timestamp: UInt64(Date().timeIntervalSince1970 * 1000)
        )
        
        let newPage = Page(
            pageId: pageId,
            header: newHeader,
            slots: newSlots,
            data: page.data,
            lsn: page.lsn,
            isDirty: true,
            isPinned: page.isPinned,
            timestamp: UInt64(Date().timeIntervalSince1970 * 1000)
        )
        
        pages[pageId] = newPage
        
        // TLA+: Add to allocated RIDs
        allocatedRIDs.insert(rid)
        
        // TLA+: Update free space tracking
        try await updateFreeSpaceTracking(pageId: pageId)
        
        print("Inserted row: \(rid)")
    }
    
    /// Delete row
    /// TLA+ Action: DeleteRow(rid)
    public func deleteRow(rid: RID) async throws {
        // TLA+: Check if RID is allocated
        guard allocatedRIDs.contains(rid) else {
            throw HeapTableManagerError.ridNotAllocated
        }
        
        // TLA+: Find page containing RID
        guard let pageId = findPageContainingRID(rid: rid) else {
            throw HeapTableManagerError.ridNotFound
        }
        
        // TLA+: Get page
        guard var page = pages[pageId] else {
            throw HeapTableManagerError.pageNotFound
        }
        
        // TLA+: Find slot for RID
        guard let slotIndex = findSlotForRID(page: page, rid: rid) else {
            throw HeapTableManagerError.slotNotFound
        }
        
        // TLA+: Mark slot as tombstone
        var newSlots = page.slots
        newSlots[slotIndex] = PageSlot(
            offset: newSlots[slotIndex].offset,
            length: newSlots[slotIndex].length,
            isTombstone: true,
            timestamp: UInt64(Date().timeIntervalSince1970 * 1000)
        )
        
        let newPage = Page(
            pageId: pageId,
            header: page.header,
            slots: newSlots,
            data: page.data,
            lsn: page.lsn,
            isDirty: true,
            isPinned: page.isPinned,
            timestamp: UInt64(Date().timeIntervalSince1970 * 1000)
        )
        
        pages[pageId] = newPage
        
        // TLA+: Remove from allocated RIDs
        allocatedRIDs.remove(rid)
        
        // TLA+: Update free space tracking
        try await updateFreeSpaceTracking(pageId: pageId)
        
        print("Deleted row: \(rid)")
    }
    
    /// Read row
    /// TLA+ Action: ReadRow(rid)
    public func readRow(rid: RID) async throws -> Row? {
        // TLA+: Check if RID is allocated
        guard allocatedRIDs.contains(rid) else {
            return nil
        }
        
        // TLA+: Find page containing RID
        guard let pageId = findPageContainingRID(rid: rid) else {
            return nil
        }
        
        // TLA+: Get page
        guard let page = pages[pageId] else {
            return nil
        }
        
        // TLA+: Find slot for RID
        guard let slotIndex = findSlotForRID(page: page, rid: rid) else {
            return nil
        }
        
        let slot = page.slots[slotIndex]
        
        // TLA+: Check if slot is tombstone
        guard !slot.isTombstone else {
            return nil
        }
        
        // TLA+: Read row data
        let rowData = readRowData(page: page, slot: slot)
        let row = parseRowData(rowData)
        
        print("Read row: \(rid)")
        return row
    }
    
    /// Update row
    /// TLA+ Action: UpdateRow(rid, row)
    public func updateRow(rid: RID, row: Row) async throws {
        // TLA+: Check if RID is allocated
        guard allocatedRIDs.contains(rid) else {
            throw HeapTableManagerError.ridNotAllocated
        }
        
        // TLA+: Find page containing RID
        guard let pageId = findPageContainingRID(rid: rid) else {
            throw HeapTableManagerError.ridNotFound
        }
        
        // TLA+: Get page
        guard var page = pages[pageId] else {
            throw HeapTableManagerError.pageNotFound
        }
        
        // TLA+: Find slot for RID
        guard let slotIndex = findSlotForRID(page: page, rid: rid) else {
            throw HeapTableManagerError.slotNotFound
        }
        
        let slot = page.slots[slotIndex]
        
        // TLA+: Check if slot is tombstone
        guard !slot.isTombstone else {
            throw HeapTableManagerError.slotIsTombstone
        }
        
        // TLA+: Check if new row fits
        let newRowSize = calculateRowSize(row)
        if newRowSize > slot.length {
            // TLA+: Delete old row and insert new row
            try await deleteRow(rid: rid)
            try await insertRow(rid: rid, row: row)
            return
        }
        
        // TLA+: Update row data
        let newRowData = serializeRowData(row)
        let newPage = updateRowData(page: page, slot: slot, newRowData: newRowData)
        pages[pageId] = newPage
        
        print("Updated row: \(rid)")
    }
    
    // MARK: - Helper Methods
    
    /// Find page with space
    /// TLA+ Function: FindPageWithSpace(rowSize)
    private func findPageWithSpace(rowSize: Int) async throws -> PageID {
        // TLA+: Check free list
        for pageId in freeList {
            if let page = pages[pageId] {
                if hasFreeSpace(page: page, requiredSize: rowSize) {
                    return pageId
                }
            }
        }
        
        // TLA+: Create new page
        let newPageId = generateNewPageID()
        let newPage = createNewPage(pageId: newPageId)
        pages[newPageId] = newPage
        freeList.insert(newPageId)
        
        return newPageId
    }
    
    /// Check if page has free space
    /// TLA+ Function: HasFreeSpace(page, requiredSize)
    private func hasFreeSpace(page: Page, requiredSize: Int) -> Bool {
        let freeSpace = page.header.freeEnd - page.header.freeStart
        return freeSpace >= requiredSize
    }
    
    /// Calculate row size
    /// TLA+ Function: CalculateRowSize(row)
    private func calculateRowSize(_ row: Row) -> Int {
        return row.reduce(0) { $0 + $1.count }
    }
    
    /// Calculate page checksum
    /// TLA+ Function: CalculatePageChecksum(page)
    private func calculatePageChecksum(page: Page) -> UInt32 {
        // Simplified checksum calculation
        return UInt32(page.data.hashValue)
    }
    
    /// Find page containing RID
    /// TLA+ Function: FindPageContainingRID(rid)
    private func findPageContainingRID(rid: RID) -> PageID? {
        // This would require a more complex implementation to track RID to page mapping
        // For now, we'll search through all pages
        for (pageId, page) in pages {
            if findSlotForRID(page: page, rid: rid) != nil {
                return pageId
            }
        }
        return nil
    }
    
    /// Find slot for RID
    /// TLA+ Function: FindSlotForRID(page, rid)
    private func findSlotForRID(page: Page, rid: RID) -> Int? {
        // This would require a more complex implementation to track RID to slot mapping
        // For now, we'll return nil
        return nil
    }
    
    /// Read row data
    /// TLA+ Function: ReadRowData(page, slot)
    private func readRowData(page: Page, slot: PageSlot) -> Data {
        let startIndex = slot.offset
        let endIndex = slot.offset + slot.length
        return page.data.subdata(in: startIndex..<endIndex)
    }
    
    /// Parse row data
    /// TLA+ Function: ParseRowData(rowData)
    private func parseRowData(_ rowData: Data) -> Row {
        // Simplified parsing
        let string = String(data: rowData, encoding: .utf8) ?? ""
        return [string]
    }
    
    /// Serialize row data
    /// TLA+ Function: SerializeRowData(row)
    private func serializeRowData(_ row: Row) -> Data {
        // Simplified serialization
        let string = row.joined(separator: ",")
        return string.data(using: .utf8) ?? Data()
    }
    
    /// Update row data
    /// TLA+ Function: UpdateRowData(page, slot, newRowData)
    private func updateRowData(page: Page, slot: PageSlot, newRowData: Data) -> Page {
        var newData = page.data
        let startIndex = slot.offset
        let endIndex = slot.offset + slot.length
        
        if endIndex <= newData.count {
            newData.replaceSubrange(startIndex..<endIndex, with: newRowData)
        }
        
        return Page(
            pageId: page.pageId,
            header: page.header,
            slots: page.slots,
            data: newData,
            lsn: page.lsn,
            isDirty: true,
            isPinned: page.isPinned,
            timestamp: UInt64(Date().timeIntervalSince1970 * 1000)
        )
    }
    
    /// Generate new page ID
    /// TLA+ Function: GenerateNewPageID()
    private func generateNewPageID() -> PageID {
        return UInt64(pages.count + 1)
    }
    
    /// Create new page
    /// TLA+ Function: CreateNewPage(pageId)
    private func createNewPage(pageId: PageID) -> Page {
        let header = PageHeader(
            pageId: pageId,
            slotCount: 0,
            freeStart: 0,
            freeEnd: 4096, // Page size
            checksum: 0,
            timestamp: UInt64(Date().timeIntervalSince1970 * 1000)
        )
        
        return Page(
            pageId: pageId,
            header: header,
            slots: [],
            data: Data(count: 4096),
            lsn: 0,
            isDirty: false,
            isPinned: false,
            timestamp: UInt64(Date().timeIntervalSince1970 * 1000)
        )
    }
    
    /// Update free space tracking
    /// TLA+ Function: UpdateFreeSpaceTracking(pageId)
    private func updateFreeSpaceTracking(pageId: PageID) async throws {
        guard let page = pages[pageId] else {
            return
        }
        
        let freeSpace = page.header.freeEnd - page.header.freeStart
        
        if freeSpace > 0 {
            freeList.insert(pageId)
        } else {
            freeList.remove(pageId)
        }
    }
    
    /// Check if slots are non-overlapping
    /// TLA+ Function: SlotsNonOverlapping(page)
    private func slotsNonOverlapping(page: Page) -> Bool {
        let slots = page.slots.filter { !$0.isTombstone }
        
        for i in 0..<slots.count {
            for j in (i+1)..<slots.count {
                let slot1 = slots[i]
                let slot2 = slots[j]
                
                if (slot1.offset < slot2.offset + slot2.length) &&
                   (slot2.offset < slot1.offset + slot1.length) {
                    return false
                }
            }
        }
        
        return true
    }
    
    /// Check if page is valid
    /// TLA+ Function: ValidPage(page)
    private func validPage(page: Page) -> Bool {
        // Check basic page validity
        return page.header.pageId == page.pageId &&
               page.header.slotCount >= 0 &&
               page.header.freeStart >= 0 &&
               page.header.freeEnd >= page.header.freeStart &&
               page.header.freeEnd <= 4096 &&
               slotsNonOverlapping(page: page)
    }
    
    // MARK: - Query Operations
    
    /// Get page count
    public func getPageCount() -> Int {
        return pages.count
    }
    
    /// Get free page count
    public func getFreePageCount() -> Int {
        return freeList.count
    }
    
    /// Get allocated RID count
    public func getAllocatedRIDCount() -> Int {
        return allocatedRIDs.count
    }
    
    /// Get page
    public func getPage(pageId: PageID) -> Page? {
        return pages[pageId]
    }
    
    /// Get all pages
    public func getAllPages() -> [PageID: Page] {
        return pages
    }
    
    /// Get free pages
    public func getFreePages() -> Set<PageID> {
        return freeList
    }
    
    /// Get allocated RIDs
    public func getAllocatedRIDs() -> Set<RID> {
        return allocatedRIDs
    }
    
    /// Get page statistics
    public func getPageStatistics() -> [String: Any] {
        var totalSlots = 0
        var totalFreeSpace = 0
        var totalUsedSpace = 0
        
        for page in pages.values {
            totalSlots += page.header.slotCount
            totalFreeSpace += (page.header.freeEnd - page.header.freeStart)
            totalUsedSpace += (4096 - (page.header.freeEnd - page.header.freeStart))
        }
        
        return [
            "pageCount": pages.count,
            "freePageCount": freeList.count,
            "totalSlots": totalSlots,
            "totalFreeSpace": totalFreeSpace,
            "totalUsedSpace": totalUsedSpace,
            "allocatedRIDCount": allocatedRIDs.count
        ]
    }
    
    /// Clear heap table
    public func clearHeapTable() async throws {
        pages.removeAll()
        freeList.removeAll()
        allocatedRIDs.removeAll()
        
        print("Heap table cleared")
    }
    
    /// Reset heap table
    public func resetHeapTable() async throws {
        try await clearHeapTable()
        print("Heap table reset")
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
            if page.header.freeEnd < page.header.freeStart {
                return false
            }
            if page.header.freeEnd > 4096 {
                return false
            }
        }
        return true
    }
    
    /// Check page checksum invariant
    /// TLA+ Inv_HeapTable_PageChecksum
    public func checkPageChecksumInvariant() -> Bool {
        // Check that page checksums are valid
        for page in pages.values {
            let expectedChecksum = calculatePageChecksum(page: page)
            if page.header.checksum != expectedChecksum {
                return false
            }
        }
        return true
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

/// Buffer pool manager
public protocol BufferPoolManager: Sendable {
    func getPage(pageId: PageID) async throws -> Page
    func putPage(page: Page) async throws
    func pinPage(pageId: PageID) async throws
    func unpinPage(pageId: PageID) async throws
}

/// WAL manager
public protocol WALManager: Sendable {
    func appendRecord(txId: TxID, kind: String, data: Data) async throws -> LSN
    func flushLog() async throws
}

/// Heap table manager error
public enum HeapTableManagerError: Error, LocalizedError {
    case ridAlreadyAllocated
    case ridNotAllocated
    case ridNotFound
    case pageNotFound
    case slotNotFound
    case slotIsTombstone
    case insufficientSpace
    case invalidPage
    case invalidSlot
    case checksumMismatch
    case serializationFailed
    case deserializationFailed
    
    public var errorDescription: String? {
        switch self {
        case .ridAlreadyAllocated:
            return "RID is already allocated"
        case .ridNotAllocated:
            return "RID is not allocated"
        case .ridNotFound:
            return "RID not found"
        case .pageNotFound:
            return "Page not found"
        case .slotNotFound:
            return "Slot not found"
        case .slotIsTombstone:
            return "Slot is tombstone"
        case .insufficientSpace:
            return "Insufficient space"
        case .invalidPage:
            return "Invalid page"
        case .invalidSlot:
            return "Invalid slot"
        case .checksumMismatch:
            return "Checksum mismatch"
        case .serializationFailed:
            return "Serialization failed"
        case .deserializationFailed:
            return "Deserialization failed"
        }
    }
}