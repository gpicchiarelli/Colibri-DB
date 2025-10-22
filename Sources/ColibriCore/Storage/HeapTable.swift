//
//  HeapTable.swift
//  ColibrìDB Heap Table Implementation
//
//  Based on: spec/HeapTable.tla
//  Implements: Slotted page storage
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//
//  Key Properties:
//  - Slot Consistency: Slots non-overlapping and within page bounds
//  - Free Space Validity: Free space pointers consistent
//  - Page Checksum: All pages have valid checksums
//
//  Based on: Slotted page design from database literature
//

import Foundation

/// Heap Table for tuple storage using slotted pages
/// Corresponds to TLA+ module: HeapTable.tla
public actor HeapTable {
    // MARK: - State Variables (TLA+ vars)
    
    /// All pages in the heap table
    /// TLA+: pages \in [PageIds -> Page]
    private var pages: [PageID: Page] = [:]
    
    /// Set of page IDs with free space
    /// TLA+: freeList \subseteq PageIds
    private var freeList: Set<PageID> = []
    
    /// Set of allocated RIDs
    /// TLA+: allocatedRIDs \subseteq RID
    private var allocatedRIDs: Set<RID> = []
    
    // MARK: - Dependencies
    
    /// Buffer pool for page management
    private let bufferPool: BufferPool
    
    /// WAL for logging changes
    private let wal: FileWAL
    
    /// Next page ID to allocate
    private var nextPageID: PageID = 1
    
    // MARK: - Initialization
    
    public init(bufferPool: BufferPool, wal: FileWAL) {
        self.bufferPool = bufferPool
        self.wal = wal
        
        // TLA+ Init_Heap
        self.pages = [:]
        self.freeList = []
        self.allocatedRIDs = []
        self.nextPageID = 1
    }
    
    // MARK: - Core Operations
    
    /// Insert a row into the heap table
    /// TLA+ Action: InsertRow(pid, row)
    /// Precondition: pid \in freeList /\ HasFreeSpace(page, rowSize)
    /// Postcondition: row inserted, RID assigned
    public func insert(_ row: Row, txID: TxID) async throws -> RID {
        // Serialize row to data
        let encoder = JSONEncoder()
        let rowData = try encoder.encode(row)
        let rowSize = rowData.count
        
        // Find a page with enough free space
        let pageID = try await findPageWithSpace(rowSize)
        
        // Get page from buffer pool (pins it)
        var page = try await bufferPool.getPage(pageID)
        
        defer {
            // Always unpin when done
            Task {
                try? await bufferPool.unpinPage(pageID)
            }
        }
        
        // TLA+: slotId == page.header.slotCount + 1
        let slotID = UInt32(page.slots.count)
        
        // TLA+: newSlot == [offset |-> page.header.freeEnd - rowSize, ...]
        let offset = UInt16(page.header.freeEnd) - UInt16(rowSize)
        let newSlot = PageSlot(offset: offset, length: UInt16(rowSize), tombstone: false)
        
        // TLA+: pages' = [pages EXCEPT ![pid].slots = Append(@, newSlot), ...]
        page.slots.append(newSlot)
        page.header.slotCount += 1
        page.header.freeEnd = offset
        
        // Copy data to page
        let startIdx = Int(offset)
        let endIdx = startIdx + rowSize
        page.data.replaceSubrange(startIdx..<endIdx, with: rowData)
        
        // Log the insert to WAL
        let lsn = try await wal.append(
            kind: .heapInsert,
            txID: txID,
            pageID: pageID,
            payload: rowData
        )
        
        // Update page LSN
        page.header.pageLSN = lsn
        try await wal.updatePageLSN(pageID, lsn: lsn)
        
        // Write page back (mark as dirty)
        try await bufferPool.putPage(pageID, page: page, isDirty: true)
        
        // TLA+: allocatedRIDs' = allocatedRIDs \union {rid}
        let rid = RID(pageID: pageID, slotID: slotID)
        allocatedRIDs.insert(rid)
        
        // Update free space tracking
        updateFreeSpaceTracking(pageID: pageID)
        
        return rid
    }
    
    /// Read a row from the heap table
    /// TLA+ Action: ReadRow(rid)
    /// Precondition: rid \in allocatedRIDs
    /// Postcondition: returns row data
    public func read(_ rid: RID) async throws -> Row {
        // TLA+: rid \in allocatedRIDs
        guard allocatedRIDs.contains(rid) else {
            throw DBError.notFound
        }
        
        // Get page from buffer pool
        let page = try await bufferPool.getPage(rid.pageID)
        
        defer {
            Task {
                try? await bufferPool.unpinPage(rid.pageID)
            }
        }
        
        // Check slot exists
        guard Int(rid.slotID) < page.slots.count else {
            throw DBError.notFound
        }
        
        let slot = page.slots[Int(rid.slotID)]
        
        // Check for tombstone
        guard !slot.tombstone else {
            throw DBError.notFound
        }
        
        // Extract data
        let startIdx = Int(slot.offset)
        let endIdx = startIdx + Int(slot.length)
        let rowData = page.data.subdata(in: startIdx..<endIdx)
        
        // Deserialize
        let decoder = JSONDecoder()
        let row = try decoder.decode(Row.self, from: rowData)
        
        return row
    }
    
    /// Update a row in the heap table
    /// TLA+ Action: UpdateRow(rid, newRow)
    /// Precondition: rid \in allocatedRIDs
    /// Postcondition: row updated (in-place or new slot)
    public func update(_ rid: RID, newRow: Row, txID: TxID) async throws {
        // TLA+: rid \in allocatedRIDs
        guard allocatedRIDs.contains(rid) else {
            throw DBError.notFound
        }
        
        // For simplicity, delete old and insert new
        // A real implementation would try in-place update first
        try await delete(rid, txID: txID)
        _ = try await insert(newRow, txID: txID)
    }
    
    /// Delete a row from the heap table
    /// TLA+ Action: DeleteRow(rid)
    /// Precondition: rid \in allocatedRIDs
    /// Postcondition: row marked deleted (tombstone)
    public func delete(_ rid: RID, txID: TxID) async throws {
        // TLA+: rid \in allocatedRIDs
        guard allocatedRIDs.contains(rid) else {
            throw DBError.notFound
        }
        
        // Get page from buffer pool
        var page = try await bufferPool.getPage(rid.pageID)
        
        defer {
            Task {
                try? await bufferPool.unpinPage(rid.pageID)
            }
        }
        
        // Check slot exists
        guard Int(rid.slotID) < page.slots.count else {
            throw DBError.notFound
        }
        
        // TLA+: pages' = [pages EXCEPT ![pid].slots[sid].tombstone = TRUE]
        page.slots[Int(rid.slotID)].tombstone = true
        
        // Log the delete to WAL
        let slot = page.slots[Int(rid.slotID)]
        let rowData = page.data.subdata(in: Int(slot.offset)..<Int(slot.offset + slot.length))
        
        let lsn = try await wal.append(
            kind: .heapDelete,
            txID: txID,
            pageID: rid.pageID,
            payload: rowData
        )
        
        // Update page LSN
        page.header.pageLSN = lsn
        try await wal.updatePageLSN(rid.pageID, lsn: lsn)
        
        // Write page back (mark as dirty)
        try await bufferPool.putPage(rid.pageID, page: page, isDirty: true)
        
        // TLA+: allocatedRIDs' = allocatedRIDs \ {rid}
        allocatedRIDs.remove(rid)
        
        // Update free space tracking
        updateFreeSpaceTracking(pageID: rid.pageID)
    }
    
    // MARK: - Helper Methods
    
    /// Find a page with enough free space
    /// TLA+: HasFreeSpace(page, rowSize)
    private func findPageWithSpace(_ requiredBytes: Int) async throws -> PageID {
        // Check existing pages in freeList
        for pageID in freeList {
            let page = try await bufferPool.getPage(pageID)
            defer { Task { try? await bufferPool.unpinPage(pageID) } }
            
            let freeSpace = Int(page.header.freeEnd - page.header.freeStart)
            if freeSpace >= requiredBytes {
                return pageID
            }
        }
        
        // Allocate new page
        let newPageID = nextPageID
        nextPageID += 1
        
        // Initialize empty page
        let page = Page(pageID: newPageID)
        pages[newPageID] = page
        freeList.insert(newPageID)
        
        return newPageID
    }
    
    /// Update free space tracking for a page
    private func updateFreeSpaceTracking(pageID: PageID) {
        Task {
            do {
                let page = try await bufferPool.getPage(pageID)
                defer { try? await bufferPool.unpinPage(pageID) }
                
                let freeSpace = Int(page.header.freeEnd - page.header.freeStart)
                
                if freeSpace > 0 {
                    freeList.insert(pageID)
                } else {
                    freeList.remove(pageID)
                }
            } catch {
                // Handle error silently for tracking
            }
        }
    }
    
    /// Check if page has free space
    /// TLA+: HasFreeSpace(page, rowSize)
    private func hasFreeSpace(_ page: Page, rowSize: Int) -> Bool {
        let freeSpace = Int(page.header.freeEnd - page.header.freeStart)
        return freeSpace >= rowSize
    }
    
    /// Check if slots are non-overlapping
    /// TLA+: SlotsNonOverlapping(slots)
    private func slotsNonOverlapping(_ slots: [PageSlot]) -> Bool {
        for i in 0..<slots.count {
            for j in (i+1)..<slots.count {
                let slot1 = slots[i]
                let slot2 = slots[j]
                
                // Check if slots overlap
                let slot1Start = Int(slot1.offset)
                let slot1End = slot1Start + Int(slot1.length)
                let slot2Start = Int(slot2.offset)
                let slot2End = slot2Start + Int(slot2.length)
                
                if slot1Start < slot2End && slot2Start < slot1End {
                    return false  // Overlapping slots
                }
            }
        }
        return true
    }
    
    // MARK: - Query Operations
    
    /// Get total number of allocated RIDs
    public func getAllocatedRIDCount() -> Int {
        return allocatedRIDs.count
    }
    
    /// Get number of pages with free space
    public func getFreePageCount() -> Int {
        return freeList.count
    }
    
    /// Get total number of pages
    public func getTotalPageCount() -> Int {
        return pages.count
    }
    
    /// Get next page ID
    public func getNextPageID() -> PageID {
        return nextPageID
    }
    
    // MARK: - Invariant Checking (for testing)
    
    /// Check slot consistency invariant
    /// TLA+ Inv_Heap_SlotConsistency
    public func checkSlotConsistencyInvariant() async -> Bool {
        for (pageID, _) in pages {
            do {
                let page = try await bufferPool.getPage(pageID)
                defer { try? await bufferPool.unpinPage(pageID) }
                
                if !slotsNonOverlapping(page.slots) {
                    return false
                }
            } catch {
                return false
            }
        }
        return true
    }
    
    /// Check free space validity invariant
    /// TLA+ Inv_Heap_FreeSpaceValid
    public func checkFreeSpaceValidityInvariant() async -> Bool {
        for (pageID, _) in pages {
            do {
                let page = try await bufferPool.getPage(pageID)
                defer { try? await bufferPool.unpinPage(pageID) }
                
                // Check free space pointers are valid
                if page.header.freeStart > page.header.freeEnd {
                    return false
                }
                
                if page.header.freeEnd > PAGE_SIZE {
                    return false
                }
            } catch {
                return false
            }
        }
        return true
    }
    
    /// Check page checksum invariant
    /// TLA+ Inv_Heap_PageChecksum
    public func checkPageChecksumInvariant() async -> Bool {
        for (pageID, _) in pages {
            do {
                let page = try await bufferPool.getPage(pageID)
                defer { try? await bufferPool.unpinPage(pageID) }
                
                // Check page validity
                if !page.header.isValid {
                    return false
                }
            } catch {
                return false
            }
        }
        return true
    }
    
    /// Check all invariants
    public func checkAllInvariants() async -> Bool {
        let slotConsistency = await checkSlotConsistencyInvariant()
        let freeSpaceValidity = await checkFreeSpaceValidityInvariant()
        let pageChecksum = await checkPageChecksumInvariant()
        
        return slotConsistency && freeSpaceValidity && pageChecksum
    }
}

