//
//  HeapTable.swift
//  ColibrìDB Heap Table Implementation
//
//  Based on: spec/HeapTable.tla
//  Implements: Slotted page storage
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//
//  Implements heap table storage with:
//  - Slotted page layout
//  - Insert/Read/Update/Delete operations
//  - Free space management
//  - Tombstone deletion
//

import Foundation

/// Heap Table for tuple storage using slotted pages
/// Corresponds to TLA+ module: HeapTable.tla
public actor HeapTable {
    // MARK: - State Variables
    
    /// Buffer pool for page management
    private let bufferPool: BufferPool
    
    /// WAL for logging changes
    private let wal: FileWAL
    
    /// Free space map: pageID -> free bytes
    private var freeSpaceMap: [PageID: Int] = [:]
    
    /// Next page ID to allocate
    private var nextPageID: PageID = 1
    
    // MARK: - Initialization
    
    public init(bufferPool: BufferPool, wal: FileWAL) {
        self.bufferPool = bufferPool
        self.wal = wal
        self.nextPageID = 1
    }
    
    // MARK: - Core Operations
    
    /// Insert a row into the heap table
    /// TLA+ Action: InsertRow(row)
    /// Precondition: row is valid
    /// Postcondition: row inserted, RID assigned
    public func insert(_ row: Row, txID: TxID) async throws -> RID {
        // Serialize row to data
        let encoder = JSONEncoder()
        let rowData = try encoder.encode(row)
        
        // Find a page with enough free space
        let pageID = try findPageWithSpace(Int(rowData.count))
        
        // Get page from buffer pool (pins it)
        var page = try await bufferPool.getPage(pageID)
        
        // Find free slot
        let slotID = UInt32(page.slots.count)
        
        // Allocate space in page
        let offset = page.header.freeStart
        let newFreeStart = offset + UInt16(rowData.count)
        
        guard newFreeStart <= page.header.freeEnd else {
            throw DBError.diskFull
        }
        
        // Update page
        page.header.freeStart = newFreeStart
        page.header.slotCount += 1
        
        // Add slot
        let slot = PageSlot(offset: offset, length: UInt16(rowData.count))
        page.slots.append(slot)
        
        // Copy data
        page.data.replaceSubrange(Int(offset)..<Int(newFreeStart), with: rowData)
        
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
        
        // Update free space map
        freeSpaceMap[pageID] = Int(page.header.freeEnd - page.header.freeStart)
        
        // Unpin page
        try await bufferPool.unpinPage(pageID)
        
        return RID(pageID: pageID, slotID: slotID)
    }
    
    /// Read a row from the heap table
    /// TLA+ Action: ReadRow(rid)
    /// Precondition: rid is valid
    /// Postcondition: returns row data
    public func read(_ rid: RID) async throws -> Row {
        // Get page from buffer pool
        let page = try await bufferPool.getPage(rid.pageID)
        
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
        
        // Unpin page
        try await bufferPool.unpinPage(rid.pageID)
        
        return row
    }
    
    /// Update a row in the heap table
    /// TLA+ Action: UpdateRow(rid, newRow)
    /// Precondition: rid exists
    /// Postcondition: row updated (in-place or new slot)
    public func update(_ rid: RID, newRow: Row, txID: TxID) async throws {
        // For simplicity, delete old and insert new
        // A real implementation would try in-place update first
        try await delete(rid, txID: txID)
        _ = try await insert(newRow, txID: txID)
    }
    
    /// Delete a row from the heap table
    /// TLA+ Action: DeleteRow(rid)
    /// Precondition: rid exists
    /// Postcondition: row marked deleted (tombstone)
    public func delete(_ rid: RID, txID: TxID) async throws {
        // Get page from buffer pool
        var page = try await bufferPool.getPage(rid.pageID)
        
        // Check slot exists
        guard Int(rid.slotID) < page.slots.count else {
            throw DBError.notFound
        }
        
        // Mark slot as tombstone
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
        
        // Unpin page
        try await bufferPool.unpinPage(rid.pageID)
    }
    
    // MARK: - Helper Methods
    
    /// Find a page with enough free space
    private func findPageWithSpace(_ requiredBytes: Int) throws -> PageID {
        // Check existing pages
        for (pageID, freeBytes) in freeSpaceMap {
            if freeBytes >= requiredBytes {
                return pageID
            }
        }
        
        // Allocate new page
        let newPageID = nextPageID
        nextPageID += 1
        
        // Initialize empty page
        let page = Page(pageID: newPageID)
        freeSpaceMap[newPageID] = PAGE_SIZE - MemoryLayout<PageHeader>.size
        
        return newPageID
    }
}

