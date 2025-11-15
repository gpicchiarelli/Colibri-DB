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
public struct HeapTableStatistics: Sendable {
    public let rowCount: Int64
    public let deadTuples: Int64
    public let pageCount: Int
    public let avgRowSize: Int
}

public actor HeapTable {
    // MARK: - State Variables
    
    private let bufferPool: BufferPool
    private let wal: FileWAL
    private let pageDirectory: PageDirectory
    private var nextPageID: PageID
    
    // MARK: - Initialization
    
    public init(
        bufferPool: BufferPool,
        wal: FileWAL,
        pageDirectory: PageDirectory
    ) async {
        self.bufferPool = bufferPool
        self.wal = wal
        self.pageDirectory = pageDirectory
        self.nextPageID = await pageDirectory.nextAvailablePageID()
    }
    
    // MARK: - Core Operations
    
    /// Insert a row into the heap table
    /// TLA+ Action: InsertRow(row)
    /// Precondition: row is valid
    /// Postcondition: row inserted, RID assigned
    public func insert(_ row: Row, txID: TxID) async throws -> RID {
        let encoder = JSONEncoder()
        let rowData = try encoder.encode(row)
        let pageID = try await pageWithSpace(for: Int(rowData.count) + MemoryLayout<PageSlot>.size)
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
        
        let lsn = try await wal.append(
            kind: .heapInsert,
            txID: txID,
            pageID: pageID,
            payload: rowData
        )
        page.header.pageLSN = lsn
        try await wal.updatePageLSN(pageID, lsn: lsn)
        try await refreshPageMetadata(pageID: pageID, page: &page, lsn: lsn)
        try await bufferPool.putPage(pageID, page: page, isDirty: true)
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
    public func update(_ rid: RID, newRow: Row, txID: TxID) async throws -> RID {
        let encoder = JSONEncoder()
        let newRowData = try encoder.encode(newRow)
        
        var page = try await bufferPool.getPage(rid.pageID)
        guard Int(rid.slotID) < page.slots.count else {
            try await bufferPool.unpinPage(rid.pageID)
            throw DBError.notFound
        }
        
        var slot = page.slots[Int(rid.slotID)]
        guard !slot.tombstone else {
            try await bufferPool.unpinPage(rid.pageID)
            throw DBError.notFound
        }
        
        let existingRowData = page.data.subdata(in: Int(slot.offset)..<Int(slot.offset + slot.length))
        if newRowData.count <= slot.length {
            let start = Int(slot.offset)
            let end = start + newRowData.count
            page.data.replaceSubrange(start..<end, with: newRowData)
            if newRowData.count < slot.length {
                let padding = [UInt8](repeating: 0, count: Int(slot.length) - newRowData.count)
                page.data.replaceSubrange(end..<start + Int(slot.length), with: padding)
            }
            slot.length = UInt16(newRowData.count)
            page.slots[Int(rid.slotID)] = slot
            
            let payload = HeapUpdateLogRecord(oldRowData: existingRowData, newRowData: newRowData)
            let lsn = try await wal.append(
                kind: .heapUpdate,
                txID: txID,
                pageID: rid.pageID,
                payload: try encoder.encode(payload)
            )
            page.header.pageLSN = lsn
            try await wal.updatePageLSN(rid.pageID, lsn: lsn)
            
            try await refreshPageMetadata(pageID: rid.pageID, page: &page, lsn: lsn)
            try await bufferPool.putPage(rid.pageID, page: page, isDirty: true)
            try await bufferPool.unpinPage(rid.pageID)
            return rid
        } else {
            try await bufferPool.unpinPage(rid.pageID)
            try await delete(rid, txID: txID)
            return try await insert(newRow, txID: txID)
        }
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
        
        let slot = page.slots[Int(rid.slotID)]
        let rowData = page.data.subdata(in: Int(slot.offset)..<Int(slot.offset + slot.length))
        let encoder = JSONEncoder()
        let payload = HeapDeleteLogRecord(oldRowData: rowData)
        let lsn = try await wal.append(
            kind: .heapDelete,
            txID: txID,
            pageID: rid.pageID,
            payload: try encoder.encode(payload)
        )
        page.header.pageLSN = lsn
        try await wal.updatePageLSN(rid.pageID, lsn: lsn)
        try await refreshPageMetadata(pageID: rid.pageID, page: &page, lsn: lsn)
        try await bufferPool.putPage(rid.pageID, page: page, isDirty: true)
        try await bufferPool.unpinPage(rid.pageID)
    }
    
    // MARK: - Helper Methods
    
    private func pageWithSpace(for requiredBytes: Int) async throws -> PageID {
        if let pageID = await pageDirectory.page(withFreeSpace: requiredBytes) {
            return pageID
        }
        return try await allocatePage()
    }
    
    /// Scan all rows from the heap table
    /// Returns all non-deleted rows
    public func scanAll() async throws -> [Row] {
        var allRows: [Row] = []
        let pageIDs = await pageDirectory.allPageIDs()
        
        for pageID in pageIDs {
            let page = try await bufferPool.getPage(pageID)
            for (slotIndex, slot) in page.slots.enumerated() where !slot.tombstone {
                let rid = RID(pageID: pageID, slotID: UInt32(slotIndex))
                if let row = try? await read(rid) {
                    allRows.append(row)
                }
            }
            try await bufferPool.unpinPage(pageID)
        }
        return allRows
    }
    
    /// Scan all rows with their RIDs
    public func scanAllWithRID() async throws -> [(RID, Row)] {
        var results: [(RID, Row)] = []
        let pageIDs = await pageDirectory.allPageIDs()
        
        for pageID in pageIDs {
            let page = try await bufferPool.getPage(pageID)
            for (slotIndex, slot) in page.slots.enumerated() where !slot.tombstone {
                let rid = RID(pageID: pageID, slotID: UInt32(slotIndex))
                if let row = try? await read(rid) {
                    results.append((rid, row))
                }
            }
            try await bufferPool.unpinPage(pageID)
        }
        return results
    }
    
    private func allocatePage() async throws -> PageID {
        let pageID = nextPageID
        nextPageID += 1
        var page = try await bufferPool.getPage(pageID)
        page.header = PageHeader(pageID: pageID)
        page.slots.removeAll(keepingCapacity: false)
        page.data = Data(count: PAGE_SIZE)
        page.header.checksum = pageChecksum(page)
        try await bufferPool.putPage(pageID, page: page, isDirty: true)
        try await bufferPool.unpinPage(pageID)
        try await pageDirectory.registerPage(
            pageID: pageID,
            freeBytes: computeFreeBytes(for: page),
            checksum: page.header.checksum,
            lsn: 0
        )
        return pageID
    }
    
    private func computeFreeBytes(for page: Page) -> Int {
        return Int(page.header.freeEnd) - Int(page.header.freeStart)
    }
    
    private func pageChecksum(_ page: Page) -> UInt32 {
        var checksum: UInt32 = 0
        page.data.withUnsafeBytes { buffer in
            for byte in buffer {
                checksum = checksum &+ UInt32(byte)
                checksum = (checksum << 5) | (checksum >> 27)
            }
        }
        return checksum
    }
    
    private func refreshPageMetadata(pageID: PageID, page: inout Page, lsn: LSN) async throws {
        let checksum = pageChecksum(page)
        page.header.checksum = checksum
        let freeBytes = computeFreeBytes(for: page)
        try await pageDirectory.updatePage(
            pageID: pageID,
            freeBytes: freeBytes,
            checksum: checksum,
            lsn: lsn
        )
    }
    
    private struct HeapUpdateLogRecord: Codable {
        let oldRowData: Data
        let newRowData: Data
    }
    
    private struct HeapDeleteLogRecord: Codable {
        let oldRowData: Data
    }
    
    public func collectStatistics() async throws -> HeapTableStatistics {
        let pageIDs = await pageDirectory.allPageIDs()
        var liveTuples: Int64 = 0
        var deadTuples: Int64 = 0
        var totalBytes: Int64 = 0
        
        for pageID in pageIDs {
            let page = try await bufferPool.getPage(pageID)
            for slot in page.slots {
                if slot.tombstone {
                    deadTuples += 1
                } else {
                    liveTuples += 1
                    totalBytes += Int64(slot.length)
                }
            }
            try await bufferPool.unpinPage(pageID)
        }
        
        let avgRowSize = liveTuples > 0 ? Int(totalBytes / liveTuples) : 0
        return HeapTableStatistics(
            rowCount: liveTuples,
            deadTuples: deadTuples,
            pageCount: pageIDs.count,
            avgRowSize: avgRowSize
        )
    }
}

