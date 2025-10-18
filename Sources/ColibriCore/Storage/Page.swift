//
//  Page.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Page anatomy detailing slots, headers, and byte math.

import Foundation
/// Fixed-size page with header, slot directory and JSON-encoded tuples (MVP).

// Simple 8KB page with slot directory and JSON-encoded rows.

/// Page header with metadata, free space pointers and checksum.
struct PageHeader {
    var magic: UInt32 = 0x434F4C49 // 'COLI'
    var pageId: UInt64
    var pageLSN: UInt64
    var freeStart: UInt16 // offset where free space starts (grows upward)
    var freeEnd: UInt16   // offset where free space ends (grows downward)
    var slotCount: UInt16
    var checksum: UInt32 // CRC32 of the whole page with this field zeroed
}

/// Slot metadata stored in the page slot directory (4 bytes).
struct PageSlot {
    private enum Flag {
        static let tombstoneMask: UInt16 = 0x8000
        static let lengthMask: UInt16 = 0x7FFF
    }

    var offset: UInt16
    private var rawLength: UInt16

    init(offset: UInt16, length: UInt16, tombstone: Bool = false) {
        self.offset = offset
        self.rawLength = length & Flag.lengthMask
        if tombstone { self.rawLength |= Flag.tombstoneMask }
    }

    var length: UInt16 {
        get { rawLength & Flag.lengthMask }
        set {
            rawLength = (rawLength & Flag.tombstoneMask) | (newValue & Flag.lengthMask)
        }
    }

    var isTombstone: Bool {
        get { (rawLength & Flag.tombstoneMask) != 0 }
        set {
            if newValue {
                rawLength |= Flag.tombstoneMask
            } else {
                rawLength &= Flag.lengthMask
            }
        }
    }
}

/// In-memory representation of a database page.
public struct Page {
    static let headerSize = 32
    static let slotSize = 4

    let pageSize: Int
    var header: PageHeader
    var data: Data // always pageSize bytes

    /// Initializes a fresh page with the given id and size.
    init(pageId: UInt64, pageSize: Int) {
        self.pageSize = pageSize
        let header = PageHeader(pageId: pageId,
                                pageLSN: 0,
                                freeStart: UInt16(Page.headerSize),
                                freeEnd: UInt16(pageSize),
                                slotCount: 0,
                                checksum: 0)
        self.header = header
        self.data = Data(repeating: 0, count: pageSize)
        writeHeader()
    }

    /// Initializes a page from raw bytes, validating magic and checksum.
    init?(from raw: Data, pageSize: Int) {
        guard raw.count == pageSize else { return nil }
        self.pageSize = pageSize
        self.data = raw
        guard let hdr = Page.readHeader(from: raw) else { return nil }
        // verify magic and checksum
        guard hdr.magic == 0x434F4C49 else { return nil }
        if !CRC32.verify(data: data, checksumOffset: 28) { return nil }
        self.header = hdr
    }

    /// Encodes header fields into `data` and updates the checksum.
    mutating func writeHeader() {
        // encode header fields
        data.withUnsafeMutableBytes { buf in
            var off = 0
            func put<T>(_ v: T) {
                var val = v
                let sz = MemoryLayout<T>.size
                withUnsafeBytes(of: &val) { src in
                    buf.baseAddress!.advanced(by: off).copyMemory(from: src.baseAddress!, byteCount: sz)
                }
                off += sz
            }
            put(header.magic)
            put(header.pageId)
            put(header.pageLSN)
            put(header.freeStart)
            put(header.freeEnd)
            put(header.slotCount)
            put(UInt16(0)) // padding to reach 28 bytes
            put(header.checksum)
        }
        // update checksum
        header.checksum = CRC32.computeWithZeroedChecksum(data: &data, checksumOffset: 28)
        data.withUnsafeMutableBytes { buf in
            var c = header.checksum
            withUnsafeBytes(of: &c) { src in
                buf.baseAddress!.advanced(by: 28).copyMemory(from: src.baseAddress!, byteCount: 4)
            }
        }
    }

    /// Sets the pageLSN used by WAL recovery.
    mutating func setPageLSN(_ lsn: UInt64) {
        header.pageLSN = lsn
    }

    /// Decodes a header from raw page data.
    static func readHeader(from data: Data) -> PageHeader? {
        var hdr = PageHeader(pageId: 0, pageLSN: 0, freeStart: 0, freeEnd: 0, slotCount: 0, checksum: 0)
        var off = 0
        func get<T>(_ t: T.Type) -> T {
            let sz = MemoryLayout<T>.size
            let val = data.withUnsafeBytes { ptr -> T in
                ptr.baseAddress!.advanced(by: off).assumingMemoryBound(to: T.self).pointee
            }
            off += sz
            return val
        }
        hdr.magic = get(UInt32.self)
        hdr.pageId = get(UInt64.self)
        hdr.pageLSN = get(UInt64.self)
        hdr.freeStart = get(UInt16.self)
        hdr.freeEnd = get(UInt16.self)
        hdr.slotCount = get(UInt16.self)
        _ = get(UInt16.self) // padding
        hdr.checksum = get(UInt32.self)
        return hdr
    }

    /// Returns contiguous free space available for a new tuple.
    func availableSpaceForInsert() -> Int {
        let free = Int(header.freeEnd) - Int(header.freeStart)
        return max(0, free - Page.slotSize)
    }

    /// Returns live/dead tuple counts and byte utilization statistics for the page.
    func fragmentationMetrics() -> (liveTuples: Int, deadTuples: Int, liveBytes: Int, deadBytes: Int, freeBytes: Int) {
        var liveTuples = 0
        var deadTuples = 0
        var liveBytes = 0
        if header.slotCount > 0 {
            for sid in 1...header.slotCount {
        let slotPos = pageSize - Int(sid) * Page.slotSize
        let slot: PageSlot = data.withUnsafeBytes { ptr in
            ptr.baseAddress!.advanced(by: slotPos).assumingMemoryBound(to: PageSlot.self).pointee
        }
                if slot.length == 0 || slot.isTombstone {
                    deadTuples += 1
                } else {
                    liveTuples += 1
                    liveBytes += Int(slot.length)
                }
            }
        }
        let dataRegionBytes = max(0, Int(header.freeStart) - Page.headerSize)
        let deadBytes = max(0, dataRegionBytes - liveBytes)
        let freeBytes = max(0, Int(header.freeEnd) - Int(header.freeStart))
        return (liveTuples, deadTuples, liveBytes, deadBytes, freeBytes)
    }

    /// Simulates an insert without modifying the page (for RID prediction).
    func simulateInsert(rowBytes: Data) -> UInt16? {
        let need = rowBytes.count
        guard need <= availableSpaceForInsert() else { return nil }
        return header.slotCount &+ 1
    }
    
    /// Inserts tuple bytes and returns allocated slot id, or nil if insufficient space.
    mutating func insert(rowBytes: Data) -> UInt16? {
        let need = rowBytes.count
        guard need <= availableSpaceForInsert() else { return nil }
        let slotId = header.slotCount &+ 1
        let offset = header.freeStart
        // write row bytes
        data.replaceSubrange(Int(offset)..<Int(offset) + need, with: rowBytes)
        // write slot
        let slotOffset = Int(header.freeEnd) - Page.slotSize
        var slot = PageSlot(offset: offset, length: UInt16(need), tombstone: false)
        withUnsafeBytes(of: &slot) { src in
            data.replaceSubrange(slotOffset..<slotOffset+Page.slotSize, with: src)
        }
        header.freeStart = UInt16(Int(header.freeStart) + need)
        header.freeEnd = UInt16(slotOffset)
        header.slotCount = slotId
        writeHeader()
        return slotId
    }

    /// Reads tuple bytes for a given slot id.
    func read(slotId: UInt16) -> Data? {
        guard slotId > 0 && slotId <= header.slotCount else { return nil }
        let slotPos = pageSize - Int(slotId) * Page.slotSize
        let slot: PageSlot = data.withUnsafeBytes { ptr in
            ptr.baseAddress!.advanced(by: slotPos).assumingMemoryBound(to: PageSlot.self).pointee
        }
        if slot.length == 0 || slot.isTombstone { return nil }
        let start = Int(slot.offset)
        let end = start + Int(slot.length)
        guard end <= pageSize else { return nil }
        return data.subdata(in: start..<end)
    }

    /// Returns true if the slot exists and has a non-zero length (live tuple).
    func isSlotLive(_ slotId: UInt16) -> Bool {
        guard slotId > 0 && slotId <= header.slotCount else { return false }
        let slotPos = pageSize - Int(slotId) * Page.slotSize
        let slot: PageSlot = data.withUnsafeBytes { ptr in
            ptr.baseAddress!.advanced(by: slotPos).assumingMemoryBound(to: PageSlot.self).pointee
        }
        return slot.length != 0
    }

    mutating func markTombstone(slotId: UInt16) {
        guard slotId > 0 && slotId <= header.slotCount else { return }
        let slotPos = pageSize - Int(slotId) * Page.slotSize
        var slot: PageSlot = data.withUnsafeBytes { ptr in
            ptr.baseAddress!.advanced(by: slotPos).assumingMemoryBound(to: PageSlot.self).pointee
        }
        slot.isTombstone = true
        withUnsafeBytes(of: slot) { src in
            data.replaceSubrange(slotPos..<slotPos+Page.slotSize, with: src)
        }
    }

    mutating func clearTombstone(slotId: UInt16) {
        guard slotId > 0 && slotId <= header.slotCount else { return }
        let slotPos = pageSize - Int(slotId) * Page.slotSize
        var slot: PageSlot = data.withUnsafeBytes { ptr in
            ptr.baseAddress!.advanced(by: slotPos).assumingMemoryBound(to: PageSlot.self).pointee
        }
        slot.isTombstone = false
        withUnsafeBytes(of: slot) { src in
            data.replaceSubrange(slotPos..<slotPos+Page.slotSize, with: src)
        }
    }

    // Compacts live tuples to the front of the page, preserving slot ids.
    // Returns reclaimed free space delta (after - before).
    /// Compacts the page, preserving slot ids; returns gained free bytes.
    /// Compacts page by removing fragmentation and reclaiming space from deleted tuples.
    /// Optimized for memory efficiency - reuses existing buffer where possible.
    /// - Returns: Number of bytes reclaimed (free space gained)
    mutating func compact() -> Int {
        let originalFree = availableSpaceForInsert()
        
        // Count live tuples first to pre-allocate efficiently
        var liveCount = 0
        var totalLiveSize = 0
        
        for sid in 1...header.slotCount {
            let slotPos = pageSize - Int(sid) * Page.slotSize
            let slot: PageSlot = data.withUnsafeBytes { ptr in
                ptr.baseAddress!.advanced(by: slotPos).assumingMemoryBound(to: PageSlot.self).pointee
            }
            if slot.length == 0 || slot.isTombstone { continue }
            liveCount += 1
            totalLiveSize += Int(slot.length)
        }
        
        // Early exit if no compaction needed
        guard liveCount > 0 else {
            header.freeStart = UInt16(Page.headerSize)
            writeHeader()
            return availableSpaceForInsert() - originalFree
        }
        
        // Collect live tuples with pre-allocated capacity (memory optimization)
        var tuples: [(slotId: UInt16, offset: UInt16, length: UInt16)] = []
        tuples.reserveCapacity(liveCount)  // Pre-allocate to avoid reallocations
        
        for sid in 1...header.slotCount {
            let slotPos = pageSize - Int(sid) * Page.slotSize
            let slot: PageSlot = data.withUnsafeBytes { ptr in
                ptr.baseAddress!.advanced(by: slotPos).assumingMemoryBound(to: PageSlot.self).pointee
            }
            if slot.length == 0 || slot.isTombstone { continue }
            
            let start = Int(slot.offset)
            let end = start + Int(slot.length)
            guard end <= pageSize else { continue }
            
            tuples.append((slotId: UInt16(sid), offset: slot.offset, length: slot.length))
        }
        
        // In-place compaction: shift tuples to be contiguous
        // This avoids creating a full page copy in most cases
        var currentOffset = Page.headerSize
        
        data.withUnsafeMutableBytes { ptr in
            guard let base = ptr.baseAddress else { return }
            
            // Sort tuples by original offset for efficient in-place movement
            let sortedTuples = tuples.sorted { $0.offset < $1.offset }
            
            for tuple in sortedTuples {
                let sourceStart = Int(tuple.offset)
                let length = Int(tuple.length)
                
                // Skip if already in the right place
                guard sourceStart != currentOffset else {
                    currentOffset += length
                    continue
                }
                
                // Move tuple data to new offset (memmove handles overlapping regions)
                let src = base.advanced(by: sourceStart)
                let dst = base.advanced(by: currentOffset)
                
                // Use memmove for safe overlapping copy
                memmove(dst, src, length)
                
                // Update slot directory entry
                let slotPos = pageSize - Int(tuple.slotId) * Page.slotSize
                var updatedSlot = PageSlot(offset: UInt16(currentOffset), length: tuple.length, tombstone: false)
                withUnsafeBytes(of: &updatedSlot) { slotBytes in
                    let slotDst = base.advanced(by: slotPos)
                    memcpy(slotDst, slotBytes.baseAddress!, Page.slotSize)
                }
                
                currentOffset += length
            }
            
            // Zero out freed space for security (optional, can be skipped for performance)
            if currentOffset < pageSize - Int(header.slotCount) * Page.slotSize {
                let freeStart = base.advanced(by: currentOffset)
                let freeLength = pageSize - Int(header.slotCount) * Page.slotSize - currentOffset
                memset(freeStart, 0, freeLength)
            }
        }
        
        // Update header free space pointers
        header.freeStart = UInt16(currentOffset)
        header.freeEnd = UInt16(pageSize - Int(header.slotCount) * Page.slotSize)
        writeHeader()
        
        let newFree = availableSpaceForInsert()
        let gained = newFree - originalFree
        return max(0, gained)
    }
}
