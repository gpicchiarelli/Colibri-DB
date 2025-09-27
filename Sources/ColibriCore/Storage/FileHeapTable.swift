//
//  FileHeapTable.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: File-backed heap steward managing on-disk pages and FSM state.

import Foundation
import Dispatch
#if os(macOS)
import Darwin
#endif
/// Aggregated fragmentation metrics for a heap table.
public struct HeapFragmentationStats: Codable {
    public let pageSize: Int
    public let totalPages: Int
    public let sampledPages: Int
    public let liveTupleCount: Int
    public let deadTupleCount: Int
    public let liveBytes: Int
    public let deadBytes: Int
    public let freeBytes: Int
    public let fragmentationRatio: Double
    public var avgFreeBytesPerPage: Double { Double(freeBytes) / Double(max(1, sampledPages)) }
    public var avgDeadBytesPerPage: Double { Double(deadBytes) / Double(max(1, sampledPages)) }
    public var estimatedTotalFreeBytes: Double {
        Double(freeBytes) * Double(totalPages) / Double(max(1, sampledPages))
    }
    public var estimatedTotalDeadBytes: Double {
        Double(deadBytes) * Double(totalPages) / Double(max(1, sampledPages))
    }
    public static func empty(pageSize: Int) -> HeapFragmentationStats {
        HeapFragmentationStats(pageSize: pageSize, totalPages: 0, sampledPages: 0, liveTupleCount: 0, deadTupleCount: 0, liveBytes: 0, deadBytes: 0, freeBytes: 0, fragmentationRatio: 0.0)
    }
}

/// File-backed heap table with paged storage and a first-fit free space map (FSM).

public final class FileHeapTable: TableStorageProtocol {
    let fileURL: URL
    let pageSize: Int
    private var fh: FileHandle
    private var lastPageId: UInt64 = 0
    private var buf: LRUBufferPool?
    private let sequentialReadHint: Bool
    private let snapshotCompression: CompressionAlgorithm
    // Persistent Free Space Map (FSM): pageId -> available contiguous free bytes for insert
    private var fsm: [UInt64: Int] = [:]
    // Fast path candidate pages with enough space (approximate)
    private var fsmCandidates: [UInt64] = []
    // FSM buckets for O(1) space class selection
    private var fsmBuckets: [Int: Set<UInt64>] = [:]
    private let bucketSizes = [64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536]
    // Concurrency: lock striping and FSM lock
    private let stripeCount: Int = 64
    private var pageLocks: [NSLock] = []
    private let fsmLock = NSLock()
    private let fsmURL: URL
    /// Number of pages currently allocated in the heap file.
    public var pageCount: UInt64 { lastPageId }

    /// Opens or creates a heap table at `path` with the specified page size and buffer capacity.
    /// - Parameters:
    ///   - path: File path for heap table.
    ///   - pageSize: Fixed page size in bytes.
    ///   - capacityPages: Buffer pool capacity in pages.
    public init(path: String,
                pageSize: Int,
                capacityPages: Int = 1024,
                flushQoS: DispatchQoS = .utility,
                sequentialReadHint: Bool = false,
                pageCompression: CompressionAlgorithm = .none) throws {
        self.fileURL = URL(fileURLWithPath: path)
        self.pageSize = pageSize
        self.fsmURL = URL(fileURLWithPath: path + ".fsm")
        self.sequentialReadHint = sequentialReadHint
        self.snapshotCompression = pageCompression
        let fm = FileManager.default
        if !fm.fileExists(atPath: path) {
            fm.createFile(atPath: path, contents: nil)
        }
        self.fh = try FileHandle(forUpdating: fileURL)
        // Initialize buffer pool for heap pages
        self.buf = LRUBufferPool(pageSize: pageSize, capacityPages: capacityPages, fetch: { [weak self] pid in
            guard let self = self else { return Data() }
            let offset = UInt64((pid - 1)) * UInt64(self.pageSize)
            if self.sequentialReadHint {
                IOHints.hintSequential(fd: self.fh.fileDescriptor, offset: offset, length: self.pageSize)
            }
            try self.fh.seek(toOffset: offset)
            return try self.fh.read(upToCount: self.pageSize) ?? Data(repeating: 0, count: self.pageSize)
        }, flush: { [weak self] pid, data in
            guard let self = self else { return }
            try self.fh.seek(toOffset: UInt64((pid - 1)) * UInt64(self.pageSize))
            try self.fh.write(contentsOf: data)
        }, namespace: "table:\(fileURL.lastPathComponent)", deferredWrite: true, maxDirty: 4096, flushQoS: flushQoS)
        self.buf?.startBackgroundFlush(every: 0.5)
        // Init locks
        self.pageLocks = (0..<stripeCount).map { _ in NSLock() }
        try loadOrInit()
        try loadOrInitFSM()
        refreshCandidates()
        rebuildBuckets()
    }

    deinit { buf?.stopBackgroundFlush(); try? fh.close() }

    private func fileSize() throws -> UInt64 {
        let attrs = try FileManager.default.attributesOfItem(atPath: fileURL.path)
        return (attrs[.size] as? NSNumber)?.uint64Value ?? 0
    }

    private func loadOrInit() throws {
        let size = try fileSize()
        if size == 0 {
            // create first page with id 1
            var p = Page(pageId: 1, pageSize: pageSize)
            try write(page: &p)
            lastPageId = 1
        } else {
            lastPageId = UInt64(size / UInt64(pageSize))
        }
    }

    // MARK: - FSM: load or rebuild and persist
    private struct FSMDisk: Codable { let pageSize: Int; let lastPageId: UInt64; let entries: [[UInt64]] /* [pid, free] */ }

    private func loadOrInitFSM() throws {
        let fm = FileManager.default
        var ok = false
        if fm.fileExists(atPath: fsmURL.path) {
            do {
                let data = try Data(contentsOf: fsmURL)
                let disk = try JSONDecoder().decode(FSMDisk.self, from: data)
                if disk.pageSize == pageSize && disk.lastPageId == lastPageId {
                    var map: [UInt64:Int] = [:]
                    for pair in disk.entries {
                        if pair.count == 2 { map[pair[0]] = Int(pair[1]) }
                    }
                    self.fsm = map
                    ok = true
                }
            } catch { ok = false }
        }
        if !ok { try rebuildFSM(); try persistFSM() }
    }

    private func rebuildFSM() throws {
        var map: [UInt64:Int] = [:]
        if lastPageId > 0 {
            for pid in 1...lastPageId {
                if let p = try? readPage(pid) {
                    map[pid] = p.availableSpaceForInsert()
                }
            }
        }
        self.fsm = map
    }

    private func persistFSM() throws {
        var entries: [[UInt64]] = []
        entries.reserveCapacity(fsm.count)
        for (pid, free) in fsm { entries.append([pid, UInt64(max(0, free))]) }
        let disk = FSMDisk(pageSize: pageSize, lastPageId: lastPageId, entries: entries)
        let data = try JSONEncoder().encode(disk)
        try data.write(to: fsmURL)
    }

    // MARK: - FSM candidates maintenance
    private func refreshCandidates() {
        fsmLock.lock(); defer { fsmLock.unlock() }
        let sorted = fsm.sorted { $0.value > $1.value }
        fsmCandidates = Array(sorted.prefix(256).map { $0.key })
    }

    private func updateCandidates(pageId: UInt64, freeBytes: Int) {
        fsmLock.lock(); defer { fsmLock.unlock() }
        
        // Update candidates
        if fsmCandidates.contains(pageId) { return }
        if fsmCandidates.count < 256 { fsmCandidates.append(pageId); return }
        var worstIdx = 0
        var worstFree = Int.max
        for (i, pid) in fsmCandidates.enumerated() {
            let v = fsm[pid] ?? 0
            if v < worstFree { worstFree = v; worstIdx = i }
        }
        if freeBytes > worstFree { fsmCandidates[worstIdx] = pageId }
        
        // Update buckets
        updateBuckets(pageId: pageId, freeBytes: freeBytes)
    }
    
    private func findBucketSize(for bytes: Int) -> Int {
        for size in bucketSizes {
            if bytes <= size { return size }
        }
        return bucketSizes.last!
    }
    
    private func rebuildBuckets() {
        fsmLock.lock(); defer { fsmLock.unlock() }
        fsmBuckets.removeAll()
        for (pid, freeBytes) in fsm {
            let bucketSize = findBucketSize(for: freeBytes)
            if fsmBuckets[bucketSize] == nil { fsmBuckets[bucketSize] = Set() }
            fsmBuckets[bucketSize]?.insert(pid)
        }
    }
    
    private func updateBuckets(pageId: UInt64, freeBytes: Int) {
        // Remove from old bucket
        for (size, var bucket) in fsmBuckets {
            if bucket.remove(pageId) != nil {
                fsmBuckets[size] = bucket
                break
            }
        }
        
        // Add to new bucket
        let bucketSize = findBucketSize(for: freeBytes)
        if fsmBuckets[bucketSize] == nil { fsmBuckets[bucketSize] = Set() }
        fsmBuckets[bucketSize]?.insert(pageId)
    }

    private func lockForPage(_ pageId: UInt64) -> NSLock {
        let idx = Int(pageId % UInt64(stripeCount))
        return pageLocks[idx]
    }

    private func selectPage(forNeed bytes: Int) -> UInt64? {
        fsmLock.lock(); defer { fsmLock.unlock() }
        
        // O(1) bucket lookup for space class
        let bucketSize = findBucketSize(for: bytes)
        if let bucket = fsmBuckets[bucketSize], !bucket.isEmpty {
            for pid in bucket {
                if (fsm[pid] ?? 0) >= bytes { return pid }
            }
        }
        
        // Fallback to candidates
        for pid in fsmCandidates {
            if (fsm[pid] ?? 0) >= bytes { return pid }
        }
        
        // Last resort: linear scan
        for pid in 1...lastPageId {
            if (fsm[pid] ?? 0) >= bytes { return pid }
        }
        return nil
    }

    private func readPage(_ pageId: UInt64) throws -> Page {
        let lock = lockForPage(pageId)
        lock.lock(); defer { lock.unlock() }
        let d: Data
        if let b = buf {
            d = try b.getPage(pageId)
        } else {
            try fh.seek(toOffset: UInt64((pageId - 1)) * UInt64(pageSize))
            d = try fh.read(upToCount: pageSize) ?? Data()
        }
        guard let p = Page(from: d, pageSize: pageSize) else { throw DBError.io("Corrupted page \(pageId)") }
        return p
    }

    private func write(page: inout Page, pageLSN: UInt64 = 0) throws {
        if pageLSN != 0 { page.setPageLSN(pageLSN) }
        page.writeHeader()
        let lock = lockForPage(page.header.pageId)
        lock.lock(); defer { lock.unlock() }
        if let b = buf {
            try b.putPage(page.header.pageId, data: page.data, dirty: true)
        } else {
            try fh.seek(toOffset: UInt64((page.header.pageId - 1)) * UInt64(pageSize))
            try fh.write(contentsOf: page.data)
        }
        // Durability is guaranteed by WAL+explicit flush. Avoid per-page fsync which severely hurts throughput.
    }

    /// Inserts a row using FSM first-fit and returns its RID.
    @discardableResult
    public func insert(_ row: Row) throws -> RID {
        let json = try JSONEncoder().encode(row)
        // choose page using FSM (first-fit), fallback to append
        if let pid = selectPage(forNeed: json.count) {
            var p = try readPage(pid)
            if let slotId = p.insert(rowBytes: json) {
                try write(page: &p)
                let free = p.availableSpaceForInsert()
                fsm[pid] = free
                try? persistFSM()
                updateCandidates(pageId: pid, freeBytes: free)
                return RID(pageId: p.header.pageId, slotId: slotId)
            }
        }
        // allocate new page
        let newId = lastPageId + 1
        var np = Page(pageId: newId, pageSize: pageSize)
        guard let slotId = np.insert(rowBytes: json) else { throw DBError.io("Record too large for page") }
        try write(page: &np)
        lastPageId = newId
        let free = np.availableSpaceForInsert()
        fsm[newId] = free
        try? persistFSM()
        updateCandidates(pageId: newId, freeBytes: free)
        return RID(pageId: newId, slotId: slotId)
    }

    /// Inserts a row with an explicit pageLSN (used during WAL redo).
    public func insert(_ row: Row, pageLSN: UInt64) throws -> RID {
        let json = try JSONEncoder().encode(row)
        if let pid = selectPage(forNeed: json.count) {
            var p = try readPage(pid)
            if let slotId = p.insert(rowBytes: json) {
                try write(page: &p, pageLSN: pageLSN)
                let free = p.availableSpaceForInsert()
                fsm[pid] = free
                try? persistFSM()
                updateCandidates(pageId: pid, freeBytes: free)
                return RID(pageId: p.header.pageId, slotId: slotId)
            }
        }
        let newId = lastPageId + 1
        var np = Page(pageId: newId, pageSize: pageSize)
        guard let slotId = np.insert(rowBytes: json) else { throw DBError.io("Record too large for page") }
        try write(page: &np, pageLSN: pageLSN)
        lastPageId = newId
        let free = np.availableSpaceForInsert()
        fsm[newId] = free
        try? persistFSM()
        updateCandidates(pageId: newId, freeBytes: free)
        return RID(pageId: newId, slotId: slotId)
    }

    /// Scans the entire table returning (RID, Row) pairs.
    public func scan() throws -> AnySequence<(RID, Row)> {
        let count = lastPageId
        if sequentialReadHint && count > 0 {
            IOHints.prepareSequentialRead(handle: fh,
                                          length: UInt64(count) * UInt64(pageSize))
        }
        var items: [(RID, Row)] = []
        for pid in 1...count {
            let p = try readPage(pid)
            if p.header.slotCount == 0 { continue }
            for sid in 1...p.header.slotCount {
                if !p.isSlotLive(sid) { continue }
                if let bytes = p.read(slotId: sid), let row = try? JSONDecoder().decode(Row.self, from: bytes) {
                    items.append((RID(pageId: pid, slotId: sid), row))
                }
            }
        }
        return AnySequence(items)
    }

    /// Returns buffer pool stats associated with this table.
    public func statsString() -> String {
        if let b = buf { return b.statsString() } else { return "nobuf" }
    }

    /// Returns buffer pool metrics if a pool is attached.
    public func poolMetrics() -> LRUBufferPool.Metrics? { buf?.metrics() }

    // Expose pageLSN for recovery checks (ARIES-style redo guard)
    /// Reads pageLSN for a given page (used for recovery safety checks).
    public func getPageLSN(_ pageId: UInt64) -> UInt64? {
        if let p = try? readPage(pageId) { return p.header.pageLSN }
        return nil
    }

    /// Reads a row by RID.
    public func read(_ rid: RID) throws -> Row {
        let p = try readPage(rid.pageId)
        guard let bytes = p.read(slotId: rid.slotId) else { throw DBError.notFound("RID \(rid)") }
        return try JSONDecoder().decode(Row.self, from: bytes)
    }

    /// Appends a new version of the row (MVP append-only update).
    public func update(_ rid: RID, _ newRow: Row) throws {
        // For MVP: append-only update (insert new row and ignore old).
        _ = try insert(newRow)
    }

    /// Logically deletes a row by zeroing its slot length.
    public func remove(_ rid: RID) throws {
        // MVP: logical delete by zeroing slot length
        var page = try readPage(rid.pageId)
        // Read header to compute slot position
        // slotId is 1-based; slots packed at end: position = pageSize - slotId*slotSize
        let slotPos = pageSize - Int(rid.slotId) * 4
        var d = page.data
        // Zero length (2 bytes) at slot
        // slot layout: offset u16 | length u16
        // We keep offset as is, set length to 0
        let lenPos = slotPos + 2
        d.replaceSubrange(lenPos..<(lenPos+2), with: [0,0])
        page.data = d
        try write(page: &page)
        let free = page.availableSpaceForInsert()
        fsm[rid.pageId] = free
        try? persistFSM()
        updateCandidates(pageId: rid.pageId, freeBytes: free)
    }

    /// Restores a logically deleted row into its original slot (used by rollback/CLR).
    public func restore(_ rid: RID, row: Row, pageLSN: UInt64? = nil) throws {
        var page = try readPage(rid.pageId)
        let bytes = try JSONEncoder().encode(row)
        let slotPos = pageSize - Int(rid.slotId) * 4
        var slot: PageSlot = page.data.withUnsafeBytes { ptr in
            ptr.baseAddress!.advanced(by: slotPos).assumingMemoryBound(to: PageSlot.self).pointee
        }
        let start = Int(slot.offset)
        let end = start + bytes.count
        guard end <= pageSize else { throw DBError.io("Cannot restore row: slot overflow") }
        slot.length = UInt16(bytes.count)
        page.data.replaceSubrange(start..<end, with: bytes)
        withUnsafeBytes(of: slot) { src in
            page.data.replaceSubrange(slotPos..<slotPos+Page.slotSize, with: src)
        }
        if let lsn = pageLSN, lsn != 0 { page.setPageLSN(lsn) }
        try write(page: &page)
        fsm[rid.pageId] = page.availableSpaceForInsert()
        try? persistFSM()
    }

    /// Removes a row and sets the pageLSN (used during WAL redo).
    public func remove(_ rid: RID, pageLSN: UInt64) throws {
        var page = try readPage(rid.pageId)
        let slotPos = pageSize - Int(rid.slotId) * 4
        var d = page.data
        let lenPos = slotPos + 2
        d.replaceSubrange(lenPos..<(lenPos+2), with: [0,0])
        page.data = d
        try write(page: &page, pageLSN: pageLSN)
        let free = page.availableSpaceForInsert()
        fsm[rid.pageId] = free
        try? persistFSM()
        updateCandidates(pageId: rid.pageId, freeBytes: free)
    }

    // Flush any dirty pages from buffer to disk
    /// Flushes dirty pages in the buffer to disk and fsyncs the file.
    public func flush(fullSync: Bool = false) throws {
        let span = Signpost.begin(.flush, name: "HeapFlush", message: fileURL.lastPathComponent)
        defer { Signpost.end(span, message: fullSync ? "fullsync" : "fsync") }
        try buf?.flushAll()
        try IOHints.synchronize(handle: fh, full: fullSync)
        writeCompressedSnapshotIfNeeded()
    }

    private func writeCompressedSnapshotIfNeeded() {
        guard snapshotCompression != .none else { return }
        guard let raw = try? Data(contentsOf: fileURL) else { return }
        guard let compressed = CompressionCodec.compress(raw, algorithm: snapshotCompression) else { return }
        let target = fileURL.appendingPathExtension(snapshotCompression.rawValue)
        try? compressed.write(to: target)
    }

    // Compact a single page: returns additional free space obtained
    /// Compacts a single page, returning the additional free bytes obtained.
    public func compactPage(_ pageId: UInt64) throws -> Int {
        var p = try readPage(pageId)
        let gained = p.compact()
        try write(page: &p)
        let free = p.availableSpaceForInsert()
        fsm[pageId] = free
        try? persistFSM()
        updateCandidates(pageId: pageId, freeBytes: free)
        return gained
    }

    // Compact all pages; returns total gained bytes and number of pages touched
    /// Compacts all pages; returns number of pages touched and total free bytes gained.
    public func compactAllPages() throws -> (pages: Int, gained: Int) {
        var touched = 0
        var total = 0
        for pid in 1...lastPageId {
            var p = try readPage(pid)
            let g = p.compact()
            if g > 0 {
                try write(page: &p)
                fsm[pid] = p.availableSpaceForInsert()
                touched += 1
                total += g
            }
        }
        try? persistFSM()
        return (touched, total)
    }

    /// Estimates fragmentation by sampling data pages.
    public func fragmentationStats(samplePages: Int? = nil) throws -> HeapFragmentationStats {
        let total = Int(lastPageId)
        guard total > 0 else { return HeapFragmentationStats.empty(pageSize: pageSize) }
        let requestedSample = samplePages ?? total
        let sampleCount = max(1, min(total, requestedSample))
        var pageIds: [UInt64] = []
        pageIds.reserveCapacity(sampleCount)
        if sampleCount >= total {
            for pid in 1...lastPageId { pageIds.append(pid) }
        } else {
            let stride = max(1, total / sampleCount)
            var pid: UInt64 = 1
            while pid <= lastPageId && pageIds.count < sampleCount {
                pageIds.append(pid)
                pid &+= UInt64(stride)
            }
            if let last = pageIds.last, last != lastPageId { pageIds.append(lastPageId) }
        }
        var liveTuples = 0
        var deadTuples = 0
        var liveBytes = 0
        var deadBytes = 0
        var freeBytes = 0
        for pid in pageIds {
            let page = try readPage(pid)
            let metrics = page.fragmentationMetrics()
            liveTuples &+= metrics.liveTuples
            deadTuples &+= metrics.deadTuples
            liveBytes &+= metrics.liveBytes
            deadBytes &+= metrics.deadBytes
            freeBytes &+= metrics.freeBytes
        }
        let sampled = pageIds.count
        let totalSampledBytes = sampled * pageSize
        let ratio = totalSampledBytes == 0 ? 0.0 : Double(deadBytes + freeBytes) / Double(totalSampledBytes)
        return HeapFragmentationStats(pageSize: pageSize,
                                      totalPages: total,
                                      sampledPages: sampled,
                                      liveTupleCount: liveTuples,
                                      deadTupleCount: deadTuples,
                                      liveBytes: liveBytes,
                                      deadBytes: deadBytes,
                                      freeBytes: freeBytes,
                                      fragmentationRatio: ratio)
    }
}
