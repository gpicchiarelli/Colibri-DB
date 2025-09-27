//
//  FileBPlusTreeIndex.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrìDB — BSD 3-Clause License

// Theme: B+Tree grand design coordinating shared components.

import Foundation
import Dispatch

/// Indice B+Tree persistente, page-based, con WAL dedicato e buffer pool
/// configurabile. Supporta chiavi composite multi-tipo, bulk build, check di
/// consistenza e compattazione online delle foglie. Tutte le operazioni sono
/// progettate per essere idempotenti così da integrarsi con il recovery ARIES.
public final class FileBPlusTreeIndex {
    public let path: String
    let pageSize: Int
    let fm = FileManager.default
    var fh: FileHandle
    var buf: LRUBufferPool?
    let walPath: String
    var walFH: FileHandle
    var nextLSN: UInt64 = 1
    var opsSinceCheckpoint: Int = 0
    let checkpointEvery: Int = 256
    var ioHintsEnabled: Bool
    var walFullSyncEnabled: Bool = false
    private var internalWALEnabled: Bool = false  // PERFORMANCE: Disable internal WAL for speed

    struct Header {
        var pageSize: Int
        var root: UInt64
        var nextPage: UInt64
        var checkpointLSN: UInt64
    }
    var hdr: Header

    enum LeafFlag {
        static let prefixCompressed: UInt8 = 1 << 0
        static let prefixCompressedV2: UInt8 = 1 << 1
        static let ridDeltaEncoded: UInt8 = 1 << 2
    }

    enum InternalFlag {
        static let prefixCompressed: UInt16 = 1 << 15
        static let countMask: UInt16 = 0x7FFF
    }

    public init(path: String,
                pageSize: Int,
                capacityPages: Int = 256,
                flushQoS: DispatchQoS = .utility,
                ioHintsEnabled: Bool = false,
                walFullSyncEnabled: Bool = false) throws {
        self.path = path
        self.pageSize = pageSize
        self.ioHintsEnabled = ioHintsEnabled
        let url = URL(fileURLWithPath: path)
        if !fm.fileExists(atPath: path) {
            fm.createFile(atPath: path, contents: nil)
        }
        self.fh = try FileHandle(forUpdating: url)
        self.walPath = path + ".wal"
        if !fm.fileExists(atPath: walPath) {
            fm.createFile(atPath: walPath, contents: nil)
        }
        self.walFH = try FileHandle(forUpdating: URL(fileURLWithPath: walPath))
        // Note: WAL functionality disabled - using global WAL instead
        if try fh.seekToEnd() == 0 {
            self.hdr = Header(pageSize: pageSize, root: 0, nextPage: 1, checkpointLSN: 0)
            try writeHeader()
            try fh.synchronize()
        } else {
            self.hdr = try FileBPlusTreeIndex.readHeader(handle: fh, pageSize: pageSize)
        }
        setFullFSync(enabled: walFullSyncEnabled)
        self.buf = LRUBufferPool(pageSize: pageSize, capacityPages: capacityPages, fetch: { [weak self] pid in
            guard let self = self else { return Data() }
            let off = UInt64(self.pageSize) * pid
            try self.fh.seek(toOffset: off)
            return try self.fh.read(upToCount: self.pageSize) ?? Data(repeating: 0, count: self.pageSize)
        }, flush: { [weak self] pid, data in
            guard let self = self else { return }
            let off = UInt64(self.pageSize) * pid
            try self.fh.seek(toOffset: off)
            try self.fh.write(contentsOf: data)
        }, namespace: "index:\(URL(fileURLWithPath: path).lastPathComponent)", deferredWrite: true, maxDirty: 2048, flushQoS: flushQoS)
        self.buf?.startBackgroundFlush(every: 0.5)
    }

    deinit { buf?.stopBackgroundFlush(); try? fh.close() }

    public func close() {
        buf?.stopBackgroundFlush()
        try? buf?.flushAll()
        try? fh.close()
        try? walFH.close()
    }

    /// Toggles best-effort sequential hints for WAL replay and cold scans.
    public func setIOHints(enabled: Bool) {
        ioHintsEnabled = enabled
    }

    /// Enables `F_FULLFSYNC` on the index WAL when supported.
    public func setFullFSync(enabled: Bool) {
#if os(macOS)
        walFullSyncEnabled = enabled
#else
        walFullSyncEnabled = false
#endif
    }

    /// Enables/disables the internal index WAL. When disabled, index operations
    /// do not append to the per-index WAL and expect the global WAL to drive recovery.
    public func setInternalWALEnabled(_ enabled: Bool) { internalWALEnabled = enabled }
    public func isInternalWALEnabled() -> Bool { internalWALEnabled }
    
    /// Flush buffers to disk (placeholder - WAL functionality disabled)
    public func flushBuffers(fullSync: Bool = false) throws {
        // WAL functionality disabled - using global WAL instead
        if fullSync {
            try fh.synchronize()
        }
    }
    
    /// Checkpoint index (placeholder - WAL functionality disabled)
    public func checkpointIndex() throws {
        // WAL functionality disabled - using global WAL instead
        try fh.synchronize()
    }
    
    /// Close WAL and file handle (additional cleanup)
    public func closeAll() throws {
        try? walFH.close()
        try? fh.close()
    }
}
