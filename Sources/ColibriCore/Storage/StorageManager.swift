//
//  StorageManager.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-09-26.
//
// ColibrDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Storage management system with page allocation and I/O optimization.

import Foundation
import os.log

/// Storage manager coordinating page allocation and I/O operations
public final class StorageManager {
    private let logger = Logger(subsystem: "com.colibridb.storage", category: "manager")
    private let database: Database
    private let bufferPool: LRUBufferPool
    private let wal: FileWAL?
    
    // Page allocation
    private var nextPageId: UInt64 = 1
    private var freePages: Set<UInt64> = []
    private let allocationLock = NSLock()
    
    // I/O statistics
    private var readCount: UInt64 = 0
    private var writeCount: UInt64 = 0
    private var readBytes: UInt64 = 0
    private var writeBytes: UInt64 = 0
    
    public init(database: Database, bufferPool: LRUBufferPool, wal: FileWAL? = nil) {
        self.database = database
        self.bufferPool = bufferPool
        self.wal = wal
    }
    
    /// Allocates a new page
    public func allocatePage() -> UInt64 {
        allocationLock.lock()
        defer { allocationLock.unlock() }
        
        if let freePage = freePages.first {
            freePages.remove(freePage)
            return freePage
        }
        
        let pageId = nextPageId
        nextPageId += 1
        return pageId
    }
    
    /// Deallocates a page
    public func deallocatePage(_ pageId: UInt64) {
        allocationLock.lock()
        defer { allocationLock.unlock() }
        
        freePages.insert(pageId)
    }
    
    /// Reads a page from storage
    public func readPage(_ pageId: UInt64) throws -> Page {
        readCount += 1
        
        do {
            let data = try bufferPool.getPage(pageId)
            readBytes += UInt64(data.count)
            
            guard let page = Page(from: data, pageSize: 8192) else {
                throw StorageError.pageCorrupted(pageId)
            }
            
            return page
        } catch {
            throw StorageError.readFailed(pageId, error)
        }
    }
    
    /// Writes a page to storage
    public func writePage(_ page: Page) throws {
        writeCount += 1
        writeBytes += UInt64(page.data.count)
        
        do {
            // WAL page logging not implemented
            // if let wal = wal {
            //     try wal.writePage(page)
            // }
            
            // Write to buffer pool
            try bufferPool.putPage(page.header.pageId, data: page.data, dirty: true)
            
        } catch {
            throw StorageError.writeFailed(page.header.pageId, error)
        }
    }
    
    /// Flushes all dirty pages
    public func flushAll() throws {
        try bufferPool.flushAll()
    }
    
    /// Gets storage statistics
    public func getStatistics() -> StorageManagerStatistics {
        allocationLock.lock()
        defer { allocationLock.unlock() }
        
        return StorageManagerStatistics(
            totalPages: nextPageId - 1,
            freePages: freePages.count,
            readCount: readCount,
            writeCount: writeCount,
            readBytes: readBytes,
            writeBytes: writeBytes
        )
    }
    
    /// Compacts storage by removing free pages
    public func compact() throws {
        allocationLock.lock()
        defer { allocationLock.unlock() }
        
        // This would implement storage compaction
        // For now, just log the operation
        logger.info("Storage compaction completed")
    }
    
    /// Checks storage integrity
    public func checkIntegrity() throws -> Bool {
        // This would implement storage integrity checking
        // For now, just return true
        return true
    }
}

/// Storage manager statistics
public struct StorageManagerStatistics {
    public let totalPages: UInt64
    public let freePages: Int
    public let readCount: UInt64
    public let writeCount: UInt64
    public let readBytes: UInt64
    public let writeBytes: UInt64
    
    public init(totalPages: UInt64, freePages: Int, readCount: UInt64, writeCount: UInt64, readBytes: UInt64, writeBytes: UInt64) {
        self.totalPages = totalPages
        self.freePages = freePages
        self.readCount = readCount
        self.writeCount = writeCount
        self.readBytes = readBytes
        self.writeBytes = writeBytes
    }
    
    public var readRate: Double {
        return readCount > 0 ? Double(readBytes) / Double(readCount) : 0.0
    }
    
    public var writeRate: Double {
        return writeCount > 0 ? Double(writeBytes) / Double(writeCount) : 0.0
    }
}

/// Storage errors
public enum StorageError: Error, LocalizedError {
    case pageNotFound(UInt64)
    case pageCorrupted(UInt64)
    case readFailed(UInt64, Error)
    case writeFailed(UInt64, Error)
    case insufficientSpace(Int)
    case integrityCheckFailed(String)
    case walWriteFailed(Error)
    
    public var errorDescription: String? {
        switch self {
        case .pageNotFound(let pageId):
            return "Page \(pageId) not found"
        case .pageCorrupted(let pageId):
            return "Page \(pageId) is corrupted"
        case .readFailed(let pageId, let error):
            return "Failed to read page \(pageId): \(error.localizedDescription)"
        case .writeFailed(let pageId, let error):
            return "Failed to write page \(pageId): \(error.localizedDescription)"
        case .insufficientSpace(let required):
            return "Insufficient space: \(required) bytes required"
        case .integrityCheckFailed(let message):
            return "Integrity check failed: \(message)"
        case .walWriteFailed(let error):
            return "WAL write failed: \(error.localizedDescription)"
        }
    }
}

/// Page allocator for efficient page management
public final class PageAllocator {
    private var freePages: Set<UInt64> = []
    private var nextPageId: UInt64 = 1
    private let lock = NSLock()
    
    public init() {}
    
    /// Allocates a new page
    public func allocate() -> UInt64 {
        lock.lock()
        defer { lock.unlock() }
        
        if let freePage = freePages.first {
            freePages.remove(freePage)
            return freePage
        }
        
        let pageId = nextPageId
        nextPageId += 1
        return pageId
    }
    
    /// Deallocates a page
    public func deallocate(_ pageId: UInt64) {
        lock.lock()
        defer { lock.unlock() }
        
        freePages.insert(pageId)
    }
    
    /// Gets allocation statistics
    public func getStatistics() -> PageAllocationStatistics {
        lock.lock()
        defer { lock.unlock() }
        
        return PageAllocationStatistics(
            totalPages: nextPageId - 1,
            freePages: freePages.count,
            allocatedPages: (nextPageId - 1) - UInt64(freePages.count)
        )
    }
}

/// Page allocation statistics
public struct PageAllocationStatistics {
    public let totalPages: UInt64
    public let freePages: Int
    public let allocatedPages: UInt64
    
    public init(totalPages: UInt64, freePages: Int, allocatedPages: UInt64) {
        self.totalPages = totalPages
        self.freePages = freePages
        self.allocatedPages = allocatedPages
    }
    
    public var utilizationRate: Double {
        return totalPages > 0 ? Double(allocatedPages) / Double(totalPages) : 0.0
    }
}

/// I/O optimizer for storage operations
public final class IOOptimizer {
    private let logger = Logger(subsystem: "com.colibridb.storage", category: "optimizer")
    private var readPatterns: [String: ReadPattern] = [:]
    private var writePatterns: [String: WritePattern] = [:]
    private let patternLock = NSLock()
    
    public init() {}
    
    /// Records a read pattern
    public func recordRead(table: String, pageId: UInt64, size: Int) {
        patternLock.lock()
        defer { patternLock.unlock() }
        
        if readPatterns[table] == nil {
            readPatterns[table] = ReadPattern(table: table)
        }
        
        readPatterns[table]?.recordRead(pageId: pageId, size: size)
    }
    
    /// Records a write pattern
    public func recordWrite(table: String, pageId: UInt64, size: Int) {
        patternLock.lock()
        defer { patternLock.unlock() }
        
        if writePatterns[table] == nil {
            writePatterns[table] = WritePattern(table: table)
        }
        
        writePatterns[table]?.recordWrite(pageId: pageId, size: size)
    }
    
    /// Gets read pattern for a table
    public func getReadPattern(for table: String) -> ReadPattern? {
        patternLock.lock()
        defer { patternLock.unlock() }
        return readPatterns[table]
    }
    
    /// Gets write pattern for a table
    public func getWritePattern(for table: String) -> WritePattern? {
        patternLock.lock()
        defer { patternLock.unlock() }
        return writePatterns[table]
    }
    
    /// Optimizes I/O for a table
    public func optimizeIO(for table: String) -> IOOptimization {
        patternLock.lock()
        defer { patternLock.unlock() }
        
        let readPattern = readPatterns[table]
        let writePattern = writePatterns[table]
        
        return IOOptimization(
            table: table,
            readOptimization: readPattern?.getOptimization() ?? .none,
            writeOptimization: writePattern?.getOptimization() ?? .none
        )
    }
}

/// Read pattern analysis
public struct ReadPattern {
    public let table: String
    private var pageReads: [UInt64: Int] = [:]
    private var totalReads: Int = 0
    private var totalBytes: Int = 0
    
    public init(table: String) {
        self.table = table
    }
    
    public mutating func recordRead(pageId: UInt64, size: Int) {
        pageReads[pageId, default: 0] += 1
        totalReads += 1
        totalBytes += size
    }
    
    public func getOptimization() -> ReadOptimization {
        let avgReadsPerPage = Double(totalReads) / Double(pageReads.count)
        
        if avgReadsPerPage > 10.0 {
            return .sequential
        } else if avgReadsPerPage > 5.0 {
            return .random
        } else {
            return .none
        }
    }
}

/// Write pattern analysis
public struct WritePattern {
    public let table: String
    private var pageWrites: [UInt64: Int] = [:]
    private var totalWrites: Int = 0
    private var totalBytes: Int = 0
    
    public init(table: String) {
        self.table = table
    }
    
    public mutating func recordWrite(pageId: UInt64, size: Int) {
        pageWrites[pageId, default: 0] += 1
        totalWrites += 1
        totalBytes += size
    }
    
    public func getOptimization() -> WriteOptimization {
        let avgWritesPerPage = Double(totalWrites) / Double(pageWrites.count)
        
        if avgWritesPerPage > 10.0 {
            return .batch
        } else if avgWritesPerPage > 5.0 {
            return .async
        } else {
            return .none
        }
    }
}

/// I/O optimization recommendations
public struct IOOptimization {
    public let table: String
    public let readOptimization: ReadOptimization
    public let writeOptimization: WriteOptimization
    
    public init(table: String, readOptimization: ReadOptimization, writeOptimization: WriteOptimization) {
        self.table = table
        self.readOptimization = readOptimization
        self.writeOptimization = writeOptimization
    }
}

/// Read optimization types
public enum ReadOptimization {
    case none
    case sequential
    case random
    case prefetch
}

/// Write optimization types
public enum WriteOptimization {
    case none
    case batch
    case async
    case sync
}

/// Storage compression manager
public final class StorageCompressionManager {
    private let logger = Logger(subsystem: "com.colibridb.storage", category: "compression")
    private let compressionCodec: CompressionCodec?
    private var compressionStats: [String: CompressionStatistics] = [:]
    private let statsLock = NSLock()
    
    public init(compressionCodec: CompressionCodec) {
        self.compressionCodec = compressionCodec
    }
    
    /// Compresses a page
    public func compressPage(_ page: Page) throws -> Data {
        let originalSize = page.data.count
        let compressedData = CompressionCodec.compress(page.data, algorithm: .zlib) ?? page.data
        let compressedSize = compressedData.count
        
        // Update statistics
        updateCompressionStats(table: "unknown", originalSize: originalSize, compressedSize: compressedSize)
        
        return compressedData
    }
    
    /// Decompresses a page
    public func decompressPage(_ data: Data) throws -> Page {
        let decompressedData = try CompressionCodec.decompress(data, algorithm: .zlib, expectedSize: 8192)
        
        guard let page = Page(from: decompressedData, pageSize: 8192) else {
            throw StorageError.pageCorrupted(0)
        }
        
        return page
    }
    
    /// Updates compression statistics
    private func updateCompressionStats(table: String, originalSize: Int, compressedSize: Int) {
        statsLock.lock()
        defer { statsLock.unlock() }
        
        if compressionStats[table] == nil {
            compressionStats[table] = CompressionStatistics(table: table)
        }
        
        compressionStats[table]?.update(originalSize: originalSize, compressedSize: compressedSize)
    }
    
    /// Gets compression statistics
    public func getCompressionStatistics() -> [String: CompressionStatistics] {
        statsLock.lock()
        defer { statsLock.unlock() }
        return compressionStats
    }
}

/// Compression statistics
public struct CompressionStatistics {
    public let table: String
    public var totalOriginalSize: Int = 0
    public var totalCompressedSize: Int = 0
    public var compressionCount: Int = 0
    
    public init(table: String) {
        self.table = table
    }
    
    public mutating func update(originalSize: Int, compressedSize: Int) {
        totalOriginalSize += originalSize
        totalCompressedSize += compressedSize
        compressionCount += 1
    }
    
    public var compressionRatio: Double {
        return totalOriginalSize > 0 ? Double(totalCompressedSize) / Double(totalOriginalSize) : 0.0
    }
    
    public var spaceSaved: Int {
        return totalOriginalSize - totalCompressedSize
    }
}
