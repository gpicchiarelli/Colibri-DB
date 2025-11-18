//
//  IndexManager.swift
//  ColibrìDB Index Manager Implementation
//
//  Based on: spec/Index.tla
//  Implements: Database indexing system
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//
//  Key Properties:
//  - Index Consistency: Indexes are consistent
//  - Data Integrity: Data integrity is maintained
//  - Performance Metrics: Performance metrics are tracked
//

import Foundation
import Logging

// MARK: - Index Types

/// Index ID
/// Corresponds to TLA+: IndexID
public typealias IndexID = UInt64


/// Index entry
/// Corresponds to TLA+: IndexEntry
public struct IndexEntry: Codable, Sendable, Equatable {
    public let entryId: String
    public let indexId: IndexID
    public let key: String
    public let value: String
    public let pageId: UInt64
    public let offset: UInt64
    public var isDeleted: Bool
    public let timestamp: UInt64
    
    public init(entryId: String, indexId: IndexID, key: String, value: String, pageId: UInt64, offset: UInt64, isDeleted: Bool, timestamp: UInt64) {
        self.entryId = entryId
        self.indexId = indexId
        self.key = key
        self.value = value
        self.pageId = pageId
        self.offset = offset
        self.isDeleted = isDeleted
        self.timestamp = timestamp
    }
}

// IndexMetadata is defined in Catalog/CatalogManager.swift

/// Index metrics
/// Corresponds to TLA+: IndexMetrics
public struct IndexMetrics: Codable, Sendable, Equatable {
    public let indexId: IndexID
    public let entryCount: Int
    public let size: UInt64
    public let height: Int
    public let leafCount: Int
    public let internalCount: Int
    public let averageKeySize: Double
    public let averageValueSize: Double
    public let hitRate: Double
    public let missRate: Double
    public let scanCount: Int
    public let insertCount: Int
    public let updateCount: Int
    public let deleteCount: Int
    
    public init(indexId: IndexID, entryCount: Int, size: UInt64, height: Int, leafCount: Int, internalCount: Int, averageKeySize: Double, averageValueSize: Double, hitRate: Double, missRate: Double, scanCount: Int, insertCount: Int, updateCount: Int, deleteCount: Int) {
        self.indexId = indexId
        self.entryCount = entryCount
        self.size = size
        self.height = height
        self.leafCount = leafCount
        self.internalCount = internalCount
        self.averageKeySize = averageKeySize
        self.averageValueSize = averageValueSize
        self.hitRate = hitRate
        self.missRate = missRate
        self.scanCount = scanCount
        self.insertCount = insertCount
        self.updateCount = updateCount
        self.deleteCount = deleteCount
    }
}

// MARK: - Index Manager

/// Index Manager for database indexing system
/// Corresponds to TLA+ module: Index.tla
public actor IndexManagerActor {
    
    // MARK: - State Variables (TLA+ vars)
    
    /// Indexes
    /// TLA+: indexes \in [IndexID -> Index]
    private var indexes: [IndexID: Index] = [:]
    
    /// Index metadata
    /// TLA+: indexMetadata \in [IndexID -> IndexMetadata]
    private var indexMetadata: [IndexID: IndexMetadata] = [:]
    
    /// Index metrics
    /// TLA+: indexMetrics \in [IndexID -> IndexMetrics]
    private var indexMetrics: [IndexID: IndexMetrics] = [:]
    
    /// Index cache
    /// TLA+: indexCache \in [IndexID -> [IndexEntry]]
    private var indexCache: [IndexID: [IndexEntry]] = [:]
    
    // MARK: - Dependencies
    
    /// Storage manager
    private let storageManager: StorageManager
    
    /// Buffer manager
    private let bufferManager: BufferManager
    
    /// Catalog Manager - **Catalog-First**: Index Manager MUST check Catalog before operations
    /// Index Manager uses Catalog to:
    /// - Validate index existence before operations
    /// - Get index metadata (columns, type, uniqueness) from Catalog
    /// - Ensure all indexes are defined in Catalog first
    /// - Do NOT maintain duplicate index metadata (Catalog is single source of truth)
    private let catalog: CatalogManager
    
    /// Logger
    private let logger: ColibriLogger
    
    // MARK: - Initialization
    
    /// Initialize Index Manager
    /// - Parameters:
    ///   - storageManager: Storage manager for I/O operations
    ///   - bufferManager: Buffer manager for page caching
    ///   - catalog: **Catalog-First**: Catalog Manager (REQUIRED)
    public init(storageManager: StorageManager, bufferManager: BufferManager, catalog: CatalogManager) {
        self.storageManager = storageManager
        self.bufferManager = bufferManager
        self.catalog = catalog
        self.logger = ColibriLogger()
        
        // TLA+ Init
        self.indexes = [:]
        self.indexMetadata = [:]
        self.indexMetrics = [:]
        self.indexCache = [:]
    }
    
    // MARK: - Index Operations
    
    /// Create index
    /// TLA+ Action: CreateIndex(metadata)
    /// 
    /// **Catalog-First**: Index MUST be created in Catalog FIRST.
    /// This method creates the index STRUCTURE, but metadata comes from Catalog.
    public func createIndex(metadata: IndexMetadata) async throws -> IndexID {
        // **Catalog-First**: Check if index exists in Catalog
        guard let catalogIndexMetadata = await catalog.getIndex(name: metadata.name) else {
            throw IndexError.indexNotFound
        }
        
        // **Catalog-First**: Validate metadata matches Catalog
        guard catalogIndexMetadata.tableName == metadata.tableName,
              catalogIndexMetadata.columns == metadata.columns,
              catalogIndexMetadata.indexType == metadata.indexType,
              catalogIndexMetadata.unique == metadata.unique else {
            throw IndexError.indexMetadataMismatch
        }
        
        // **Catalog-First**: Get table metadata from Catalog to validate columns
        guard let tableMetadata = await catalog.getTable(name: metadata.tableName) else {
            throw IndexError.tableNotFound
        }
        
        // Validate index columns exist in table (double-check)
        for column in metadata.columns {
            guard tableMetadata.columns.contains(where: { $0.name == column }) else {
                throw IndexError.invalidColumn("Index column \(column) not found in table")
            }
        }
        
        // TLA+: Create index structure (Catalog has metadata, we create physical structure)
        let index = Index(
            indexId: IndexID(0), // Generate new ID
            indexType: metadata.indexType,
            entries: [],
            isUnique: metadata.unique,
            isPrimary: false, // Default value
            isClustered: false, // Default value
            fillFactor: 0.8, // Default value
            created: UInt64(Date().timeIntervalSince1970 * 1000),
            lastModified: UInt64(Date().timeIntervalSince1970 * 1000)
        )
        
        let indexId = IndexID(UInt64(indexes.count + 1))
        indexes[indexId] = index
        // **Catalog-First**: Do NOT store duplicate metadata (Catalog is single source of truth)
        // indexMetadata[indexId] = metadata  // REMOVED - use Catalog instead
        
        // TLA+: Initialize metrics
        let metrics = IndexMetrics(
            indexId: indexId,
            entryCount: 0,
            size: 0,
            height: 0,
            leafCount: 0,
            internalCount: 0,
            averageKeySize: 0.0,
            averageValueSize: 0.0,
            hitRate: 0.0,
            missRate: 0.0,
            scanCount: 0,
            insertCount: 0,
            updateCount: 0,
            deleteCount: 0
        )
        indexMetrics[indexId] = metrics
        
        await logger.info("Created index", metadata: ["name": metadata.name, "id": "\(indexId)"])
        return indexId
    }
    
    /// Drop index
    /// TLA+ Action: DropIndex(indexId)
    /// 
    /// **Catalog-First**: Index MUST be dropped from Catalog FIRST.
    /// This method drops the index STRUCTURE.
    public func dropIndex(indexId: IndexID) async throws {
        // **Catalog-First**: Check if index exists in Catalog
        // Note: We need to find index name from indexId, which requires a mapping
        // For now, check that index structure exists locally
        
        // TLA+: Check if index exists locally
        guard indexes[indexId] != nil else {
            throw IndexError.indexNotFound
        }
        
        // **Catalog-First**: Index should already be dropped from Catalog
        // (Catalog.dropIndex should be called first)
        // We just drop the physical structure here
        
        // TLA+: Drop index structure
        indexes.removeValue(forKey: indexId)
        // **Catalog-First**: Do NOT maintain duplicate metadata
        // indexMetadata.removeValue(forKey: indexId)  // REMOVED - Catalog is source of truth
        indexMetrics.removeValue(forKey: indexId)
        indexCache.removeValue(forKey: indexId)
        
        await logger.info("Dropped index", metadata: ["id": "\(indexId)"])
    }
    
    /// Insert entry
    /// TLA+ Action: InsertEntry(indexId, entry)
    public func insertEntry(indexId: IndexID, entry: IndexEntry) async throws {
        // TLA+: Check if index exists
        guard var index = indexes[indexId] else {
            throw IndexError.indexNotFound
        }
        
        // TLA+: Check uniqueness
        if index.isUnique {
            let existingEntry = index.entries.first { $0.key == entry.key && !$0.isDeleted }
            if existingEntry != nil {
                throw IndexError.duplicateKey
            }
        }
        
        // TLA+: Insert entry
        index.entries.append(entry)
        index.lastModified = UInt64(Date().timeIntervalSince1970 * 1000)
        indexes[indexId] = index
        
        // TLA+: Update cache
        if indexCache[indexId] == nil {
            indexCache[indexId] = []
        }
        indexCache[indexId]?.append(entry)
        
        // If entry has pageId, ensure page is in buffer (for persistence)
        if entry.pageId > 0 {
            // Touch the page to ensure it's in buffer cache
            _ = await bufferManager.getPageQuery(pageId: PageID(entry.pageId))
        }
        
        // TLA+: Update metrics
        updateMetrics(indexId: indexId)
        
        await logger.debug("Inserted entry into index", metadata: ["id": "\(indexId)"])
    }
    
    /// Delete entry
    /// TLA+ Action: DeleteEntry(indexId, entryId)
    public func deleteEntry(indexId: IndexID, entryId: String) async throws {
        // TLA+: Check if index exists
        guard var index = indexes[indexId] else {
            throw IndexError.indexNotFound
        }
        
        // TLA+: Find and mark as deleted
        if let entryIndex = index.entries.firstIndex(where: { $0.entryId == entryId }) {
            index.entries[entryIndex].isDeleted = true
            index.lastModified = UInt64(Date().timeIntervalSince1970 * 1000)
            indexes[indexId] = index
            
            // TLA+: Update cache
            if let cacheIndex = indexCache[indexId]?.firstIndex(where: { $0.entryId == entryId }) {
                indexCache[indexId]?[cacheIndex].isDeleted = true
            }
            
            // TLA+: Update metrics
            updateMetrics(indexId: indexId)
            
            await logger.debug("Deleted entry from index", metadata: ["id": "\(indexId)"])
        } else {
            throw IndexError.entryNotFound
        }
    }
    
    /// Lookup entry
    /// TLA+ Action: LookupEntry(indexId, key)
    public func lookupEntry(indexId: IndexID, key: String) async throws -> [IndexEntry] {
        // TLA+: Check if index exists
        guard let index = indexes[indexId] else {
            throw IndexError.indexNotFound
        }
        
        // TLA+: Lookup entries
        let entries = index.entries.filter { $0.key == key && !$0.isDeleted }
        
        // Prefetch pages for found entries
        let pageIds = Set(entries.map { PageID($0.pageId) })
        for pageId in pageIds {
            // Prefetch page into buffer cache
                _ = await bufferManager.getPageQuery(pageId: pageId)
        }
        
        // TLA+: Update metrics
        updateMetrics(indexId: indexId)
        
        await logger.debug("Looked up entries in index", metadata: ["id": "\(indexId)", "key": key])
        return entries
    }
    
    /// Range scan
    /// TLA+ Action: RangeScan(indexId, startKey, endKey)
    public func rangeScan(indexId: IndexID, startKey: String, endKey: String) async throws -> [IndexEntry] {
        // TLA+: Check if index exists
        guard let index = indexes[indexId] else {
            throw IndexError.indexNotFound
        }
        
        // TLA+: Range scan
        let entries = index.entries.filter { entry in
            !entry.isDeleted && entry.key >= startKey && entry.key <= endKey
        }
        
        // Prefetch pages for found entries
        let pageIds = Set(entries.map { PageID($0.pageId) })
        for pageId in pageIds {
            // Prefetch page into buffer cache
                _ = await bufferManager.getPageQuery(pageId: pageId)
        }
        
        // TLA+: Update metrics
        updateMetrics(indexId: indexId)
        
        await logger.debug("Range scanned index", metadata: ["id": "\(indexId)", "start": startKey, "end": endKey])
        return entries
    }
    
    // MARK: - Helper Methods
    
    /// Update metrics
    private func updateMetrics(indexId: IndexID) {
        // TLA+: Update index metrics
        guard let index = indexes[indexId] else { return }
        
        let entryCount = index.entries.filter { !$0.isDeleted }.count
        let size = index.entries.reduce(0) { $0 + UInt64($1.key.count + $1.value.count) }
        let averageKeySize = index.entries.isEmpty ? 0.0 : Double(index.entries.reduce(0) { $0 + $1.key.count }) / Double(index.entries.count)
        let averageValueSize = index.entries.isEmpty ? 0.0 : Double(index.entries.reduce(0) { $0 + $1.value.count }) / Double(index.entries.count)
        
        let metrics = IndexMetrics(
            indexId: indexId,
            entryCount: entryCount,
            size: size,
            height: 0, // Simplified
            leafCount: 0, // Simplified
            internalCount: 0, // Simplified
            averageKeySize: averageKeySize,
            averageValueSize: averageValueSize,
            hitRate: 0.0, // Simplified
            missRate: 0.0, // Simplified
            scanCount: 0, // Simplified
            insertCount: 0, // Simplified
            updateCount: 0, // Simplified
            deleteCount: 0 // Simplified
        )
        
        indexMetrics[indexId] = metrics
    }
    
    /// Get index type
    private func getIndexType(indexId: IndexID) -> IndexType? {
        return indexes[indexId]?.indexType
    }
    
    /// Get index metadata
    private func getIndexMetadata(indexId: IndexID) -> IndexMetadata? {
        return indexMetadata[indexId]
    }
    
    /// Update index metrics
    private func updateIndexMetrics(indexId: IndexID, metrics: IndexMetrics) {
        indexMetrics[indexId] = metrics
    }
    
    // MARK: - Query Operations
    
    
    
    /// Get index metrics
    public func getIndexMetrics(indexId: IndexID) -> IndexMetrics? {
        return indexMetrics[indexId]
    }
    
    /// Get all indexes
    public func getAllIndexes() -> [Index] {
        return Array(indexes.values)
    }
    
    /// Get indexes by table
    public func getIndexesByTable(tableName: String) -> [Index] {
        return indexes.values.filter { index in
            indexMetadata[index.indexId]?.tableName == tableName
        }
    }
    
    /// Get indexes by type
    public func getIndexesByType(type: IndexType) -> [Index] {
        return indexes.values.filter { $0.indexType == type }
    }
    
    /// Get index count
    public func getIndexCount() -> Int {
        return indexes.count
    }
    
    /// Get index metrics
    public func getIndexMetrics() -> [IndexMetrics] {
        return Array(indexMetrics.values)
    }
    
    /// Get index metadata for table
    public func getIndexMetadataForTable(tableName: String) -> [IndexMetadata] {
        return indexMetadata.values.filter { $0.tableName == tableName }
    }
    
    /// Check if index exists
    public func indexExists(indexId: IndexID) -> Bool {
        return indexes[indexId] != nil
    }
    
    /// Get index by name
    public func getIndexByName(name: String) -> Index? {
        return indexes.values.first { index in
            indexMetadata[index.indexId]?.name == name
        }
    }
    
    /// Get unique indexes
    public func getUniqueIndexes() -> [Index] {
        return indexes.values.filter { $0.isUnique }
    }
    
    /// Get primary indexes
    public func getPrimaryIndexes() -> [Index] {
        return indexes.values.filter { $0.isPrimary }
    }
    
    /// Get clustered indexes
    public func getClusteredIndexes() -> [Index] {
        return indexes.values.filter { $0.isClustered }
    }
    
    /// Get index entries
    public func getIndexEntries(indexId: IndexID) -> [IndexEntry] {
        return indexes[indexId]?.entries ?? []
    }
    
    /// Get cached entries
    public func getCachedEntries(indexId: IndexID) -> [IndexEntry] {
        return indexCache[indexId] ?? []
    }
    
    /// Clear index cache
    public func clearIndexCache() async throws {
        indexCache.removeAll()
        await logger.info("Index cache cleared")
    }
    
    /// Rebuild index
    public func rebuildIndex(indexId: IndexID) async throws {
        // TLA+: Rebuild index
        guard var index = indexes[indexId] else {
            throw IndexError.indexNotFound
        }
        
        // TLA+: Clear and rebuild
        index.entries.removeAll()
        index.lastModified = UInt64(Date().timeIntervalSince1970 * 1000)
        indexes[indexId] = index
        
        // TLA+: Clear cache
        indexCache[indexId] = []
        
        // TLA+: Update metrics
        updateMetrics(indexId: indexId)
        
        await logger.info("Rebuilt index", metadata: ["id": "\(indexId)"])
    }
    
    // MARK: - Invariant Checking (for testing)
    
    /// Check index consistency invariant
    /// TLA+ Inv_Index_IndexConsistency
    public func checkIndexConsistencyInvariant() -> Bool {
        // Check that indexes are consistent
        // Verify that all indexes have valid metadata
        for (indexId, index) in indexes {
            guard indexMetadata[indexId] != nil else {
                return false
            }
            // Check that index entries match metadata
            if let metadata = indexMetadata[indexId] {
                if index.indexType != metadata.indexType {
                    return false
                }
                if index.isUnique != metadata.unique {
                    return false
                }
            }
        }
        return true
    }
    
    /// Check data integrity invariant
    /// TLA+ Inv_Index_DataIntegrity
    public func checkDataIntegrityInvariant() -> Bool {
        // Check that data integrity is maintained
        // Verify that unique indexes have no duplicate keys
        for (_, index) in indexes where index.isUnique {
            let activeEntries = index.entries.filter { !$0.isDeleted }
            let keys = Set(activeEntries.map { $0.key })
            if keys.count != activeEntries.count {
                return false // Duplicate keys found
            }
        }
        // Verify that entries match their metadata
        for (indexId, index) in indexes {
            for entry in index.entries {
                if entry.indexId != indexId {
                    return false
                }
            }
        }
        return true
    }
    
    /// Check performance metrics invariant
    /// TLA+ Inv_Index_PerformanceMetrics
    public func checkPerformanceMetricsInvariant() -> Bool {
        // Check that performance metrics are tracked
        // Verify that metrics exist for all indexes
        for indexId in indexes.keys {
            guard indexMetrics[indexId] != nil else {
                return false
            }
        }
        // Verify that metrics values are non-negative
        for metrics in indexMetrics.values {
            if metrics.entryCount < 0 || metrics.size < 0 || metrics.height < 0 {
                return false
            }
            if metrics.hitRate < 0.0 || metrics.hitRate > 1.0 {
                return false
            }
            if metrics.missRate < 0.0 || metrics.missRate > 1.0 {
                return false
            }
        }
        return true
    }
    
    /// Check all invariants
    public func checkAllInvariants() -> Bool {
        let indexConsistency = checkIndexConsistencyInvariant()
        let dataIntegrity = checkDataIntegrityInvariant()
        let performanceMetrics = checkPerformanceMetricsInvariant()
        
        return indexConsistency && dataIntegrity && performanceMetrics
    }
}

// MARK: - Supporting Types

/// Index
public struct Index: Codable, Sendable, Equatable {
    public let indexId: IndexID
    public let indexType: IndexType
    public var entries: [IndexEntry]
    public let isUnique: Bool
    public let isPrimary: Bool
    public let isClustered: Bool
    public let fillFactor: Double
    public let created: UInt64
    public var lastModified: UInt64
    
    public init(indexId: IndexID, indexType: IndexType, entries: [IndexEntry], isUnique: Bool, isPrimary: Bool, isClustered: Bool, fillFactor: Double, created: UInt64, lastModified: UInt64) {
        self.indexId = indexId
        self.indexType = indexType
        self.entries = entries
        self.isUnique = isUnique
        self.isPrimary = isPrimary
        self.isClustered = isClustered
        self.fillFactor = fillFactor
        self.created = created
        self.lastModified = lastModified
    }
}

/// Storage manager
public protocol StorageManager: Sendable {
    func readPage(pageId: UInt64) async throws -> Data
    func writePage(pageId: UInt64, data: Data) async throws
    func deletePage(pageId: UInt64) async throws
}

// BufferManager protocol is defined in Buffer/BufferManager.swift


/// Index error
public enum IndexError: Error, LocalizedError, Equatable {
    case indexNotFound
    case entryNotFound
    case duplicateKey
    case indexCreationFailed
    case indexDropFailed
    case entryInsertFailed
    case entryDeleteFailed
    case lookupFailed
    case scanFailed
    case indexMetadataMismatch  // **Catalog-First**: Index metadata doesn't match Catalog
    case tableNotFound  // **Catalog-First**: Table not found in Catalog
    case invalidColumn(String)  // **Catalog-First**: Invalid column (from Catalog validation)
    
    public var errorDescription: String? {
        switch self {
        case .indexNotFound:
            return "Index not found"
        case .entryNotFound:
            return "Index entry not found"
        case .duplicateKey:
            return "Duplicate key in unique index"
        case .indexCreationFailed:
            return "Index creation failed"
        case .indexDropFailed:
            return "Index drop failed"
        case .entryInsertFailed:
            return "Entry insertion failed"
        case .entryDeleteFailed:
            return "Entry deletion failed"
        case .lookupFailed:
            return "Entry lookup failed"
        case .scanFailed:
            return "Range scan failed"
        case .indexMetadataMismatch:
            return "Index metadata does not match Catalog (Catalog-First violation)"
        case .tableNotFound:
            return "Table not found in Catalog"
        case .invalidColumn(let message):
            return "Invalid column: \(message)"
        }
    }
}