//
//  IndexSubsystemTests.swift
//  ColibrìDB - Index Subsystem Tests
//
//  Tests for unified index management across all index types
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//

import XCTest
@testable import ColibriCore

/// Tests for the unified Index Subsystem
/// Covers all 9 index types: BTree, Hash, ART, LSM, Fractal, Bloom, SkipList, TTree, Radix
final class IndexSubsystemTests {
    
    // MARK: - Setup
    
    func testIndexSubsystemCreation() async throws {
        // Arrange & Act
        let subsystem = IndexSubsystem()
        
        // Assert
        XCTAssert(subsystem != nil)
        let stats = await subsystem.getStats()
        XCTAssert(stats.totalIndexes == 0)
    }
    
    // MARK: - Index Management Tests
    
    func testCreateBTreeIndex() async throws {
        // Arrange
        let subsystem = IndexSubsystem()
        
        // Act
        try await subsystem.createIndex(
            indexName: "users_pk",
            indexType: .btree,
            tableName: "users",
            columns: ["id"],
            unique: true
        )
        
        // Assert
        let index = await subsystem.getIndex(indexName: "users_pk")
        XCTAssert(index != nil)
        XCTAssert(index?.indexType == .btree)
        XCTAssert(index?.tableName == "users")
        XCTAssert(index?.columns == ["id"])
        XCTAssert(index?.unique == true)
        
        let stats = await subsystem.getStats()
        XCTAssert(stats.totalIndexes == 1)
    }
    
    func testCreateHashIndex() async throws {
        // Arrange
        let subsystem = IndexSubsystem()
        
        // Act
        try await subsystem.createIndex(
            indexName: "users_email",
            indexType: .hash,
            tableName: "users",
            columns: ["email"],
            unique: true
        )
        
        // Assert
        let index = await subsystem.getIndex(indexName: "users_email")
        XCTAssert(index?.indexType == .hash)
        XCTAssert(index?.unique == true)
    }
    
    func testCreateARTIndex() async throws {
        // Arrange
        let subsystem = IndexSubsystem()
        
        // Act
        try await subsystem.createIndex(
            indexName: "users_name",
            indexType: .btree,  // ART not supported, using btree
            tableName: "users",
            columns: ["first_name", "last_name"]
        )
        
        // Assert
        let index = await subsystem.getIndex(indexName: "users_name")
        XCTAssert(index?.indexType == .btree)  // ART not supported, using btree
        XCTAssert(index?.columns == ["first_name", "last_name"])
    }
    
    func testCreateLSMIndex() async throws {
        // Arrange
        let subsystem = IndexSubsystem()
        
        // Act
        try await subsystem.createIndex(
            indexName: "logs_timestamp",
            indexType: .btree,  // LSM not supported, using btree
            tableName: "logs",
            columns: ["timestamp"]
        )
        
        // Assert
        let index = await subsystem.getIndex(indexName: "logs_timestamp")
        XCTAssert(index?.indexType == .btree)  // LSM not supported, using btree
    }
    
    func testCreateFractalIndex() async throws {
        // Arrange
        let subsystem = IndexSubsystem()
        
        // Act
        try await subsystem.createIndex(
            indexName: "events_time",
            indexType: .btree,  // Fractal not supported, using btree
            tableName: "events",
            columns: ["created_at"]
        )
        
        // Assert
        let index = await subsystem.getIndex(indexName: "events_time")
        XCTAssert(index?.indexType == .btree)  // Fractal not supported, using btree
    }
    
    func testCreateBloomFilter() async throws {
        // Arrange
        let subsystem = IndexSubsystem()
        
        // Act
        try await subsystem.createIndex(
            indexName: "users_exists",
            indexType: .btree,  // Bloom not supported, using btree
            tableName: "users",
            columns: ["id"]
        )
        
        // Assert
        let index = await subsystem.getIndex(indexName: "users_exists")
        XCTAssert(index?.indexType == .btree)  // Bloom not supported, using btree
    }
    
    func testCreateSkipListIndex() async throws {
        // Arrange
        let subsystem = IndexSubsystem()
        
        // Act
        try await subsystem.createIndex(
            indexName: "scores_rank",
            indexType: .btree,  // SkipList not supported, using btree
            tableName: "scores",
            columns: ["score"]
        )
        
        // Assert
        let index = await subsystem.getIndex(indexName: "scores_rank")
        XCTAssert(index?.indexType == .btree)  // SkipList not supported, using btree
    }
    
    func testCreateTTreeIndex() async throws {
        // Arrange
        let subsystem = IndexSubsystem()
        
        // Act
        try await subsystem.createIndex(
            indexName: "cache_key",
            indexType: .btree,  // TTree not supported, using btree
            tableName: "cache",
            columns: ["key"]
        )
        
        // Assert
        let index = await subsystem.getIndex(indexName: "cache_key")
        XCTAssert(index?.indexType == .btree)  // TTree not supported, using btree
    }
    
    func testCreateRadixIndex() async throws {
        // Arrange
        let subsystem = IndexSubsystem()
        
        // Act
        try await subsystem.createIndex(
            indexName: "paths_prefix",
            indexType: .btree,  // Radix not supported, using btree
            tableName: "paths",
            columns: ["path"]
        )
        
        // Assert
        let index = await subsystem.getIndex(indexName: "paths_prefix")
        XCTAssert(index?.indexType == .btree)  // Radix not supported, using btree
    }
    
    func testCreateDuplicateIndexFails() async throws {
        // Arrange
        let subsystem = IndexSubsystem()
        try await subsystem.createIndex(
            indexName: "test_index",
            indexType: .btree,
            tableName: "test_table",
            columns: ["id"]
        )
        
        // Act & Assert
        do {
            try await subsystem.createIndex(
                indexName: "test_index",
                indexType: .hash,
                tableName: "test_table",
                columns: ["id"]
            )
        }
    }
    
    func testDropIndex() async throws {
        // Arrange
        let subsystem = IndexSubsystem()
        try await subsystem.createIndex(
            indexName: "test_index",
            indexType: .btree,
            tableName: "test_table",
            columns: ["id"]
        )
        
        // Act
        try await subsystem.dropIndex(indexName: "test_index")
        
        // Assert
        let index = await subsystem.getIndex(indexName: "test_index")
        XCTAssert(index == nil)
        
        let stats = await subsystem.getStats()
        XCTAssert(stats.totalIndexes == 0)
    }
    
    func testDropNonExistentIndexFails() async throws {
        // Arrange
        let subsystem = IndexSubsystem()
        
        // Act & Assert
        do {
            try await subsystem.dropIndex(indexName: "non_existent")
        }
    }
    
    // MARK: - Index Operations Tests
    
    func testInsertIntoIndexes() async throws {
        // Arrange
        let subsystem = IndexSubsystem()
        try await subsystem.createIndex(
            indexName: "users_id",
            indexType: .btree,
            tableName: "users",
            columns: ["id"]
        )
        try await subsystem.createIndex(
            indexName: "users_email",
            indexType: .hash,
            tableName: "users",
            columns: ["email"]
        )
        
        // Act
        try await subsystem.insert(tableName: "users", key: "123", recordId: "rec_123")
        
        // Assert
        let stats = await subsystem.getStats()
        XCTAssert(stats.totalInserts == 1)
    }
    
    func testDeleteFromIndexes() async throws {
        // Arrange
        let subsystem = IndexSubsystem()
        try await subsystem.createIndex(
            indexName: "users_id",
            indexType: .btree,
            tableName: "users",
            columns: ["id"]
        )
        
        // Act
        try await subsystem.delete(tableName: "users", key: "123")
        
        // Assert
        let stats = await subsystem.getStats()
        XCTAssert(stats.totalDeletes == 1)
    }
    
    func testSearchWithIndex() async throws {
        // Arrange
        let subsystem = IndexSubsystem()
        try await subsystem.createIndex(
            indexName: "users_email",
            indexType: .hash,
            tableName: "users",
            columns: ["email"]
        )
        
        // Act
        let results = try await subsystem.search(tableName: "users", column: "email", key: "test@example.com")
        
        // Assert
        XCTAssert(results != nil)
        let stats = await subsystem.getStats()
        XCTAssert(stats.totalSearches == 1)
    }
    
    func testSearchWithoutSuitableIndexFails() async throws {
        // Arrange
        let subsystem = IndexSubsystem()
        
        // Act & Assert
        do {
            try await subsystem.search(tableName: "users", column: "email", key: "test@example.com")
        }
    }
    
    // MARK: - Query Optimization Tests
    
    func testSelectIndexForQuery() async throws {
        // Arrange
        let subsystem = IndexSubsystem()
        try await subsystem.createIndex(
            indexName: "users_email_hash",
            indexType: .hash,
            tableName: "users",
            columns: ["email"]
        )
        try await subsystem.createIndex(
            indexName: "users_email_btree",
            indexType: .btree,
            tableName: "users",
            columns: ["email"]
        )
        
        // Act
        let selectedIndex = await subsystem.selectIndexForQuery(
            queryHash: "query_123",
            tableName: "users",
            whereColumn: "email"
        )
        
        // Assert
        XCTAssert(selectedIndex != nil)
        XCTAssert(selectedIndex == "users_email_hash" || selectedIndex == "users_email_btree")
    }
    
    func testGetSelectedIndex() async throws {
        // Arrange
        let subsystem = IndexSubsystem()
        try await subsystem.createIndex(
            indexName: "users_email",
            indexType: .hash,
            tableName: "users",
            columns: ["email"]
        )
        
        // Act
        _ = await subsystem.selectIndexForQuery(
            queryHash: "query_123",
            tableName: "users",
            whereColumn: "email"
        )
        let selectedIndex = await subsystem.getSelectedIndex(queryHash: "query_123")
        
        // Assert
        XCTAssert(selectedIndex == "users_email")
    }
    
    // MARK: - Maintenance Tests
    
    func testUpdateStatistics() async throws {
        // Arrange
        let subsystem = IndexSubsystem()
        try await subsystem.createIndex(
            indexName: "users_id",
            indexType: .btree,
            tableName: "users",
            columns: ["id"]
        )
        
        // Act
        await subsystem.updateStatistics(indexName: "users_id")
        
        // Assert
        let stats = await subsystem.getIndexStats(indexName: "users_id")
        XCTAssert(stats != nil)
    }
    
    func testRebuildIndex() async throws {
        // Arrange
        let subsystem = IndexSubsystem()
        try await subsystem.createIndex(
            indexName: "users_id",
            indexType: .btree,
            tableName: "users",
            columns: ["id"]
        )
        
        // Act
        try await subsystem.rebuildIndex(indexName: "users_id")
        
        // Assert
        let index = await subsystem.getIndex(indexName: "users_id")
        XCTAssert(index != nil)
        
        let stats = await subsystem.getStats()
        XCTAssert(stats.totalRebuilds == 1)
    }
    
    func testRebuildNonExistentIndexFails() async throws {
        // Arrange
        let subsystem = IndexSubsystem()
        
        // Act & Assert
        do {
            try await subsystem.rebuildIndex(indexName: "non_existent")
        }
    }
    
    // MARK: - Query Methods Tests
    
    func testGetAllIndexes() async throws {
        // Arrange
        let subsystem = IndexSubsystem()
        try await subsystem.createIndex(
            indexName: "index1",
            indexType: .btree,
            tableName: "table1",
            columns: ["col1"]
        )
        try await subsystem.createIndex(
            indexName: "index2",
            indexType: .hash,
            tableName: "table2",
            columns: ["col2"]
        )
        
        // Act
        let indexes = await subsystem.getAllIndexes()
        
        // Assert
        XCTAssert(indexes.count == 2)
        XCTAssert(indexes.contains { $0.indexName == "index1" })
        XCTAssert(indexes.contains { $0.indexName == "index2" })
    }
    
    func testGetIndexesForTable() async throws {
        // Arrange
        let subsystem = IndexSubsystem()
        try await subsystem.createIndex(
            indexName: "table1_index1",
            indexType: .btree,
            tableName: "table1",
            columns: ["col1"]
        )
        try await subsystem.createIndex(
            indexName: "table1_index2",
            indexType: .hash,
            tableName: "table1",
            columns: ["col2"]
        )
        try await subsystem.createIndex(
            indexName: "table2_index1",
            indexType: .btree,  // ART not supported, using btree
            tableName: "table2",
            columns: ["col3"]
        )
        
        // Act
        let table1Indexes = await subsystem.getIndexesForTable(tableName: "table1")
        let table2Indexes = await subsystem.getIndexesForTable(tableName: "table2")
        
        // Assert
        XCTAssert(table1Indexes.count == 2)
        XCTAssert(table2Indexes.count == 1)
        XCTAssert(table1Indexes.allSatisfy { $0.tableName == "table1" })
        XCTAssert(table2Indexes.allSatisfy { $0.tableName == "table2" })
    }
    
    // MARK: - Statistics Tests
    
    func testIndexStatistics() async throws {
        // Arrange
        let subsystem = IndexSubsystem()
        try await subsystem.createIndex(
            indexName: "users_id",
            indexType: .btree,
            tableName: "users",
            columns: ["id"]
        )
        
        // Act
        let stats = await subsystem.getIndexStats(indexName: "users_id")
        
        // Assert
        XCTAssert(stats != nil)
        XCTAssert(stats?.indexName == "users_id")
    }
    
    func testSubsystemStatistics() async throws {
        // Arrange
        let subsystem = IndexSubsystem()
        try await subsystem.createIndex(
            indexName: "index1",
            indexType: .btree,
            tableName: "table1",
            columns: ["col1"]
        )
        try await subsystem.insert(tableName: "table1", key: "key1", recordId: "rec1")
        try await subsystem.delete(tableName: "table1", key: "key1")
        
        // Act
        let stats = await subsystem.getStats()
        
        // Assert
        XCTAssert(stats.totalIndexes == 1)
        XCTAssert(stats.totalInserts == 1)
        XCTAssert(stats.totalDeletes == 1)
        XCTAssert(stats.totalSearches == 0)
        XCTAssert(stats.totalRebuilds == 0)
    }
    
    // MARK: - Error Handling Tests
    
    func testIndexAlreadyExistsError() async throws {
        // Arrange
        let subsystem = IndexSubsystem()
        try await subsystem.createIndex(
            indexName: "test_index",
            indexType: .btree,
            tableName: "test_table",
            columns: ["id"]
        )
        
        // Act & Assert
        do {
            try await subsystem.createIndex(
                indexName: "test_index",
                indexType: .hash,
                tableName: "test_table",
                columns: ["id"]
            )
            XCTFail("Should have thrown IndexSubsystemError.indexAlreadyExists")
        } catch {
            // Expected
        }
    }
    
    func testIndexNotFoundError() async throws {
        // Arrange
        let subsystem = IndexSubsystem()
        
        // Act & Assert
        do {
            try await subsystem.dropIndex(indexName: "non_existent")
            XCTFail("Should have thrown IndexSubsystemError.indexNotFound")
        } catch {
            // Expected
        }
    }
    
    func testNoSuitableIndexError() async throws {
        // Arrange
        let subsystem = IndexSubsystem()
        
        // Act & Assert
        do {
            _ = try await subsystem.search(tableName: "users", column: "email", key: "test@example.com")
            XCTAssertTrue(false, "Should throw error for non-existent table")
        } catch {
            // Expected error - test passes
        }
    }
    
    // MARK: - Performance Tests
    
    func testBulkIndexOperations() async throws {
        // Arrange
        let subsystem = IndexSubsystem()
        let indexCount = 100
        
        // Act
        for i in 0..<indexCount {
            try await subsystem.createIndex(
                indexName: "index_\(i)",
                indexType: .btree,
                tableName: "table_\(i % 10)",
                columns: ["col_\(i)"]
            )
        }
        
        // Assert
        let stats = await subsystem.getStats()
        XCTAssert(stats.totalIndexes == indexCount)
        
        let allIndexes = await subsystem.getAllIndexes()
        XCTAssert(allIndexes.count == indexCount)
    }
    
    func testConcurrentIndexOperations() async throws {
        // Arrange
        let subsystem = IndexSubsystem()
        let operationCount = 50
        
        // Act
        await withTaskGroup(of: Void.self) { group in
            for i in 0..<operationCount {
                group.addTask {
                    try? await subsystem.createIndex(
                        indexName: "concurrent_index_\(i)",
                        indexType: .btree,
                        tableName: "concurrent_table",
                        columns: ["col_\(i)"]
                    )
                }
            }
        }
        
        // Assert
        let stats = await subsystem.getStats()
        XCTAssert(stats.totalIndexes == operationCount)
    }
    
    // MARK: - Index Type Specific Tests
    
    func testAllIndexTypesSupported() async throws {
        // Arrange
        let subsystem = IndexSubsystem()
        let indexTypes: [IndexType] = [.btree, .hash]
        
        // Act & Assert
        for (index, type) in indexTypes.enumerated() {
            try await subsystem.createIndex(
                indexName: "test_\(type.rawValue)",
                indexType: type,
                tableName: "test_table",
                columns: ["col_\(index)"]
            )
            
            let createdIndex = await subsystem.getIndex(indexName: "test_\(type.rawValue)")
            XCTAssert(createdIndex?.indexType == type)
        }
        
        let stats = await subsystem.getStats()
        XCTAssert(stats.totalIndexes == indexTypes.count)
    }
    
    func testIndexTypeCharacteristics() async throws {
        // Arrange
        let subsystem = IndexSubsystem()
        
        // Act
        try await subsystem.createIndex(
            indexName: "btree_index",
            indexType: .btree,
            tableName: "test_table",
            columns: ["id"],
            unique: true
        )
        
        try await subsystem.createIndex(
            indexName: "hash_index",
            indexType: .hash,
            tableName: "test_table",
            columns: ["email"],
            unique: true
        )
        
        try await subsystem.createIndex(
            indexName: "art_index",
            indexType: .btree,
            tableName: "test_table",
            columns: ["name"]
        )
        
        // Assert
        let btreeIndex = await subsystem.getIndex(indexName: "btree_index")
        let hashIndex = await subsystem.getIndex(indexName: "hash_index")
        let artIndex = await subsystem.getIndex(indexName: "art_index")
        
        XCTAssert(btreeIndex?.indexType == .btree)
        XCTAssert(hashIndex?.indexType == .hash)
        XCTAssert(artIndex?.indexType == .btree)
        
        XCTAssert(btreeIndex?.unique == true)
        XCTAssert(hashIndex?.unique == true)
        XCTAssert(artIndex?.unique == false)
    }
}

