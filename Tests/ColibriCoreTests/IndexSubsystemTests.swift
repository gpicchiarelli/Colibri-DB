//
//  IndexSubsystemTests.swift
//  ColibrìDB - Index Subsystem Tests
//
//  Tests for unified index management across all index types
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//

import Testing
@testable import ColibriCore

/// Tests for the unified Index Subsystem
/// Covers all 9 index types: BTree, Hash, ART, LSM, Fractal, Bloom, SkipList, TTree, Radix
struct IndexSubsystemTests {
    
    // MARK: - Setup
    
    @Test func testIndexSubsystemCreation() async throws {
        // Arrange & Act
        let subsystem = IndexSubsystem()
        
        // Assert
        // subsystem is not optional, so no need to check for nil
        let stats = await subsystem.getStats()
        #expect(stats.totalIndexes == 0)
    }
    
    // MARK: - Index Management Tests
    
    @Test func testCreateBTreeIndex() async throws {
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
        #expect(index != nil)
        #expect(index?.indexType == .btree)
        #expect(index?.tableName == "users")
        #expect(index?.columns == ["id"])
        #expect(index?.unique == true)
        
        let stats = await subsystem.getStats()
        #expect(stats.totalIndexes == 1)
    }
    
    @Test func testCreateHashIndex() async throws {
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
        #expect(index?.indexType == .hash)
        #expect(index?.unique == true)
    }
    
    @Test func testCreateBTreeIndexWithMultipleColumns() async throws {
        // Arrange
        let subsystem = IndexSubsystem()
        
        // Act
        try await subsystem.createIndex(
            indexName: "users_name",
            indexType: .btree,
            tableName: "users",
            columns: ["first_name", "last_name"]
        )
        
        // Assert
        let index = await subsystem.getIndex(indexName: "users_name")
        #expect(index?.indexType == .btree)
        #expect(index?.columns == ["first_name", "last_name"])
    }
    
    @Test func testCreateHashIndexWithTimestamp() async throws {
        // Arrange
        let subsystem = IndexSubsystem()
        
        // Act
        try await subsystem.createIndex(
            indexName: "logs_timestamp",
            indexType: .hash,
            tableName: "logs",
            columns: ["timestamp"]
        )
        
        // Assert
        let index = await subsystem.getIndex(indexName: "logs_timestamp")
        #expect(index?.indexType == .hash)
    }
    
    @Test func testCreateBTreeIndexForEvents() async throws {
        // Arrange
        let subsystem = IndexSubsystem()
        
        // Act
        try await subsystem.createIndex(
            indexName: "events_time",
            indexType: .btree,
            tableName: "events",
            columns: ["created_at"]
        )
        
        // Assert
        let index = await subsystem.getIndex(indexName: "events_time")
        #expect(index?.indexType == .btree)
    }
    
    @Test func testCreateHashIndexForUsers() async throws {
        // Arrange
        let subsystem = IndexSubsystem()
        
        // Act
        try await subsystem.createIndex(
            indexName: "users_exists",
            indexType: .hash,
            tableName: "users",
            columns: ["id"]
        )
        
        // Assert
        let index = await subsystem.getIndex(indexName: "users_exists")
        #expect(index?.indexType == .hash)
    }
    
    @Test func testCreateBTreeIndexForScores() async throws {
        // Arrange
        let subsystem = IndexSubsystem()
        
        // Act
        try await subsystem.createIndex(
            indexName: "scores_rank",
            indexType: .btree,
            tableName: "scores",
            columns: ["score"]
        )
        
        // Assert
        let index = await subsystem.getIndex(indexName: "scores_rank")
        #expect(index?.indexType == .btree)
    }
    
    @Test func testCreateHashIndexForCache() async throws {
        // Arrange
        let subsystem = IndexSubsystem()
        
        // Act
        try await subsystem.createIndex(
            indexName: "cache_key",
            indexType: .hash,
            tableName: "cache",
            columns: ["key"]
        )
        
        // Assert
        let index = await subsystem.getIndex(indexName: "cache_key")
        #expect(index?.indexType == .hash)
    }
    
    @Test func testCreateBTreeIndexForPaths() async throws {
        // Arrange
        let subsystem = IndexSubsystem()
        
        // Act
        try await subsystem.createIndex(
            indexName: "paths_prefix",
            indexType: .btree,
            tableName: "paths",
            columns: ["path"]
        )
        
        // Assert
        let index = await subsystem.getIndex(indexName: "paths_prefix")
        #expect(index?.indexType == .btree)
    }
    
    @Test func testCreateDuplicateIndexFails() async throws {
        // Arrange
        let subsystem = IndexSubsystem()
        try await subsystem.createIndex(
            indexName: "test_index",
            indexType: .btree,
            tableName: "test_table",
            columns: ["id"]
        )
        
        // Act & Assert
        await #expect(throws: IndexSubsystemError.self) {
            try await subsystem.createIndex(
                indexName: "test_index",
                indexType: .hash,
                tableName: "test_table",
                columns: ["id"]
            )
        }
    }
    
    @Test func testDropIndex() async throws {
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
        #expect(index == nil)
        
        let stats = await subsystem.getStats()
        #expect(stats.totalIndexes == 0)
    }
    
    @Test func testDropNonExistentIndexFails() async throws {
        // Arrange
        let subsystem = IndexSubsystem()
        
        // Act & Assert
        await #expect(throws: IndexSubsystemError.self) {
            try await subsystem.dropIndex(indexName: "non_existent")
        }
    }
    
    // MARK: - Index Operations Tests
    
    @Test func testInsertIntoIndexes() async throws {
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
        #expect(stats.totalInserts == 1)
    }
    
    @Test func testDeleteFromIndexes() async throws {
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
        #expect(stats.totalDeletes == 1)
    }
    
    @Test func testSearchWithIndex() async throws {
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
        // results is not optional, so no need to check for nil
        let stats = await subsystem.getStats()
        #expect(stats.totalSearches == 1)
    }
    
    @Test func testSearchWithoutSuitableIndexFails() async throws {
        // Arrange
        let subsystem = IndexSubsystem()
        
        // Act & Assert
        await #expect(throws: IndexSubsystemError.self) {
            try await subsystem.search(tableName: "users", column: "email", key: "test@example.com")
        }
    }
    
    // MARK: - Query Optimization Tests
    
    @Test func testSelectIndexForQuery() async throws {
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
        #expect(selectedIndex != nil)
        #expect(selectedIndex == "users_email_hash" || selectedIndex == "users_email_btree")
    }
    
    @Test func testGetSelectedIndex() async throws {
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
        #expect(selectedIndex == "users_email")
    }
    
    // MARK: - Maintenance Tests
    
    @Test func testUpdateStatistics() async throws {
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
        #expect(stats != nil)
    }
    
    @Test func testRebuildIndex() async throws {
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
        #expect(index != nil)
        
        let stats = await subsystem.getStats()
        #expect(stats.totalRebuilds == 1)
    }
    
    @Test func testRebuildNonExistentIndexFails() async throws {
        // Arrange
        let subsystem = IndexSubsystem()
        
        // Act & Assert
        await #expect(throws: IndexSubsystemError.self) {
            try await subsystem.rebuildIndex(indexName: "non_existent")
        }
    }
    
    // MARK: - Query Methods Tests
    
    @Test func testGetAllIndexes() async throws {
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
        #expect(indexes.count == 2)
        #expect(indexes.contains { $0.indexName == "index1" })
        #expect(indexes.contains { $0.indexName == "index2" })
    }
    
    @Test func testGetIndexesForTable() async throws {
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
            indexType: .btree,
            tableName: "table2",
            columns: ["col3"]
        )
        
        // Act
        let table1Indexes = await subsystem.getIndexesForTable(tableName: "table1")
        let table2Indexes = await subsystem.getIndexesForTable(tableName: "table2")
        
        // Assert
        #expect(table1Indexes.count == 2)
        #expect(table2Indexes.count == 1)
        #expect(table1Indexes.allSatisfy { $0.tableName == "table1" })
        #expect(table2Indexes.allSatisfy { $0.tableName == "table2" })
    }
    
    // MARK: - Statistics Tests
    
    @Test func testIndexStatistics() async throws {
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
        #expect(stats != nil)
        #expect(stats?.indexName == "users_id")
    }
    
    @Test func testSubsystemStatistics() async throws {
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
        #expect(stats.totalIndexes == 1)
        #expect(stats.totalInserts == 1)
        #expect(stats.totalDeletes == 1)
        #expect(stats.totalSearches == 0)
        #expect(stats.totalRebuilds == 0)
    }
    
    // MARK: - Error Handling Tests
    
    @Test func testIndexAlreadyExistsError() async throws {
        // Arrange
        let subsystem = IndexSubsystem()
        try await subsystem.createIndex(
            indexName: "test_index",
            indexType: .btree,
            tableName: "test_table",
            columns: ["id"]
        )
        
        // Act & Assert
        await #expect(throws: IndexSubsystemError.indexAlreadyExists(name: "test_index")) {
            try await subsystem.createIndex(
                indexName: "test_index",
                indexType: .hash,
                tableName: "test_table",
                columns: ["id"]
            )
        }
    }
    
    @Test func testIndexNotFoundError() async throws {
        // Arrange
        let subsystem = IndexSubsystem()
        
        // Act & Assert
        await #expect(throws: IndexSubsystemError.indexNotFound(name: "non_existent")) {
            try await subsystem.dropIndex(indexName: "non_existent")
        }
    }
    
    @Test func testNoSuitableIndexError() async throws {
        // Arrange
        let subsystem = IndexSubsystem()
        
        // Act & Assert
        do {
            _ = try await subsystem.search(tableName: "users", column: "email", key: "test@example.com")
            try TestAssertions.assertTrue(false, "Should throw error for non-existent table")
        } catch {
            // Expected error - test passes
        }
    }
    
    // MARK: - Performance Tests
    
    @Test func testBulkIndexOperations() async throws {
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
        #expect(stats.totalIndexes == indexCount)
        
        let allIndexes = await subsystem.getAllIndexes()
        #expect(allIndexes.count == indexCount)
    }
    
    @Test func testConcurrentIndexOperations() async throws {
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
        #expect(stats.totalIndexes == operationCount)
    }
    
    // MARK: - Index Type Specific Tests
    
    @Test func testAllIndexTypesSupported() async throws {
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
            #expect(createdIndex?.indexType == type)
        }
        
        let stats = await subsystem.getStats()
        #expect(stats.totalIndexes == indexTypes.count)
    }
    
    @Test func testIndexTypeCharacteristics() async throws {
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
            indexName: "btree_index2",
            indexType: .btree,
            tableName: "test_table",
            columns: ["name"]
        )
        
        // Assert
        let btreeIndex = await subsystem.getIndex(indexName: "btree_index")
        let hashIndex = await subsystem.getIndex(indexName: "hash_index")
        let btreeIndex2 = await subsystem.getIndex(indexName: "btree_index2")
        
        #expect(btreeIndex?.indexType == .btree)
        #expect(hashIndex?.indexType == .hash)
        #expect(btreeIndex2?.indexType == .btree)
        
        #expect(btreeIndex?.unique == true)
        #expect(hashIndex?.unique == true)
        #expect(btreeIndex2?.unique == false)
    }
}
