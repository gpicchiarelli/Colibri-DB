//
//  MultiDatabaseCatalogTests.swift
//  ColibrìDB - Multi-Database Catalog Tests
//
//  Tests for multi-database management and catalog operations
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//

import XCTest
@testable import ColibriCore

/// Tests for the Multi-Database Catalog
/// Covers database creation, deletion, switching, and metadata management
final class MultiDatabaseCatalogTests {
    
    // MARK: - Setup
    
    func testMultiDatabaseCatalogCreation() async throws {
        // Arrange & Act
        let catalog = MultiDatabaseCatalog()
        
        // Assert
        XCTAssert(catalog != nil)
        let currentDB = await catalog.getCurrentDatabase()
        XCTAssert(currentDB == "system")
        
        let databases = await catalog.listDatabases()
        XCTAssert(databases.contains("system"))
    }
    
    // MARK: - Database Creation Tests
    
    func testCreateDatabase() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        
        // Act
        try await catalog.createDatabase(name: "test_db", owner: "test_user")
        
        // Assert
        let databases = await catalog.listDatabases()
        XCTAssert(databases.contains("test_db"))
        
        let dbInfo = await catalog.getDatabaseInfo(name: "test_db")
        XCTAssert(dbInfo != nil)
        XCTAssert(dbInfo?.name == "test_db")
        XCTAssert(dbInfo?.owner == "test_user")
    }
    
    func testCreateMultipleDatabases() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        
        // Act
        try await catalog.createDatabase(name: "db1", owner: "user1")
        try await catalog.createDatabase(name: "db2", owner: "user2")
        try await catalog.createDatabase(name: "db3", owner: "user3")
        
        // Assert
        let databases = await catalog.listDatabases()
        XCTAssert(databases.contains("db1"))
        XCTAssert(databases.contains("db2"))
        XCTAssert(databases.contains("db3"))
        XCTAssert(databases.contains("system"))
        XCTAssert(databases.count == 4)
    }
    
    func testCreateDatabaseWithCustomEncoding() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        
        // Act
        try await catalog.createDatabase(name: "utf8_db", owner: "admin")
        
        // Assert
        let dbInfo = await catalog.getDatabaseInfo(name: "utf8_db")
        XCTAssert(dbInfo?.encoding == "UTF8")
        XCTAssert(dbInfo?.collation == "en_US.UTF-8")
    }
    
    func testCreateDuplicateDatabaseFails() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        try await catalog.createDatabase(name: "test_db", owner: "test_user")
        
        // Act & Assert
        do {
            try await catalog.createDatabase(name: "test_db", owner: "another_user")
        }
    }
    
    // MARK: - Database Deletion Tests
    
    func testDropDatabase() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        try await catalog.createDatabase(name: "test_db", owner: "test_user")
        
        // Act
        try await catalog.dropDatabase(name: "test_db")
        
        // Assert
        let databases = await catalog.listDatabases()
        XCTAssert(!databases.contains("test_db"))
        XCTAssert(databases.contains("system"))
        
        let dbInfo = await catalog.getDatabaseInfo(name: "test_db")
        XCTAssert(dbInfo == nil)
    }
    
    func testDropNonExistentDatabaseFails() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        
        // Act & Assert
        do {
            try await catalog.dropDatabase(name: "non_existent")
        }
    }
    
    func testDropSystemDatabaseFails() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        
        // Act & Assert
        do {
            try await catalog.dropDatabase(name: "system")
            XCTFail("Should have thrown error")
        } catch {
            // Expected
        }
    }
    
    func testDropCurrentDatabaseSwitchesToSystem() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        try await catalog.createDatabase(name: "test_db", owner: "test_user")
        try await catalog.switchDatabase(name: "test_db")
        
        let currentBefore = await catalog.getCurrentDatabase()
        XCTAssert(currentBefore == "test_db")
        
        // Act
        try await catalog.dropDatabase(name: "test_db")
        
        // Assert
        let currentAfter = await catalog.getCurrentDatabase()
        XCTAssert(currentAfter == "system")
    }
    
    // MARK: - Database Switching Tests
    
    func testSwitchDatabase() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        try await catalog.createDatabase(name: "test_db", owner: "test_user")
        
        // Act
        try await catalog.switchDatabase(name: "test_db")
        
        // Assert
        let currentDB = await catalog.getCurrentDatabase()
        XCTAssert(currentDB == "test_db")
    }
    
    func testSwitchToNonExistentDatabaseFails() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        
        // Act & Assert
        do {
            try await catalog.switchDatabase(name: "non_existent")
        }
    }
    
    func testSwitchBetweenDatabases() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        try await catalog.createDatabase(name: "db1", owner: "user1")
        try await catalog.createDatabase(name: "db2", owner: "user2")
        
        // Act & Assert
        try await catalog.switchDatabase(name: "db1")
        var currentDB = await catalog.getCurrentDatabase()
        XCTAssert(currentDB == "db1")
        
        try await catalog.switchDatabase(name: "db2")
        currentDB = await catalog.getCurrentDatabase()
        XCTAssert(currentDB == "db2")
        
        try await catalog.switchDatabase(name: "system")
        currentDB = await catalog.getCurrentDatabase()
        XCTAssert(currentDB == "system")
    }
    
    // MARK: - Database Information Tests
    
    func testGetDatabaseInfo() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        try await catalog.createDatabase(name: "test_db", owner: "test_user")
        
        // Act
        let dbInfo = await catalog.getDatabaseInfo(name: "test_db")
        
        // Assert
        XCTAssert(dbInfo != nil)
        XCTAssert(dbInfo?.name == "test_db")
        XCTAssert(dbInfo?.owner == "test_user")
        XCTAssert(dbInfo?.encoding == "UTF8")
        XCTAssert(dbInfo?.collation == "en_US.UTF-8")
        XCTAssert(dbInfo?.createdAt != nil)
    }
    
    func testGetNonExistentDatabaseInfo() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        
        // Act
        let dbInfo = await catalog.getDatabaseInfo(name: "non_existent")
        
        // Assert
        XCTAssert(dbInfo == nil)
    }
    
    func testGetSystemDatabaseInfo() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        
        // Act
        let dbInfo = await catalog.getDatabaseInfo(name: "system")
        
        // Assert
        XCTAssert(dbInfo != nil)
        XCTAssert(dbInfo?.name == "system")
        XCTAssert(dbInfo?.owner == "admin")
    }
    
    // MARK: - Database Listing Tests
    
    func testListDatabases() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        try await catalog.createDatabase(name: "db1", owner: "user1")
        try await catalog.createDatabase(name: "db2", owner: "user2")
        try await catalog.createDatabase(name: "db3", owner: "user3")
        
        // Act
        let databases = await catalog.listDatabases()
        
        // Assert
        XCTAssert(databases.count == 4) // system + 3 created
        XCTAssert(databases.contains("system"))
        XCTAssert(databases.contains("db1"))
        XCTAssert(databases.contains("db2"))
        XCTAssert(databases.contains("db3"))
    }
    
    func testListDatabasesAfterDrop() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        try await catalog.createDatabase(name: "db1", owner: "user1")
        try await catalog.createDatabase(name: "db2", owner: "user2")
        try await catalog.createDatabase(name: "db3", owner: "user3")
        
        // Act
        try await catalog.dropDatabase(name: "db2")
        let databases = await catalog.listDatabases()
        
        // Assert
        XCTAssert(databases.count == 3) // system + 2 remaining
        XCTAssert(databases.contains("system"))
        XCTAssert(databases.contains("db1"))
        XCTAssert(!databases.contains("db2"))
        XCTAssert(databases.contains("db3"))
    }
    
    // MARK: - Current Database Tests
    
    func testGetCurrentDatabase() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        
        // Act
        let currentDB = await catalog.getCurrentDatabase()
        
        // Assert
        XCTAssert(currentDB == "system")
    }
    
    func testCurrentDatabaseAfterOperations() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        
        // Act & Assert
        var currentDB = await catalog.getCurrentDatabase()
        XCTAssert(currentDB == "system")
        
        try await catalog.createDatabase(name: "test_db", owner: "test_user")
        currentDB = await catalog.getCurrentDatabase()
        XCTAssert(currentDB == "system") // Should not change
        
        try await catalog.switchDatabase(name: "test_db")
        currentDB = await catalog.getCurrentDatabase()
        XCTAssert(currentDB == "test_db")
        
        try await catalog.dropDatabase(name: "test_db")
        currentDB = await catalog.getCurrentDatabase()
        XCTAssert(currentDB == "system") // Should switch back to system
    }
    
    // MARK: - Database Metadata Tests
    
    func testDatabaseMetadata() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        let startTime = Date()
        
        // Act
        try await catalog.createDatabase(name: "metadata_test", owner: "metadata_user")
        let dbInfo = await catalog.getDatabaseInfo(name: "metadata_test")
        let endTime = Date()
        
        // Assert
        XCTAssert(dbInfo != nil)
        XCTAssert(dbInfo?.name == "metadata_test")
        XCTAssert(dbInfo?.owner == "metadata_user")
        XCTAssert(dbInfo?.encoding == "UTF8")
        XCTAssert(dbInfo?.collation == "en_US.UTF-8")
        if let createdAt = dbInfo?.createdAt {
            XCTAssert(createdAt >= startTime)
            XCTAssert(createdAt <= endTime)
        } else {
            XCTFail("Database info should have createdAt date")
        }
    }
    
    func testDatabaseOwnership() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        
        // Act
        try await catalog.createDatabase(name: "user1_db", owner: "user1")
        try await catalog.createDatabase(name: "user2_db", owner: "user2")
        try await catalog.createDatabase(name: "admin_db", owner: "admin")
        
        // Assert
        let user1DB = await catalog.getDatabaseInfo(name: "user1_db")
        let user2DB = await catalog.getDatabaseInfo(name: "user2_db")
        let adminDB = await catalog.getDatabaseInfo(name: "admin_db")
        
        XCTAssert(user1DB?.owner == "user1")
        XCTAssert(user2DB?.owner == "user2")
        XCTAssert(adminDB?.owner == "admin")
    }
    
    // MARK: - Error Handling Tests
    
    func testDatabaseErrorTypes() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        
        // Act & Assert - Duplicate error
        try await catalog.createDatabase(name: "test_db", owner: "user1")
        do {
            try await catalog.createDatabase(name: "test_db", owner: "user2")
        }
        
        // Act & Assert - Not found error
        do {
            try await catalog.dropDatabase(name: "non_existent")
            XCTFail("Should have thrown DBError.notFound")
        } catch {
            // Expected
        }
        
        do {
            try await catalog.switchDatabase(name: "non_existent")
            XCTFail("Should have thrown DBError.notFound")
        } catch {
            // Expected
        }
        
        // Act & Assert - Internal error
        do {
            try await catalog.dropDatabase(name: "system")
            XCTFail("Should have thrown error")
        } catch {
            // Expected
        }
    }
    
    // MARK: - Concurrent Operations Tests
    
    func testConcurrentDatabaseCreation() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        let dbCount = 10
        
        // Act
        await withTaskGroup(of: Void.self) { group in
            for i in 0..<dbCount {
                group.addTask {
                    try? await catalog.createDatabase(name: "concurrent_db_\(i)", owner: "user_\(i)")
                }
            }
        }
        
        // Assert
        let databases = await catalog.listDatabases()
        XCTAssert(databases.count >= dbCount + 1) // +1 for system database
    }
    
    func testConcurrentDatabaseOperations() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        
        // Act
        await withTaskGroup(of: Void.self) { group in
            // Create databases
            for i in 0..<5 {
                group.addTask {
                    try? await catalog.createDatabase(name: "concurrent_\(i)", owner: "user_\(i)")
                }
            }
            
            // Switch databases
            group.addTask {
                try? await catalog.switchDatabase(name: "system")
            }
        }
        
        // Assert
        let databases = await catalog.listDatabases()
        XCTAssert(databases.count >= 6) // system + created databases
    }
    
    // MARK: - Edge Cases Tests
    
    func testEmptyDatabaseName() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        
        // Act & Assert
        do {
            try await catalog.switchDatabase(name: "")
            XCTFail("Should have thrown error")
        } catch {
            // Expected
        }
        
        do {
            try await catalog.dropDatabase(name: "")
        }
    }
    
    func testSystemDatabaseOperations() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        
        // Act & Assert
        // System database should exist and be accessible
        let systemDB = await catalog.getDatabaseInfo(name: "system")
        XCTAssert(systemDB != nil)
        XCTAssert(systemDB?.name == "system")
        XCTAssert(systemDB?.owner == "admin")
        
        // Should be able to switch to system database
        try await catalog.switchDatabase(name: "system")
        let currentDB = await catalog.getCurrentDatabase()
        XCTAssert(currentDB == "system")
    }
    
    func testDatabaseNameCaseSensitivity() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        
        // Act
        try await catalog.createDatabase(name: "TestDB", owner: "user1")
        try await catalog.createDatabase(name: "testdb", owner: "user2")
        
        // Assert
        let databases = await catalog.listDatabases()
        XCTAssert(databases.contains("TestDB"))
        XCTAssert(databases.contains("testdb"))
        XCTAssert(databases.count == 3) // system + 2 created
    }
    
    // MARK: - Performance Tests
    
    func testBulkDatabaseOperations() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        let dbCount = 100
        
        // Act
        for i in 0..<dbCount {
            try await catalog.createDatabase(name: "bulk_db_\(i)", owner: "user_\(i)")
        }
        
        // Assert
        let databases = await catalog.listDatabases()
        XCTAssert(databases.count == dbCount + 1) // +1 for system
        
        // Test switching to each database
        for i in 0..<dbCount {
            try await catalog.switchDatabase(name: "bulk_db_\(i)")
            let currentDB = await catalog.getCurrentDatabase()
            XCTAssert(currentDB == "bulk_db_\(i)")
        }
    }
    
    func testDatabaseCreationPerformance() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        let startTime = Date()
        
        // Act
        for i in 0..<50 {
            try await catalog.createDatabase(name: "perf_db_\(i)", owner: "user_\(i)")
        }
        
        // Assert
        let endTime = Date()
        let duration = endTime.timeIntervalSince(startTime)
        
        let databases = await catalog.listDatabases()
        XCTAssert(databases.count == 51) // 50 + system
        
        // Performance assertion (should complete in reasonable time)
        XCTAssert(duration < 5.0) // 5 seconds max
    }
    
    // MARK: - Integration Tests
    
    func testCompleteDatabaseLifecycle() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        
        // Act & Assert - Create
        try await catalog.createDatabase(name: "lifecycle_db", owner: "lifecycle_user")
        var databases = await catalog.listDatabases()
        XCTAssert(databases.contains("lifecycle_db"))
        
        // Act & Assert - Switch
        try await catalog.switchDatabase(name: "lifecycle_db")
        var currentDB = await catalog.getCurrentDatabase()
        XCTAssert(currentDB == "lifecycle_db")
        
        // Act & Assert - Get info
        let dbInfo = await catalog.getDatabaseInfo(name: "lifecycle_db")
        XCTAssert(dbInfo?.name == "lifecycle_db")
        XCTAssert(dbInfo?.owner == "lifecycle_user")
        
        // Act & Assert - Drop
        try await catalog.dropDatabase(name: "lifecycle_db")
        databases = await catalog.listDatabases()
        XCTAssert(!databases.contains("lifecycle_db"))
        
        // Act & Assert - Current should switch back to system
        currentDB = await catalog.getCurrentDatabase()
        XCTAssert(currentDB == "system")
    }
    
    func testMultipleDatabaseWorkflow() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        
        // Act & Assert - Create multiple databases
        try await catalog.createDatabase(name: "app_db", owner: "app_user")
        try await catalog.createDatabase(name: "analytics_db", owner: "analytics_user")
        try await catalog.createDatabase(name: "logs_db", owner: "logs_user")
        
        // Act & Assert - Switch between them
        try await catalog.switchDatabase(name: "app_db")
        let current1 = await catalog.getCurrentDatabase()
        XCTAssertEqual(current1, "app_db")
        
        try await catalog.switchDatabase(name: "analytics_db")
        let current2 = await catalog.getCurrentDatabase()
        XCTAssertEqual(current2, "analytics_db")
        
        try await catalog.switchDatabase(name: "logs_db")
        let current3 = await catalog.getCurrentDatabase()
        XCTAssertEqual(current3, "logs_db")
        
        // Act & Assert - Drop one, others remain
        try await catalog.dropDatabase(name: "analytics_db")
        let databases = await catalog.listDatabases()
        XCTAssert(databases.contains("app_db"))
        XCTAssert(!databases.contains("analytics_db"))
        XCTAssert(databases.contains("logs_db"))
        XCTAssert(databases.contains("system"))
        
        // Act & Assert - Current should remain on logs_db
        let current = await catalog.getCurrentDatabase()
        XCTAssertEqual(current, "logs_db")
    }
}
