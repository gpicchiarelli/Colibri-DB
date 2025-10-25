//
//  MultiDatabaseCatalogTests.swift
//  ColibrìDB - Multi-Database Catalog Tests
//
//  Tests for multi-database management and catalog operations
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//

import Testing
@testable import ColibriCore

/// Tests for the Multi-Database Catalog
/// Covers database creation, deletion, switching, and metadata management
struct MultiDatabaseCatalogTests {
    
    // MARK: - Setup
    
    @Test func testMultiDatabaseCatalogCreation() async throws {
        // Arrange & Act
        let catalog = MultiDatabaseCatalog()
        
        // Assert
        #expect(catalog != nil)
        let currentDB = await catalog.getCurrentDatabase()
        #expect(currentDB == "system")
        
        let databases = await catalog.listDatabases()
        #expect(databases.contains("system"))
    }
    
    // MARK: - Database Creation Tests
    
    @Test func testCreateDatabase() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        
        // Act
        try await catalog.createDatabase(name: "test_db", owner: "test_user")
        
        // Assert
        let databases = await catalog.listDatabases()
        #expect(databases.contains("test_db"))
        
        let dbInfo = await catalog.getDatabaseInfo(name: "test_db")
        #expect(dbInfo != nil)
        #expect(dbInfo?.name == "test_db")
        #expect(dbInfo?.owner == "test_user")
    }
    
    @Test func testCreateMultipleDatabases() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        
        // Act
        try await catalog.createDatabase(name: "db1", owner: "user1")
        try await catalog.createDatabase(name: "db2", owner: "user2")
        try await catalog.createDatabase(name: "db3", owner: "user3")
        
        // Assert
        let databases = await catalog.listDatabases()
        #expect(databases.contains("db1"))
        #expect(databases.contains("db2"))
        #expect(databases.contains("db3"))
        #expect(databases.contains("system"))
        #expect(databases.count == 4)
    }
    
    @Test func testCreateDatabaseWithCustomEncoding() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        
        // Act
        try await catalog.createDatabase(name: "utf8_db", owner: "admin")
        
        // Assert
        let dbInfo = await catalog.getDatabaseInfo(name: "utf8_db")
        #expect(dbInfo?.encoding == "UTF8")
        #expect(dbInfo?.collation == "en_US.UTF-8")
    }
    
    @Test func testCreateDuplicateDatabaseFails() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        try await catalog.createDatabase(name: "test_db", owner: "test_user")
        
        // Act & Assert
        await #expect(throws: DBError.duplicate) {
            try await catalog.createDatabase(name: "test_db", owner: "another_user")
        }
    }
    
    // MARK: - Database Deletion Tests
    
    @Test func testDropDatabase() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        try await catalog.createDatabase(name: "test_db", owner: "test_user")
        
        // Act
        try await catalog.dropDatabase(name: "test_db")
        
        // Assert
        let databases = await catalog.listDatabases()
        #expect(!databases.contains("test_db"))
        #expect(databases.contains("system"))
        
        let dbInfo = await catalog.getDatabaseInfo(name: "test_db")
        #expect(dbInfo == nil)
    }
    
    @Test func testDropNonExistentDatabaseFails() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        
        // Act & Assert
        await #expect(throws: DBError.notFound) {
            try await catalog.dropDatabase(name: "non_existent")
        }
    }
    
    @Test func testDropSystemDatabaseFails() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        
        // Act & Assert
        await #expect(throws: DBError.internalError("Cannot drop system database")) {
            try await catalog.dropDatabase(name: "system")
        }
    }
    
    @Test func testDropCurrentDatabaseSwitchesToSystem() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        try await catalog.createDatabase(name: "test_db", owner: "test_user")
        try await catalog.switchDatabase(name: "test_db")
        
        let currentBefore = await catalog.getCurrentDatabase()
        #expect(currentBefore == "test_db")
        
        // Act
        try await catalog.dropDatabase(name: "test_db")
        
        // Assert
        let currentAfter = await catalog.getCurrentDatabase()
        #expect(currentAfter == "system")
    }
    
    // MARK: - Database Switching Tests
    
    @Test func testSwitchDatabase() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        try await catalog.createDatabase(name: "test_db", owner: "test_user")
        
        // Act
        try await catalog.switchDatabase(name: "test_db")
        
        // Assert
        let currentDB = await catalog.getCurrentDatabase()
        #expect(currentDB == "test_db")
    }
    
    @Test func testSwitchToNonExistentDatabaseFails() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        
        // Act & Assert
        await #expect(throws: DBError.notFound) {
            try await catalog.switchDatabase(name: "non_existent")
        }
    }
    
    @Test func testSwitchBetweenDatabases() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        try await catalog.createDatabase(name: "db1", owner: "user1")
        try await catalog.createDatabase(name: "db2", owner: "user2")
        
        // Act & Assert
        try await catalog.switchDatabase(name: "db1")
        var currentDB = await catalog.getCurrentDatabase()
        #expect(currentDB == "db1")
        
        try await catalog.switchDatabase(name: "db2")
        currentDB = await catalog.getCurrentDatabase()
        #expect(currentDB == "db2")
        
        try await catalog.switchDatabase(name: "system")
        currentDB = await catalog.getCurrentDatabase()
        #expect(currentDB == "system")
    }
    
    // MARK: - Database Information Tests
    
    @Test func testGetDatabaseInfo() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        try await catalog.createDatabase(name: "test_db", owner: "test_user")
        
        // Act
        let dbInfo = await catalog.getDatabaseInfo(name: "test_db")
        
        // Assert
        #expect(dbInfo != nil)
        #expect(dbInfo?.name == "test_db")
        #expect(dbInfo?.owner == "test_user")
        #expect(dbInfo?.encoding == "UTF8")
        #expect(dbInfo?.collation == "en_US.UTF-8")
        #expect(dbInfo?.createdAt != nil)
    }
    
    @Test func testGetNonExistentDatabaseInfo() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        
        // Act
        let dbInfo = await catalog.getDatabaseInfo(name: "non_existent")
        
        // Assert
        #expect(dbInfo == nil)
    }
    
    @Test func testGetSystemDatabaseInfo() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        
        // Act
        let dbInfo = await catalog.getDatabaseInfo(name: "system")
        
        // Assert
        #expect(dbInfo != nil)
        #expect(dbInfo?.name == "system")
        #expect(dbInfo?.owner == "admin")
    }
    
    // MARK: - Database Listing Tests
    
    @Test func testListDatabases() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        try await catalog.createDatabase(name: "db1", owner: "user1")
        try await catalog.createDatabase(name: "db2", owner: "user2")
        try await catalog.createDatabase(name: "db3", owner: "user3")
        
        // Act
        let databases = await catalog.listDatabases()
        
        // Assert
        #expect(databases.count == 4) // system + 3 created
        #expect(databases.contains("system"))
        #expect(databases.contains("db1"))
        #expect(databases.contains("db2"))
        #expect(databases.contains("db3"))
    }
    
    @Test func testListDatabasesAfterDrop() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        try await catalog.createDatabase(name: "db1", owner: "user1")
        try await catalog.createDatabase(name: "db2", owner: "user2")
        try await catalog.createDatabase(name: "db3", owner: "user3")
        
        // Act
        try await catalog.dropDatabase(name: "db2")
        let databases = await catalog.listDatabases()
        
        // Assert
        #expect(databases.count == 3) // system + 2 remaining
        #expect(databases.contains("system"))
        #expect(databases.contains("db1"))
        #expect(!databases.contains("db2"))
        #expect(databases.contains("db3"))
    }
    
    // MARK: - Current Database Tests
    
    @Test func testGetCurrentDatabase() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        
        // Act
        let currentDB = await catalog.getCurrentDatabase()
        
        // Assert
        #expect(currentDB == "system")
    }
    
    @Test func testCurrentDatabaseAfterOperations() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        
        // Act & Assert
        var currentDB = await catalog.getCurrentDatabase()
        #expect(currentDB == "system")
        
        try await catalog.createDatabase(name: "test_db", owner: "test_user")
        currentDB = await catalog.getCurrentDatabase()
        #expect(currentDB == "system") // Should not change
        
        try await catalog.switchDatabase(name: "test_db")
        currentDB = await catalog.getCurrentDatabase()
        #expect(currentDB == "test_db")
        
        try await catalog.dropDatabase(name: "test_db")
        currentDB = await catalog.getCurrentDatabase()
        #expect(currentDB == "system") // Should switch back to system
    }
    
    // MARK: - Database Metadata Tests
    
    @Test func testDatabaseMetadata() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        let startTime = Date()
        
        // Act
        try await catalog.createDatabase(name: "metadata_test", owner: "metadata_user")
        let dbInfo = await catalog.getDatabaseInfo(name: "metadata_test")
        let endTime = Date()
        
        // Assert
        #expect(dbInfo != nil)
        #expect(dbInfo?.name == "metadata_test")
        #expect(dbInfo?.owner == "metadata_user")
        #expect(dbInfo?.encoding == "UTF8")
        #expect(dbInfo?.collation == "en_US.UTF-8")
        #expect(dbInfo?.createdAt >= startTime)
        #expect(dbInfo?.createdAt <= endTime)
    }
    
    @Test func testDatabaseOwnership() async throws {
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
        
        #expect(user1DB?.owner == "user1")
        #expect(user2DB?.owner == "user2")
        #expect(adminDB?.owner == "admin")
    }
    
    // MARK: - Error Handling Tests
    
    @Test func testDatabaseErrorTypes() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        
        // Act & Assert - Duplicate error
        try await catalog.createDatabase(name: "test_db", owner: "user1")
        await #expect(throws: DBError.duplicate) {
            try await catalog.createDatabase(name: "test_db", owner: "user2")
        }
        
        // Act & Assert - Not found error
        await #expect(throws: DBError.notFound) {
            try await catalog.dropDatabase(name: "non_existent")
        }
        
        await #expect(throws: DBError.notFound) {
            try await catalog.switchDatabase(name: "non_existent")
        }
        
        // Act & Assert - Internal error
        await #expect(throws: DBError.internalError("Cannot drop system database")) {
            try await catalog.dropDatabase(name: "system")
        }
    }
    
    // MARK: - Concurrent Operations Tests
    
    @Test func testConcurrentDatabaseCreation() async throws {
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
        #expect(databases.count >= dbCount + 1) // +1 for system database
    }
    
    @Test func testConcurrentDatabaseOperations() async throws {
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
        #expect(databases.count >= 6) // system + created databases
    }
    
    // MARK: - Edge Cases Tests
    
    @Test func testEmptyDatabaseName() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        
        // Act & Assert
        await #expect(throws: DBError.notFound) {
            try await catalog.switchDatabase(name: "")
        }
        
        await #expect(throws: DBError.notFound) {
            try await catalog.dropDatabase(name: "")
        }
    }
    
    @Test func testSystemDatabaseOperations() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        
        // Act & Assert
        // System database should exist and be accessible
        let systemDB = await catalog.getDatabaseInfo(name: "system")
        #expect(systemDB != nil)
        #expect(systemDB?.name == "system")
        #expect(systemDB?.owner == "admin")
        
        // Should be able to switch to system database
        try await catalog.switchDatabase(name: "system")
        let currentDB = await catalog.getCurrentDatabase()
        #expect(currentDB == "system")
    }
    
    @Test func testDatabaseNameCaseSensitivity() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        
        // Act
        try await catalog.createDatabase(name: "TestDB", owner: "user1")
        try await catalog.createDatabase(name: "testdb", owner: "user2")
        
        // Assert
        let databases = await catalog.listDatabases()
        #expect(databases.contains("TestDB"))
        #expect(databases.contains("testdb"))
        #expect(databases.count == 3) // system + 2 created
    }
    
    // MARK: - Performance Tests
    
    @Test func testBulkDatabaseOperations() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        let dbCount = 100
        
        // Act
        for i in 0..<dbCount {
            try await catalog.createDatabase(name: "bulk_db_\(i)", owner: "user_\(i)")
        }
        
        // Assert
        let databases = await catalog.listDatabases()
        #expect(databases.count == dbCount + 1) // +1 for system
        
        // Test switching to each database
        for i in 0..<dbCount {
            try await catalog.switchDatabase(name: "bulk_db_\(i)")
            let currentDB = await catalog.getCurrentDatabase()
            #expect(currentDB == "bulk_db_\(i)")
        }
    }
    
    @Test func testDatabaseCreationPerformance() async throws {
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
        #expect(databases.count == 51) // 50 + system
        
        // Performance assertion (should complete in reasonable time)
        #expect(duration < 5.0) // 5 seconds max
    }
    
    // MARK: - Integration Tests
    
    @Test func testCompleteDatabaseLifecycle() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        
        // Act & Assert - Create
        try await catalog.createDatabase(name: "lifecycle_db", owner: "lifecycle_user")
        var databases = await catalog.listDatabases()
        #expect(databases.contains("lifecycle_db"))
        
        // Act & Assert - Switch
        try await catalog.switchDatabase(name: "lifecycle_db")
        var currentDB = await catalog.getCurrentDatabase()
        #expect(currentDB == "lifecycle_db")
        
        // Act & Assert - Get info
        let dbInfo = await catalog.getDatabaseInfo(name: "lifecycle_db")
        #expect(dbInfo?.name == "lifecycle_db")
        #expect(dbInfo?.owner == "lifecycle_user")
        
        // Act & Assert - Drop
        try await catalog.dropDatabase(name: "lifecycle_db")
        databases = await catalog.listDatabases()
        #expect(!databases.contains("lifecycle_db"))
        
        // Act & Assert - Current should switch back to system
        currentDB = await catalog.getCurrentDatabase()
        #expect(currentDB == "system")
    }
    
    @Test func testMultipleDatabaseWorkflow() async throws {
        // Arrange
        let catalog = MultiDatabaseCatalog()
        
        // Act & Assert - Create multiple databases
        try await catalog.createDatabase(name: "app_db", owner: "app_user")
        try await catalog.createDatabase(name: "analytics_db", owner: "analytics_user")
        try await catalog.createDatabase(name: "logs_db", owner: "logs_user")
        
        // Act & Assert - Switch between them
        try await catalog.switchDatabase(name: "app_db")
        #expect(await catalog.getCurrentDatabase() == "app_db")
        
        try await catalog.switchDatabase(name: "analytics_db")
        #expect(await catalog.getCurrentDatabase() == "analytics_db")
        
        try await catalog.switchDatabase(name: "logs_db")
        #expect(await catalog.getCurrentDatabase() == "logs_db")
        
        // Act & Assert - Drop one, others remain
        try await catalog.dropDatabase(name: "analytics_db")
        let databases = await catalog.listDatabases()
        #expect(databases.contains("app_db"))
        #expect(!databases.contains("analytics_db"))
        #expect(databases.contains("logs_db"))
        #expect(databases.contains("system"))
        
        // Act & Assert - Current should remain on logs_db
        #expect(await catalog.getCurrentDatabase() == "logs_db")
    }
}
