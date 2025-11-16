//
//  SystemCatalogIntegrationTests.swift
//  Integration tests for SystemCatalogManager, PrivilegeManager, and InformationSchemaViews
//

import XCTest
@testable import ColibriCore

final class SystemCatalogIntegrationTests: XCTestCase {
    private var tempDir: URL!
    private var db: ColibrìDB!
    
    override func setUp() async throws {
        tempDir = FileManager.default.temporaryDirectory.appendingPathComponent(UUID().uuidString)
        try FileManager.default.createDirectory(at: tempDir, withIntermediateDirectories: true)
        
        let config = ColibrìDBConfiguration(
            dataDirectory: tempDir,
            bufferPoolSize: 100,
            maxConnections: 10,
            walBufferSize: 1024 * 1024,
            checkpointInterval: 300,
            logLevel: .info,
            enableStatistics: false,
            enableAutoAnalyze: false
        )
        
        db = try ColibrìDB(config: config)
        try await db.start()
        
        // Bootstrap system catalog
        let bootstrap = SystemCatalogBootstrap()
        try await bootstrap.initialize(on: db)
    }
    
    override func tearDown() async throws {
        try? await db?.shutdown()
        try? FileManager.default.removeItem(at: tempDir)
    }
    
    // MARK: - SystemCatalogManager Tests
    
    func testCatalogManagerLoadsDatabases() async throws {
        let manager = SystemCatalogManager(database: db)
        try await manager.loadAll()
        
        // Should have at least colibri_sys database
        let tableId = try await manager.resolveTable(database: "colibri_sys", schema: "sys", table: "sys_users")
        XCTAssertNotNil(tableId, "Should resolve sys_users table")
    }
    
    func testCatalogManagerResolvesTableNames() async throws {
        let manager = SystemCatalogManager(database: db)
        try await manager.loadAll()
        
        // Create a test table
        let tx = try await db.beginTransaction()
        try await db.executeQuery("""
            CREATE TABLE test_schema.test_table (
                id BIGINT PRIMARY KEY,
                name TEXT NOT NULL
            );
        """, txId: tx)
        try await db.commit(txId: tx)
        
        // Reload catalog
        try await manager.loadAll()
        
        // Resolve the table
        let tableId = try await manager.resolveTable(database: nil, schema: "test_schema", table: "test_table")
        XCTAssertNotNil(tableId, "Should resolve test_table")
        
        if let tableId = tableId {
            let table = await manager.getTable(byId: tableId)
            XCTAssertNotNil(table, "Should get table descriptor")
            XCTAssertEqual(table?.name, "test_table")
            
            let columns = await manager.getColumns(forTableId: tableId)
            XCTAssertEqual(columns.count, 2, "Should have 2 columns")
            XCTAssertEqual(columns[0].name, "id")
            XCTAssertEqual(columns[1].name, "name")
        }
    }
    
    // MARK: - PrivilegeManager Tests
    
    func testPrivilegeManagerLoadsPrivileges() async throws {
        let manager = PrivilegeManager(database: db)
        try await manager.loadAll()
        
        // Initially no privileges should be loaded (empty sys_privileges)
        // This test just verifies loadAll() doesn't crash
        XCTAssertTrue(true, "PrivilegeManager loaded successfully")
    }
    
    func testPrivilegeManagerGrantRevoke() async throws {
        let manager = PrivilegeManager(database: db)
        try await manager.loadAll()
        
        // Get sys_dba user ID (should exist from bootstrap)
        let tx = try await db.beginTransaction()
        let result = try await db.executeQuery("SELECT user_id FROM colibri_sys.sys_users WHERE username = 'sys_dba' LIMIT 1;", txId: tx)
        try await db.commit(txId: tx)
        
        guard let userIdRow = result.rows.first,
              let userId = extractInt64(userIdRow["user_id"]) else {
            XCTFail("sys_dba user should exist")
            return
        }
        
        // Create a test table
        let tx2 = try await db.beginTransaction()
        try await db.executeQuery("""
            CREATE TABLE test_schema.test_table (
                id BIGINT PRIMARY KEY
            );
        """, txId: tx2)
        
        // Get table_id
        let result2 = try await db.executeQuery("""
            SELECT table_id FROM colibri_sys.sys_tables 
            WHERE name = 'test_table' AND schema_id IN (
                SELECT schema_id FROM colibri_sys.sys_schemas WHERE name = 'test_schema'
            ) LIMIT 1;
        """, txId: tx2)
        try await db.commit(txId: tx2)
        
        guard let tableIdRow = result2.rows.first,
              let tableId = extractInt64(tableIdRow["table_id"]) else {
            XCTFail("test_table should exist")
            return
        }
        
        // Grant SELECT privilege
        try await manager.grant(
            privilege: .select,
            on: .table,
            objectId: tableId,
            to: .user,
            granteeId: userId,
            grantorId: userId,
            withGrantOption: true
        )
        
        // Reload privileges
        try await manager.loadAll()
        
        // Check privilege
        let hasSelect = await manager.hasPrivilege(
            userId: userId,
            roles: [],
            privilege: .select,
            on: .table,
            objectId: tableId
        )
        XCTAssertTrue(hasSelect, "User should have SELECT privilege")
        
        // Check grant option
        let canGrant = await manager.canGrant(
            userId: userId,
            roles: [],
            privilege: .select,
            on: .table,
            objectId: tableId
        )
        XCTAssertTrue(canGrant, "User should have GRANT OPTION")
        
        // Revoke privilege
        try await manager.revoke(
            privilege: .select,
            on: .table,
            objectId: tableId,
            from: .user,
            granteeId: userId,
            cascade: false
        )
        
        // Reload privileges
        try await manager.loadAll()
        
        // Check privilege is revoked
        let hasSelectAfter = await manager.hasPrivilege(
            userId: userId,
            roles: [],
            privilege: .select,
            on: .table,
            objectId: tableId
        )
        XCTAssertFalse(hasSelectAfter, "User should not have SELECT privilege after revoke")
    }
    
    // MARK: - InformationSchemaViews Tests
    
    func testInformationSchemaViewsExist() {
        let views = InformationSchemaViews.getAllViewDefinitions()
        
        XCTAssertTrue(views.keys.contains("schemata"), "Should have schemata view")
        XCTAssertTrue(views.keys.contains("tables"), "Should have tables view")
        XCTAssertTrue(views.keys.contains("columns"), "Should have columns view")
        XCTAssertTrue(views.keys.contains("table_constraints"), "Should have table_constraints view")
        XCTAssertTrue(views.keys.contains("key_column_usage"), "Should have key_column_usage view")
        XCTAssertTrue(views.keys.contains("referential_constraints"), "Should have referential_constraints view")
    }
    
    func testInformationSchemaViewsCanBeQueried() async throws {
        // Get schemata view query
        guard let schemataQuery = InformationSchemaViews.getViewQuery(viewName: "schemata") else {
            XCTFail("Should get schemata view query")
            return
        }
        
        // Execute the view query
        let tx = try await db.beginTransaction()
        let result = try await db.executeQuery(schemataQuery, txId: tx)
        try await db.commit(txId: tx)
        
        // Should return at least colibri_sys.sys schema
        XCTAssertGreaterThan(result.rows.count, 0, "Should return at least one schema")
        
        // Verify columns exist
        if let firstRow = result.rows.first {
            XCTAssertNotNil(firstRow["catalog_name"], "Should have catalog_name column")
            XCTAssertNotNil(firstRow["schema_name"], "Should have schema_name column")
        }
    }
    
    // MARK: - Helper Functions
    
    private func extractInt64(_ value: Value?) -> Int64? {
        guard let v = value, case .int(let i) = v else { return nil }
        return i
    }
}

