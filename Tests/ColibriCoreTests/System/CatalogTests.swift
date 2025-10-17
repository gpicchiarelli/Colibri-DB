//
//  CatalogTests.swift
//  ColibrDB Tests
//

import Foundation
@_spi(Experimental) import Testing
@testable import ColibriCore

@Suite("System Catalog Tests", .serialized)
struct CatalogTests {
    
    func createTestCatalog() throws -> SystemCatalog {
        let tempPath = FileManager.default.temporaryDirectory
            .appendingPathComponent(UUID().uuidString)
            .appendingPathComponent("catalog.json")
            .path
        
        return try SystemCatalog(path: tempPath)
    }
    
    @Test("Create empty catalog")
    func testCreateCatalog() throws {
        let catalog = try createTestCatalog()
        
        let tables = catalog.logicalObjects(kind: .table)
        #expect(tables.isEmpty)
    }
    
    @Test("Register table in catalog")
    func testRegisterTable() throws {
        var catalog = try createTestCatalog()
        
        let tableId = catalog.registerTable(
            name: "users",
            schema: ["id": "INT", "name": "TEXT"],
            storage: "FileHeap",
            physicalPath: "/tmp/users.dat",
            pageSize: 8192,
            inMemory: false
        )
        
        #expect(tableId != nil)
        
        let tables = catalog.logicalObjects(kind: .table)
        #expect(tables.count == 1)
        #expect(tables[0].name == "users")
    }
    
    @Test("Register index in catalog")
    func testRegisterIndex() throws {
        var catalog = try createTestCatalog()
        
        // First register table
        _ = catalog.registerTable(
            name: "users",
            schema: ["id": "INT"],
            storage: "FileHeap",
            physicalPath: "/tmp/users.dat",
            pageSize: 8192,
            inMemory: false
        )
        
        // Then register index
        let indexId = catalog.registerIndex(
            name: "idx_users_id",
            parentTable: "users",
            columns: ["id"],
            indexType: "BTree",
            physicalPath: "/tmp/idx.bt"
        )
        
        #expect(indexId != nil)
        
        let indices = catalog.logicalObjects(kind: .index)
        #expect(indices.count == 1)
        #expect(indices[0].name == "idx_users_id")
    }
    
    @Test("Lookup table by name")
    func testLookupTable() throws {
        var catalog = try createTestCatalog()
        
        _ = catalog.registerTable(
            name: "orders",
            schema: nil,
            storage: "FileHeap",
            physicalPath: "/tmp/orders.dat",
            pageSize: 8192,
            inMemory: false
        )
        
        let tables = catalog.logicalObjects(kind: .table)
        let found = tables.first { $0.name == "orders" }
        
        #expect(found != nil)
        #expect(found?.name == "orders")
    }
    
    @Test("Register role in catalog")
    func testRegisterRole() throws {
        var catalog = try createTestCatalog()
        
        let roleId = catalog.registerRole(
            name: "admin",
            kind: .user,
            members: [],
            privileges: ["ALL"],
            metadata: ["description": "Administrator"]
        )
        
        #expect(roleId != nil)
        
        let roles = catalog.roles()
        #expect(roles.contains { $0.name == "admin" })
    }
    
    @Test("Register configuration in catalog")
    func testRegisterConfiguration() throws {
        var catalog = try createTestCatalog()
        
        let configId = catalog.registerConfiguration(
            scope: "database",
            key: "max_connections",
            value: "100"
        )
        
        #expect(configId != nil)
        
        let configs = catalog.configurations(scope: "database")
        #expect(configs.contains { $0.key == "max_connections" })
    }
    
    @Test("Catalog persistence")
    func testCatalogPersistence() throws {
        let tempPath = FileManager.default.temporaryDirectory
            .appendingPathComponent(UUID().uuidString)
            .appendingPathComponent("catalog.json")
            .path
        
        // Create and save
        do {
            var catalog = try SystemCatalog(path: tempPath)
            _ = catalog.registerTable(
                name: "persistent_table",
                schema: nil,
                storage: "FileHeap",
                physicalPath: "/tmp/persistent.dat",
                pageSize: 8192,
                inMemory: false
            )
            try catalog.save()
        }
        
        // Reload and verify
        do {
            let catalog = try SystemCatalog(path: tempPath)
            let tables = catalog.logicalObjects(kind: .table)
            #expect(tables.contains { $0.name == "persistent_table" })
        }
    }
}

