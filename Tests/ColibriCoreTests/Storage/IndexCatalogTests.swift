//
//  IndexCatalogTests.swift
//  ColibrDB Tests
//

import Foundation
@_spi(Experimental) import Testing
@testable import ColibriCore

@Suite("Index Catalog Tests", .serialized)
struct IndexCatalogTests {
    
    func createTestCatalog() throws -> IndexCatalog {
        let tempDir = FileManager.default.temporaryDirectory
            .appendingPathComponent(UUID().uuidString)
        try FileManager.default.createDirectory(at: tempDir, withIntermediateDirectories: true)
        
        return try IndexCatalog(dir: tempDir.path)
    }
    
    @Test("Create empty catalog")
    func testCreateCatalog() throws {
        let catalog = try createTestCatalog()
        
        let indices = catalog.list()
        #expect(indices.isEmpty)
    }
    
    @Test("Register index definition")
    func testRegisterIndex() throws {
        var catalog = try createTestCatalog()
        
        let def = IndexDefinition(
            name: "idx_users_name",
            table: "users",
            columns: ["name"],
            indexType: "BTree",
            path: "/tmp/test.idx"
        )
        
        try catalog.register(def)
        
        let indices = catalog.list()
        #expect(indices.count == 1)
        #expect(indices[0].name == "idx_users_name")
    }
    
    @Test("Lookup index by name")
    func testLookupIndex() throws {
        var catalog = try createTestCatalog()
        
        let def = IndexDefinition(
            name: "idx_test",
            table: "test",
            columns: ["col1"],
            indexType: "Hash",
            path: "/tmp/test.idx"
        )
        
        try catalog.register(def)
        
        let found = catalog.lookup(name: "idx_test", table: "test")
        #expect(found != nil)
        #expect(found?.name == "idx_test")
    }
    
    @Test("List all indices")
    func testListIndices() throws {
        var catalog = try createTestCatalog()
        
        try catalog.register(IndexDefinition(
            name: "idx1", table: "table1", columns: ["col1"], indexType: "BTree", path: "/tmp/idx1.idx"
        ))
        try catalog.register(IndexDefinition(
            name: "idx2", table: "table1", columns: ["col2"], indexType: "Hash", path: "/tmp/idx2.idx"
        ))
        try catalog.register(IndexDefinition(
            name: "idx3", table: "table2", columns: ["col1"], indexType: "BTree", path: "/tmp/idx3.idx"
        ))
        
        let all = catalog.list()
        #expect(all.count == 3)
    }
    
    @Test("List indices for specific table")
    func testListIndicesForTable() throws {
        var catalog = try createTestCatalog()
        
        try catalog.register(IndexDefinition(
            name: "idx1", table: "users", columns: ["name"], indexType: "BTree", path: "/tmp/idx1.idx"
        ))
        try catalog.register(IndexDefinition(
            name: "idx2", table: "orders", columns: ["date"], indexType: "BTree", path: "/tmp/idx2.idx"
        ))
        
        let userIndices = catalog.list().filter { $0.table == "users" }
        #expect(userIndices.count == 1)
    }
    
    @Test("Remove index from catalog")
    func testRemoveIndex() throws {
        var catalog = try createTestCatalog()
        
        let def = IndexDefinition(
            name: "idx_temp", table: "temp", columns: ["col1"], indexType: "BTree", path: "/tmp/temp.idx"
        )
        
        try catalog.register(def)
        #expect(catalog.list().count == 1)
        
        try catalog.remove(name: "idx_temp", table: "temp")
        #expect(catalog.list().isEmpty)
    }
    
    @Test("Catalog persists after save/load")
    func testPersistence() throws {
        let tempDir = FileManager.default.temporaryDirectory
            .appendingPathComponent(UUID().uuidString)
        try FileManager.default.createDirectory(at: tempDir, withIntermediateDirectories: true)
        
        // Register and save
        do {
            var catalog = try IndexCatalog(dir: tempDir.path)
            try catalog.register(IndexDefinition(
                name: "persistent_idx", 
                table: "test", 
                columns: ["col1"], 
                indexType: "BTree", 
                path: "/tmp/persistent.idx"
            ))
            try catalog.save()
        }
        
        // Reload and verify
        do {
            let catalog = try IndexCatalog(dir: tempDir.path)
            let indices = catalog.list()
            #expect(indices.count == 1)
            #expect(indices[0].name == "persistent_idx")
        }
    }
}

