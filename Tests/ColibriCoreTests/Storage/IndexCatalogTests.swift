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
        let catalog = try createTestCatalog()
        
        let def = IndexDef(
            name: "idx_users_name",
            table: "users",
            column: nil,
            columns: ["name"],
            kind: "BTree"
        )
        
        try catalog.add(def)
        
        let indices = catalog.list()
        #expect(indices.count == 1)
        #expect(indices[0].name == "idx_users_name")
    }
    
    @Test("Lookup index by filtering")
    func testLookupIndex() throws {
        let catalog = try createTestCatalog()
        
        let def = IndexDef(
            name: "idx_test",
            table: "test",
            column: nil,
            columns: ["col1"],
            kind: "Hash"
        )
        
        try catalog.add(def)
        
        let found = catalog.list().first(where: { $0.name == "idx_test" && $0.table == "test" })
        #expect(found != nil)
        #expect(found?.name == "idx_test")
    }
    
    @Test("List all indices")
    func testListIndices() throws {
        let catalog = try createTestCatalog()
        
        try catalog.add(IndexDef(
            name: "idx1", table: "table1", column: nil, columns: ["col1"], kind: "BTree"
        ))
        try catalog.add(IndexDef(
            name: "idx2", table: "table1", column: nil, columns: ["col2"], kind: "Hash"
        ))
        try catalog.add(IndexDef(
            name: "idx3", table: "table2", column: nil, columns: ["col1"], kind: "BTree"
        ))
        
        let all = catalog.list()
        #expect(all.count == 3)
    }
    
    @Test("List indices for specific table")
    func testListIndicesForTable() throws {
        let catalog = try createTestCatalog()
        
        try catalog.add(IndexDef(
            name: "idx1", table: "users", column: nil, columns: ["name"], kind: "BTree"
        ))
        try catalog.add(IndexDef(
            name: "idx2", table: "orders", column: nil, columns: ["date"], kind: "BTree"
        ))
        
        let userIndices = catalog.list().filter { $0.table == "users" }
        #expect(userIndices.count == 1)
    }
    
    @Test("Remove index from catalog")
    func testRemoveIndex() throws {
        let catalog = try createTestCatalog()
        
        let def = IndexDef(
            name: "idx_temp", table: "temp", column: nil, columns: ["col1"], kind: "BTree"
        )
        
        try catalog.add(def)
        #expect(catalog.list().count == 1)
        
        try catalog.remove(name: "idx_temp", table: "temp")
        #expect(catalog.list().isEmpty)
    }
    
    @Test("Catalog persists after reload")
    func testPersistence() throws {
        let tempDir = FileManager.default.temporaryDirectory
            .appendingPathComponent(UUID().uuidString)
        try FileManager.default.createDirectory(at: tempDir, withIntermediateDirectories: true)
        
        // Register
        do {
            let catalog = try IndexCatalog(dir: tempDir.path)
            try catalog.add(IndexDef(
                name: "persistent_idx", 
                table: "test", 
                column: nil,
                columns: ["col1"], 
                kind: "BTree"
            ))
            // save() is called automatically by add()
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

