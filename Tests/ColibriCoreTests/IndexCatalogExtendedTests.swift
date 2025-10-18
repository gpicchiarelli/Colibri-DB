//
//  IndexCatalogExtendedTests.swift
//  ColibrDBTests
//
//  Extended tests for IndexCatalog with advanced data structures
//
// ColibrDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

import XCTest
@testable import ColibriCore

final class IndexCatalogExtendedTests: XCTestCase {
    
    var tempDir: String!
    var catalog: IndexCatalog!
    
    override func setUp() {
        super.setUp()
        
        // Create temp directory for tests
        let tempDirURL = FileManager.default.temporaryDirectory
            .appendingPathComponent("test_index_catalog_\(UUID().uuidString)")
        tempDir = tempDirURL.path
        
        do {
            catalog = try IndexCatalog(dir: tempDir)
        } catch {
            XCTFail("Failed to create catalog: \(error)")
        }
    }
    
    override func tearDown() {
        // Clean up
        try? FileManager.default.removeItem(atPath: tempDir)
        catalog = nil
        tempDir = nil
        super.tearDown()
    }
    
    // MARK: - Advanced Data Structure Support Tests
    
    func testSkipListIndexDefinition() {
        let def = IndexDef(
            name: "idx_skiplist",
            table: "users",
            column: "email",
            columns: nil,
            kind: "SkipList"
        )
        
        XCTAssertTrue(IndexDef.supportedTypes.contains("SkipList"))
        
        do {
            try catalog.add(def)
            
            let defs = catalog.list()
            XCTAssertEqual(defs.count, 1)
            XCTAssertEqual(defs.first?.kind, "SkipList")
        } catch {
            XCTFail("Failed to add SkipList index: \(error)")
        }
    }
    
    func testTTreeIndexDefinition() {
        let def = IndexDef(
            name: "idx_ttree",
            table: "products",
            column: "price",
            columns: nil,
            kind: "TTree"
        )
        
        XCTAssertTrue(IndexDef.supportedTypes.contains("TTree"))
        
        do {
            try catalog.add(def)
            
            let defs = catalog.list()
            XCTAssertEqual(defs.count, 1)
            XCTAssertEqual(defs.first?.kind, "TTree")
        } catch {
            XCTFail("Failed to add TTree index: \(error)")
        }
    }
    
    func testRadixIndexDefinition() {
        let def = IndexDef(
            name: "idx_radix",
            table: "domains",
            column: "hostname",
            columns: nil,
            kind: "Radix"
        )
        
        XCTAssertTrue(IndexDef.supportedTypes.contains("Radix"))
        
        do {
            try catalog.add(def)
            
            let defs = catalog.list()
            XCTAssertEqual(defs.count, 1)
            XCTAssertEqual(defs.first?.kind, "Radix")
        } catch {
            XCTFail("Failed to add Radix index: \(error)")
        }
    }
    
    func testLSMTreeIndexDefinition() {
        let def = IndexDef(
            name: "idx_lsm",
            table: "logs",
            column: "timestamp",
            columns: nil,
            kind: "LSM"
        )
        
        XCTAssertTrue(IndexDef.supportedTypes.contains("LSM"))
        
        do {
            try catalog.add(def)
            
            let defs = catalog.list()
            XCTAssertEqual(defs.count, 1)
            XCTAssertEqual(defs.first?.kind, "LSM")
        } catch {
            XCTFail("Failed to add LSM index: \(error)")
        }
    }
    
    func testFractalTreeIndexDefinition() {
        let def = IndexDef(
            name: "idx_fractal",
            table: "events",
            column: "event_id",
            columns: nil,
            kind: "Fractal"
        )
        
        XCTAssertTrue(IndexDef.supportedTypes.contains("Fractal"))
        
        do {
            try catalog.add(def)
            
            let defs = catalog.list()
            XCTAssertEqual(defs.count, 1)
            XCTAssertEqual(defs.first?.kind, "Fractal")
        } catch {
            XCTFail("Failed to add Fractal index: \(error)")
        }
    }
    
    // MARK: - Multiple Index Types
    
    func testMixedIndexTypes() {
        let indexes = [
            IndexDef(name: "idx_hash", table: "t1", column: "c1", columns: nil, kind: "Hash"),
            IndexDef(name: "idx_art", table: "t1", column: "c2", columns: nil, kind: "ART"),
            IndexDef(name: "idx_btree", table: "t1", column: "c3", columns: nil, kind: "BTree"),
            IndexDef(name: "idx_skiplist", table: "t2", column: "c1", columns: nil, kind: "SkipList"),
            IndexDef(name: "idx_ttree", table: "t2", column: "c2", columns: nil, kind: "TTree"),
            IndexDef(name: "idx_radix", table: "t3", column: "c1", columns: nil, kind: "Radix"),
            IndexDef(name: "idx_lsm", table: "t3", column: "c2", columns: nil, kind: "LSM"),
            IndexDef(name: "idx_fractal", table: "t4", column: "c1", columns: nil, kind: "Fractal")
        ]
        
        do {
            for index in indexes {
                try catalog.add(index)
            }
            
            let defs = catalog.list()
            XCTAssertEqual(defs.count, 8)
            
            // Verify all types are present
            let kinds = Set(defs.map { $0.kind })
            XCTAssertTrue(kinds.contains("Hash"))
            XCTAssertTrue(kinds.contains("ART"))
            XCTAssertTrue(kinds.contains("BTree"))
            XCTAssertTrue(kinds.contains("SkipList"))
            XCTAssertTrue(kinds.contains("TTree"))
            XCTAssertTrue(kinds.contains("Radix"))
            XCTAssertTrue(kinds.contains("LSM"))
            XCTAssertTrue(kinds.contains("Fractal"))
        } catch {
            XCTFail("Failed to add mixed indexes: \(error)")
        }
    }
    
    // MARK: - Multi-column Index Tests
    
    func testMultiColumnIndex() {
        let def = IndexDef(
            name: "idx_multi",
            table: "users",
            column: nil,
            columns: ["first_name", "last_name"],
            kind: "BTree"
        )
        
        do {
            try catalog.add(def)
            
            let defs = catalog.list()
            XCTAssertEqual(defs.count, 1)
            XCTAssertEqual(defs.first?.columns?.count, 2)
            XCTAssertTrue(defs.first?.columns?.contains("first_name") ?? false)
            XCTAssertTrue(defs.first?.columns?.contains("last_name") ?? false)
        } catch {
            XCTFail("Failed to add multi-column index: \(error)")
        }
    }
    
    // MARK: - Persistence Tests
    
    func testPersistence() {
        let def1 = IndexDef(name: "idx1", table: "t1", column: "c1", columns: nil, kind: "SkipList")
        let def2 = IndexDef(name: "idx2", table: "t2", column: "c2", columns: nil, kind: "TTree")
        
        do {
            try catalog.add(def1)
            try catalog.add(def2)
            
            // Create new catalog with same directory
            let catalog2 = try IndexCatalog(dir: tempDir)
            let defs = catalog2.list()
            
            XCTAssertEqual(defs.count, 2)
            
            let kinds = Set(defs.map { $0.kind })
            XCTAssertTrue(kinds.contains("SkipList"))
            XCTAssertTrue(kinds.contains("TTree"))
        } catch {
            XCTFail("Persistence test failed: \(error)")
        }
    }
    
    // MARK: - Index Removal Tests
    
    func testRemoveIndex() {
        let def = IndexDef(name: "idx_temp", table: "temp", column: "col", columns: nil, kind: "Hash")
        
        do {
            try catalog.add(def)
            XCTAssertEqual(catalog.list().count, 1)
            
            try catalog.remove(name: "idx_temp", table: "temp")
            XCTAssertEqual(catalog.list().count, 0)
        } catch {
            XCTFail("Remove test failed: \(error)")
        }
    }
    
    func testRemoveNonExistentIndex() {
        do {
            // Should not throw
            try catalog.remove(name: "nonexistent", table: "table")
            XCTAssertEqual(catalog.list().count, 0)
        } catch {
            XCTFail("Should not throw on removing non-existent index")
        }
    }
    
    // MARK: - Use Case Specific Tests
    
    func testHighConcurrencyIndexChoice() {
        // SkipList is good for high concurrency
        let def = IndexDef(
            name: "idx_concurrent",
            table: "sessions",
            column: "session_id",
            columns: nil,
            kind: "SkipList"
        )
        
        do {
            try catalog.add(def)
            let defs = catalog.list()
            XCTAssertEqual(defs.first?.kind, "SkipList")
        } catch {
            XCTFail("Failed: \(error)")
        }
    }
    
    func testInMemoryIndexChoice() {
        // TTree is good for in-memory
        let def = IndexDef(
            name: "idx_memory",
            table: "cache",
            column: "key",
            columns: nil,
            kind: "TTree"
        )
        
        do {
            try catalog.add(def)
            let defs = catalog.list()
            XCTAssertEqual(defs.first?.kind, "TTree")
        } catch {
            XCTFail("Failed: \(error)")
        }
    }
    
    func testStringPrefixIndexChoice() {
        // Radix is good for string prefixes
        let def = IndexDef(
            name: "idx_prefix",
            table: "urls",
            column: "path",
            columns: nil,
            kind: "Radix"
        )
        
        do {
            try catalog.add(def)
            let defs = catalog.list()
            XCTAssertEqual(defs.first?.kind, "Radix")
        } catch {
            XCTFail("Failed: \(error)")
        }
    }
    
    func testWriteHeavyIndexChoice() {
        // LSM is good for write-heavy workloads
        let def = IndexDef(
            name: "idx_writes",
            table: "logs",
            column: "timestamp",
            columns: nil,
            kind: "LSM"
        )
        
        do {
            try catalog.add(def)
            let defs = catalog.list()
            XCTAssertEqual(defs.first?.kind, "LSM")
        } catch {
            XCTFail("Failed: \(error)")
        }
    }
    
    func testBalancedWorkloadIndexChoice() {
        // Fractal is good for balanced read/write
        let def = IndexDef(
            name: "idx_balanced",
            table: "transactions",
            column: "tx_id",
            columns: nil,
            kind: "Fractal"
        )
        
        do {
            try catalog.add(def)
            let defs = catalog.list()
            XCTAssertEqual(defs.first?.kind, "Fractal")
        } catch {
            XCTFail("Failed: \(error)")
        }
    }
    
    // MARK: - Supported Types Verification
    
    func testAllSupportedTypes() {
        let expectedTypes = ["Hash", "ART", "BTree", "SkipList", "TTree", "Radix", "LSM", "Fractal"]
        
        for type in expectedTypes {
            XCTAssertTrue(IndexDef.supportedTypes.contains(type), "Missing support for \(type)")
        }
        
        XCTAssertEqual(Set(IndexDef.supportedTypes).count, expectedTypes.count,
                      "Duplicate types in supported types list")
    }
    
    // MARK: - Edge Cases
    
    func testEmptyTableName() {
        let def = IndexDef(name: "idx", table: "", column: "col", columns: nil, kind: "Hash")
        
        do {
            try catalog.add(def)
            let defs = catalog.list()
            XCTAssertEqual(defs.count, 1)
        } catch {
            XCTFail("Should handle empty table name: \(error)")
        }
    }
    
    func testDuplicateIndexDefinition() {
        let def = IndexDef(name: "idx", table: "t", column: "c", columns: nil, kind: "Hash")
        
        do {
            try catalog.add(def)
            try catalog.add(def) // Add same definition again
            
            // Should not add duplicate
            let defs = catalog.list()
            XCTAssertEqual(defs.count, 1)
        } catch {
            XCTFail("Failed: \(error)")
        }
    }
    
    func testLongIndexNames() {
        let longName = String(repeating: "x", count: 1000)
        let def = IndexDef(name: longName, table: "t", column: "c", columns: nil, kind: "Hash")
        
        do {
            try catalog.add(def)
            let defs = catalog.list()
            XCTAssertEqual(defs.first?.name.count, 1000)
        } catch {
            XCTFail("Should handle long names: \(error)")
        }
    }
}

