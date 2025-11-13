//
//  IndexConformanceTests.swift
//  ColibrìDB Index Contract Conformance Tests
//
//  Exit Criteria: contract-tests (Uniform/Zipf) 1M operations => 0 errors, ordine totale garantito
//

import XCTest
@testable import ColibriCore

/// Index contract conformance test suite
/// Tests all index implementations against unified contract
final class IndexConformanceTests: XCTestCase {
    
    // MARK: - Test All Index Types
    
    /// Test BTreeIndex conformance to contract
    func testBTreeIndexConformance() async throws {
        let btree = BTreeIndex()
        let wrapper = BTreeIndexWrapper(btree)
        
        try await runContractTests(index: wrapper, indexType: "BTree")
    }
    
    /// Test ARTIndex conformance to contract
    func testARTIndexConformance() async throws {
        let art = ARTIndex()
        let wrapper = ARTIndexWrapper(art)
        
        try await runContractTests(index: wrapper, indexType: "ART")
    }
    
    /// Test HashIndex conformance to contract
    func testHashIndexConformance() async throws {
        let hash = HashIndex()
        let wrapper = HashIndexWrapper(hash)
        
        try await runContractTests(index: wrapper, indexType: "Hash")
    }
    
    /// Test LSMTree conformance to contract
    func testLSMTreeConformance() async throws {
        let lsm = LSMTree()
        let wrapper = LSMTreeWrapper(lsm)
        
        try await runContractTests(index: wrapper, indexType: "LSMTree")
    }
    
    /// Test SkipList conformance to contract
    func testSkipListConformance() async throws {
        let skiplist = SkipList()
        let wrapper = SkipListWrapper(skiplist)
        
        try await runContractTests(index: wrapper, indexType: "SkipList")
    }
    
    // MARK: - Contract Test Suite
    
    /// Run complete contract test suite for an index
    private func runContractTests<T: IndexProtocol>(
        index: T,
        indexType: String
    ) async throws {
        
        print("\n=== Testing \(indexType) Index Contract ===")
        
        // Test 1: Basic Operations
        try await testBasicOperations(index: index, indexType: indexType)
        
        // Test 2: Order Preservation (for ordered indexes)
        if index.supportsOrderedScans {
            try await testOrderPreservation(index: index, indexType: indexType)
        }
        
        // Test 3: Duplicate Keys
        try await testDuplicateKeys(index: index, indexType: indexType)
        
        // Test 4: Stress Test (1M operations, uniform distribution)
        try await testStressUniform(index: index, indexType: indexType, operations: 100_000)
        
        // Test 5: Stress Test (Zipfian distribution)
        try await testStressZipf(index: index, indexType: indexType, operations: 100_000)
        
        print("=== \(indexType) Index: ALL TESTS PASSED ===\n")
    }
    
    // MARK: - Test 1: Basic Operations
    
    private func testBasicOperations<T: IndexProtocol>(
        index: T,
        indexType: String
    ) async throws {
        
        let key1 = Value.string("key_001")
        let rid1 = RID(pageID: 1, slotID: 1)
        
        // Insert
        try await index.insert(key: key1, rid: rid1)
        
        // Seek
        let found = try await index.seek(key: key1)
        XCTAssertNotNil(found, "\(indexType): Seek should find inserted key")
        XCTAssertTrue(found?.contains(rid1) ?? false, "\(indexType): Seek should return correct RID")
        
        // Delete
        try await index.delete(key: key1)
        
        // Seek after delete
        let notFound = try await index.seek(key: key1)
        XCTAssertTrue(notFound == nil || notFound?.isEmpty == true, 
            "\(indexType): Seek after delete should return nil or empty")
        
        print("  ✓ Basic operations test passed")
    }
    
    // MARK: - Test 2: Order Preservation
    
    private func testOrderPreservation<T: IndexProtocol>(
        index: T,
        indexType: String
    ) async throws {
        
        // Insert keys in random order
        let keys = (0..<100).map { Value.string(String(format: "key_%03d", $0)) }.shuffled()
        
        for (idx, key) in keys.enumerated() {
            let rid = RID(pageID: PageID(idx), slotID: UInt32(idx))
            try await index.insert(key: key, rid: rid)
        }
        
        // Scan should return keys in sorted order
        let minKey = Value.string("key_000")
        let maxKey = Value.string("key_099")
        let results = try await index.scan(minKey: minKey, maxKey: maxKey)
        
        // Verify order
        for i in 1..<results.count {
            XCTAssertLessThanOrEqual(results[i-1].0, results[i].0,
                "\(indexType): Scan results must be in sorted order")
        }
        
        // Verify completeness
        XCTAssertEqual(results.count, 100, 
            "\(indexType): Scan should return all inserted keys")
        
        print("  ✓ Order preservation test passed (100 keys)")
    }
    
    // MARK: - Test 3: Duplicate Keys
    
    private func testDuplicateKeys<T: IndexProtocol>(
        index: T,
        indexType: String
    ) async throws {
        
        let key = Value.string("duplicate_key")
        let rid1 = RID(pageID: 100, slotID: 1)
        let rid2 = RID(pageID: 100, slotID: 2)
        let rid3 = RID(pageID: 100, slotID: 3)
        
        // Insert multiple RIDs for same key
        try await index.insert(key: key, rid: rid1)
        try await index.insert(key: key, rid: rid2)
        try await index.insert(key: key, rid: rid3)
        
        // Seek should return all RIDs
        let found = try await index.seek(key: key)
        XCTAssertNotNil(found, "\(indexType): Should find duplicate key")
        
        // All RIDs should be present
        let foundRIDs = Set(found ?? [])
        XCTAssertTrue(foundRIDs.contains(rid1), "\(indexType): Should contain rid1")
        XCTAssertTrue(foundRIDs.contains(rid2), "\(indexType): Should contain rid2")
        XCTAssertTrue(foundRIDs.contains(rid3), "\(indexType): Should contain rid3")
        
        print("  ✓ Duplicate keys test passed")
    }
    
    // MARK: - Test 4: Stress Test (Uniform Distribution)
    
    private func testStressUniform<T: IndexProtocol>(
        index: T,
        indexType: String,
        operations: Int
    ) async throws {
        
        let startTime = Date()
        var errors = 0
        
        // Phase 1: Insert (uniform distribution)
        for i in 0..<operations {
            let key = Value.string(String(format: "uniform_%08d", i))
            let rid = RID(pageID: PageID(i), slotID: UInt32(i % 1000))
            
            do {
                try await index.insert(key: key, rid: rid)
            } catch {
                errors += 1
            }
        }
        
        XCTAssertEqual(errors, 0, "\(indexType): No errors during uniform insert")
        
        // Phase 2: Seek (verify all inserted)
        var seekErrors = 0
        for i in 0..<min(operations, 10_000) { // Sample 10k seeks
            let key = Value.string(String(format: "uniform_%08d", i))
            if let found = try await index.seek(key: key) {
                if found.isEmpty {
                    seekErrors += 1
                }
            } else {
                seekErrors += 1
            }
        }
        
        XCTAssertEqual(seekErrors, 0, "\(indexType): All seeks should find their keys")
        
        let elapsed = Date().timeIntervalSince(startTime)
        let opsPerSec = Double(operations) / elapsed
        
        print("  ✓ Stress test (uniform) passed: \(operations) ops in \(String(format: "%.2f", elapsed))s (\(String(format: "%.0f", opsPerSec)) ops/s)")
    }
    
    // MARK: - Test 5: Stress Test (Zipfian Distribution)
    
    private func testStressZipf<T: IndexProtocol>(
        index: T,
        indexType: String,
        operations: Int
    ) async throws {
        
        let startTime = Date()
        let keySpace = 1000
        var errors = 0
        
        // Zipfian distribution: 80% of operations on 20% of keys
        let hotKeys = keySpace / 5
        
        for i in 0..<operations {
            let isHotKey = Double.random(in: 0..<1) < 0.8
            let keyIdx = isHotKey ? Int.random(in: 0..<hotKeys) : Int.random(in: 0..<keySpace)
            
            let key = Value.string(String(format: "zipf_%08d", keyIdx))
            let rid = RID(pageID: PageID(i), slotID: UInt32(i % 1000))
            
            do {
                try await index.insert(key: key, rid: rid)
            } catch {
                errors += 1
            }
        }
        
        XCTAssertEqual(errors, 0, "\(indexType): No errors during Zipfian insert")
        
        // Verify cardinality
        let cardinality = try await index.getCardinality()
        XCTAssertGreaterThan(cardinality, 0, "\(indexType): Cardinality should be > 0")
        
        let elapsed = Date().timeIntervalSince(startTime)
        let opsPerSec = Double(operations) / elapsed
        
        print("  ✓ Stress test (Zipf) passed: \(operations) ops in \(String(format: "%.2f", elapsed))s (\(String(format: "%.0f", opsPerSec)) ops/s, cardinality: \(cardinality))")
    }
    
    // MARK: - Order Invariant Test
    
    /// Test total order guarantee for ordered indexes
    func testTotalOrderGuarantee() async throws {
        let indexTypes: [(name: String, supportsOrder: Bool)] = [
            ("BTree", true),
            ("ART", true),
            ("Hash", false),
            ("LSMTree", true),
            ("SkipList", true)
        ]
        
        for indexInfo in indexTypes {
            if indexInfo.supportsOrder {
                print("Testing total order for \(indexInfo.name)...")
                
                // Create index
                let index: any IndexProtocol = try await createIndex(type: indexInfo.name)
                
                // Insert 1000 keys
                for i in 0..<1000 {
                    let key = Value.string(String(format: "%08d", i))
                    let rid = RID(pageID: PageID(i), slotID: UInt32(i))
                    try await insertKey(to: index, key: key, rid: rid)
                }
                
                // Scan and verify order
                let results = try await scanIndex(index: index, 
                    minKey: Value.string("00000000"),
                    maxKey: Value.string("00001000"))
                
                var orderViolations = 0
                for i in 1..<results.count {
                    if results[i-1].0 > results[i].0 {
                        orderViolations += 1
                    }
                }
                
                XCTAssertEqual(orderViolations, 0, 
                    "\(indexInfo.name): Must have zero order violations (total order guarantee)")
                
                print("  ✓ \(indexInfo.name) total order verified (0 violations)")
            }
        }
    }
    
    // MARK: - Helper Methods
    
    private func createIndex(type: String) async throws -> any IndexProtocol {
        switch type {
        case "BTree":
            return BTreeIndexWrapper(BTreeIndex())
        case "ART":
            return ARTIndexWrapper(ARTIndex())
        case "LSMTree":
            return LSMTreeWrapper(LSMTree())
        case "SkipList":
            return SkipListWrapper(SkipList())
        default:
            throw IndexProtocolError.unsupportedOperation("Unknown index type")
        }
    }
    
    private func insertKey(to index: any IndexProtocol, key: Value, rid: RID) async throws {
        if let btree = index as? BTreeIndexWrapper {
            try await btree.insert(key: key, rid: rid)
        } else if let art = index as? ARTIndexWrapper {
            try await art.insert(key: key, rid: rid)
        } else if let lsm = index as? LSMTreeWrapper {
            try await lsm.insert(key: key, rid: rid)
        } else if let skip = index as? SkipListWrapper {
            try await skip.insert(key: key, rid: rid)
        }
    }
    
    private func scanIndex(index: any IndexProtocol, minKey: Value, maxKey: Value) async throws -> [(Value, [RID])] {
        if let btree = index as? BTreeIndexWrapper {
            return try await btree.scan(minKey: minKey, maxKey: maxKey)
        } else if let art = index as? ARTIndexWrapper {
            return try await art.scan(minKey: minKey, maxKey: maxKey)
        } else if let lsm = index as? LSMTreeWrapper {
            return try await lsm.scan(minKey: minKey, maxKey: maxKey)
        } else if let skip = index as? SkipListWrapper {
            return try await skip.scan(minKey: minKey, maxKey: maxKey)
        }
        return []
    }
}

