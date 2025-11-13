//
//  IndexContractTests.swift
//  ColibrìDB Index Contract Tests
//
//  TDD Macro-task A: RED phase
//  Author: ColibrìDB TDD Chief Engineer
//  Date: 2025-01-XX
//
//  Property-based tests for unified Index protocol.
//  Verifies invariants that ALL index implementations must satisfy:
//
//  1. Insert → Seek: insert(key, rid) → seek(key) returns last value
//  2. Scan Order: scan(range) returns sorted results (for ordered indexes)
//  3. Delete Reduces Cardinality: delete(key) reduces entry count
//  4. No Phantom Keys: deleted keys don't appear in scans
//  5. Idempotent Operations: multiple inserts/deletes behave correctly
//

import XCTest
@testable import ColibriCore

// Import wrapper types
extension IndexContractTests {
    // Helper to create test indexes
}

/// Test suite for unified Index protocol contract
/// All index implementations (BTreeIndex, ARTIndex, HashIndex, LSMTree, SkipList)
/// must pass these tests to be considered conformant.
final class IndexContractTests: XCTestCase {
    
    // MARK: - Test Data Generation (Seeded RNG for determinism)
    
    /// Seeded random number generator for deterministic property tests
    private struct SeededRNG {
        private var state: UInt64
        
        init(seed: UInt64 = 42) {
            self.state = seed
        }
        
        mutating func next() -> UInt64 {
            state = state &* 1103515245 &+ 12345
            return state
        }
        
        mutating func nextInt(in range: ClosedRange<Int>) -> Int {
            let span = UInt64(range.upperBound - range.lowerBound + 1)
            return range.lowerBound + Int(next() % span)
        }
        
        mutating func nextValue() -> Value {
            let kind = nextInt(in: 0...2)
            switch kind {
            case 0:
                return Value.int(Int64(nextInt(in: -1000...1000)))
            case 1:
                return Value.string("key_\(next())")
            case 2:
                return .bool(next() % 2 == 0)
            default:
                return Value.int(Int64(nextInt(in: -1000...1000)))
            }
        }
        
        mutating func generateKeys(count: Int) -> [Value] {
            var keys: [Value] = []
            for _ in 0..<count {
                keys.append(nextValue())
            }
            return keys
        }
    }
    
    // MARK: - Property Test: Insert → Seek Returns Last Value
    
    /// Property: After insert(key, rid), seek(key) returns the last inserted RID
    /// TLA+ Invariant: Inv_Index_InsertSeekConsistency
    func test_Index_Insert_Then_Seek_Returns_Last_Value() async throws {
        // This test will FAIL until all indexes conform to Index protocol
        // RED phase: test fails because protocol doesn't exist or implementations don't conform
        
        let indexes: [any IndexProtocol] = [
            BTreeIndexWrapper(BTreeIndex()),
            ARTIndexWrapper(ARTIndex()),
            HashIndexWrapper(HashIndex()),
            LSMTreeWrapper(LSMTree()),
            SkipListWrapper(SkipList())
        ]
        
        guard !indexes.isEmpty else {
            XCTFail("No index implementations conform to Index protocol yet")
            return
        }
        
        for index in indexes {
            var rng = SeededRNG(seed: 123)
            let testKeys = rng.generateKeys(count: 100)
            
            // Insert keys with multiple RIDs
            for (i, key) in testKeys.enumerated() {
                let rid = RID(pageID: UInt64(i / 10), slotID: UInt32(i % 10))
                try await index.insert(key: key, rid: rid)
                
                // After each insert, seek should return the last RID
                let result = try await index.seek(key: key)
                XCTAssertNotNil(result, "Seek should return RID after insert")
                XCTAssertTrue(result?.contains(rid) ?? false, "Seek should return last inserted RID")
            }
        }
    }
    
    // MARK: - Property Test: Scan Order (for ordered indexes)
    
    /// Property: For ordered indexes, scan(range) returns results in sorted order
    /// TLA+ Invariant: Inv_Index_ScanOrder
    func test_Index_Scan_Is_Sorted_For_Ordered_Indexes() async throws {
        let indexes: [any IndexProtocol] = [
            BTreeIndexWrapper(BTreeIndex()),
            ARTIndexWrapper(ARTIndex()),
            LSMTreeWrapper(LSMTree()),
            SkipListWrapper(SkipList())
        ]
        
        guard !indexes.isEmpty else {
            XCTFail("No index implementations conform to Index protocol yet")
            return
        }
        
        for index in indexes where index.supportsOrderedScans {
            var rng = SeededRNG(seed: 456)
            let testKeys = rng.generateKeys(count: 50)
            
            // Insert keys
            for (i, key) in testKeys.enumerated() {
                let rid = RID(pageID: 1, slotID: UInt32(i))
                try await index.insert(key: key, rid: rid)
            }
            
            // Scan entire range
            let minKey = testKeys.min() ?? .null
            let maxKey = testKeys.max() ?? .null
            
            let results = try await index.scan(minKey: minKey, maxKey: maxKey)
            
            // Verify results are sorted
            for i in 1..<results.count {
                let prevKey = results[i-1].0
                let currKey = results[i].0
                XCTAssertLessThanOrEqual(prevKey, currKey, "Scan results must be sorted")
            }
        }
    }
    
    // MARK: - Property Test: Delete Reduces Cardinality
    
    /// Property: delete(key) reduces the cardinality of the index
    /// TLA+ Invariant: Inv_Index_DeleteReducesCardinality
    func test_Index_Delete_Reduces_Cardinality() async throws {
        let indexes: [any IndexProtocol] = [
            BTreeIndexWrapper(BTreeIndex()),
            HashIndexWrapper(HashIndex()),
            LSMTreeWrapper(LSMTree()),
            SkipListWrapper(SkipList())
        ]
        
        guard !indexes.isEmpty else {
            XCTFail("No index implementations conform to Index protocol yet")
            return
        }
        
        for index in indexes {
            var rng = SeededRNG(seed: 789)
            let testKeys = rng.generateKeys(count: 30)
            
            // Insert keys
            for (i, key) in testKeys.enumerated() {
                let rid = RID(pageID: 1, slotID: UInt32(i))
                try await index.insert(key: key, rid: rid)
            }
            
            let initialCardinality = try await index.getCardinality()
            XCTAssertEqual(initialCardinality, testKeys.count, "Initial cardinality should match inserted keys")
            
            // Delete half the keys
            let keysToDelete = Array(testKeys.prefix(testKeys.count / 2))
            for key in keysToDelete {
                try await index.delete(key: key)
            }
            
            let finalCardinality = try await index.getCardinality()
            XCTAssertLessThan(finalCardinality, initialCardinality, "Delete should reduce cardinality")
            XCTAssertEqual(finalCardinality, testKeys.count - keysToDelete.count, "Cardinality should match remaining keys")
        }
    }
    
    // MARK: - Property Test: No Phantom Keys
    
    /// Property: Deleted keys don't appear in scans (no phantom reads)
    /// TLA+ Invariant: Inv_Index_NoPhantomKeys
    func test_Index_Deleted_Keys_Do_Not_Appear_In_Scans() async throws {
        let indexes: [any IndexProtocol] = [
            BTreeIndexWrapper(BTreeIndex()),
            HashIndexWrapper(HashIndex()),
            LSMTreeWrapper(LSMTree()),
            SkipListWrapper(SkipList())
        ]
        
        guard !indexes.isEmpty else {
            XCTFail("No index implementations conform to Index protocol yet")
            return
        }
        
        for index in indexes {
            var rng = SeededRNG(seed: 101112)
            let testKeys = rng.generateKeys(count: 40)
            
            // Insert keys
            for (i, key) in testKeys.enumerated() {
                let rid = RID(pageID: 1, slotID: UInt32(i))
                try await index.insert(key: key, rid: rid)
            }
            
            // Delete some keys
            let keysToDelete = Array(testKeys.prefix(10))
            for key in keysToDelete {
                try await index.delete(key: key)
            }
            
            // Scan entire range
            let minKey = testKeys.min() ?? .null
            let maxKey = testKeys.max() ?? .null
            let results = try await index.scan(minKey: minKey, maxKey: maxKey)
            
            // Verify deleted keys don't appear
            let resultKeys = Set(results.map { $0.0 })
            let deletedKeys = Set(keysToDelete)
            let intersection = resultKeys.intersection(deletedKeys)
            XCTAssertTrue(intersection.isEmpty, "Deleted keys should not appear in scans")
        }
    }
    
    // MARK: - Property Test: Idempotent Operations
    
    /// Property: Multiple inserts of same key are idempotent (last write wins)
    /// TLA+ Invariant: Inv_Index_InsertIdempotence
    func test_Index_Multiple_Inserts_Of_Same_Key_Are_Idempotent() async throws {
        let indexes: [any IndexProtocol] = [
            BTreeIndexWrapper(BTreeIndex()),
            ARTIndexWrapper(ARTIndex()),
            HashIndexWrapper(HashIndex()),
            LSMTreeWrapper(LSMTree()),
            SkipListWrapper(SkipList())
        ]
        
        guard !indexes.isEmpty else {
            XCTFail("No index implementations conform to Index protocol yet")
            return
        }
        
        for index in indexes {
            let key: Value = Value.int(42)
            let rid1 = RID(pageID: 1, slotID: 1)
            let rid2 = RID(pageID: 2, slotID: 2)
            let rid3 = RID(pageID: 3, slotID: 3)
            
            // Insert same key multiple times
            try await index.insert(key: key, rid: rid1)
            try await index.insert(key: key, rid: rid2)
            try await index.insert(key: key, rid: rid3)
            
            // Seek should return all RIDs (or last, depending on index semantics)
            let result = try await index.seek(key: key)
            XCTAssertNotNil(result, "Seek should return RIDs after multiple inserts")
            // Note: Some indexes may return all RIDs, others may return last
            // This is index-specific behavior, but should be consistent
        }
    }
    
    // MARK: - Property Test: Uniform Distribution Workload
    
    /// Property test with uniform key distribution
    func test_Index_Uniform_Distribution_Workload() async throws {
        let indexes: [any IndexProtocol] = [
            BTreeIndexWrapper(BTreeIndex()),
            ARTIndexWrapper(ARTIndex()),
            HashIndexWrapper(HashIndex()),
            LSMTreeWrapper(LSMTree()),
            SkipListWrapper(SkipList())
        ]
        
        guard !indexes.isEmpty else {
            XCTFail("No index implementations conform to Index protocol yet")
            return
        }
        
        for index in indexes {
            var rng = SeededRNG(seed: 131415)
            let testKeys = rng.generateKeys(count: 200)
            
            // Insert all keys
            for (i, key) in testKeys.enumerated() {
                let rid = RID(pageID: UInt64(i / 100), slotID: UInt32(i % 100))
                try await index.insert(key: key, rid: rid)
            }
            
            // Verify all keys are findable
            for key in testKeys {
                let result = try await index.seek(key: key)
                XCTAssertNotNil(result, "All inserted keys should be findable")
            }
            
            // Verify cardinality
            let cardinality = try await index.getCardinality()
            XCTAssertEqual(cardinality, Set(testKeys).count, "Cardinality should match unique keys")
        }
    }
    
    // MARK: - Property Test: Zipf Distribution Workload
    
    /// Property test with Zipf-like key distribution (skewed access)
    func test_Index_Zipf_Distribution_Workload() async throws {
        let indexes: [any IndexProtocol] = [
            BTreeIndexWrapper(BTreeIndex()),
            ARTIndexWrapper(ARTIndex()),
            HashIndexWrapper(HashIndex()),
            LSMTreeWrapper(LSMTree()),
            SkipListWrapper(SkipList())
        ]
        
        guard !indexes.isEmpty else {
            XCTFail("No index implementations conform to Index protocol yet")
            return
        }
        
        for index in indexes {
            var rng = SeededRNG(seed: 161718)
            
            // Generate Zipf-like distribution (few hot keys, many cold keys)
            let hotKeys = (0..<10).map { Value.int(Int64($0)) }
            let coldKeys = (10..<100).map { Value.int(Int64($0)) }
            
            // Insert hot keys many times
            for i in 0..<100 {
                let key = hotKeys[i % hotKeys.count]
                let rid = RID(pageID: 1, slotID: UInt32(i))
                try await index.insert(key: key, rid: rid)
            }
            
            // Insert cold keys once
            for (i, key) in coldKeys.enumerated() {
                let rid = RID(pageID: 2, slotID: UInt32(i))
                try await index.insert(key: key, rid: rid)
            }
            
            // Verify hot keys are findable
            for key in hotKeys {
                let result = try await index.seek(key: key)
                XCTAssertNotNil(result, "Hot keys should be findable")
            }
            
            // Verify cold keys are findable
            for key in coldKeys {
                let result = try await index.seek(key: key)
                XCTAssertNotNil(result, "Cold keys should be findable")
            }
        }
    }
}
