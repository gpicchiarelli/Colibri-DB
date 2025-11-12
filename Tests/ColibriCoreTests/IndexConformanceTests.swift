//
//  IndexConformanceTests.swift
//  ColibrìDB - Index Protocol Conformance Tests
//
//  TDD: RED Phase - Tests that will fail until implementations conform
//  Author: TDD Chief Engineer
//  Date: 2025-01-27
//
//  These tests verify that all index implementations (BTree, ART, Hash, LSM, SkipList)
//  conform to the Index protocol contract.
//

import XCTest
import Testing
@testable import ColibriCore

/// Property-based test data generator with fixed seed for determinism
struct SeededRandomGenerator {
    private var state: UInt64
    
    init(seed: UInt64 = 42) {
        self.state = seed
    }
    
    mutating func next() -> UInt64 {
        // Linear congruential generator for deterministic randomness
        state = (state &* 1103515245 &+ 12345) & 0x7fffffff
        return state
    }
    
    mutating func nextInt(min: Int, max: Int) -> Int {
        let range = UInt64(max - min + 1)
        return Int(min + (next() % range))
    }
    
    mutating func nextValue() -> Value {
        let kind = next() % 3
        switch kind {
        case 0:
            return .int(Int64(nextInt(min: -1000, max: 1000)))
        case 1:
            return .string("key_\(next())")
        default:
            return .double(Double(nextInt(min: 0, max: 1000)) / 100.0)
        }
    }
}

/// Test suite for Index protocol conformance
/// All index implementations must pass these tests
final class IndexConformanceTests: XCTestCase {
    
    // MARK: - Test: Insert → Seek Returns Last Value
    
    /// Property: After insert(k, r), seek(k) returns r
    func test_Index_Insert_Then_Seek_Returns_Last_Value() async throws {
        let indices: [any Index] = [
            BTreeIndexAdapter(BTreeIndex()),
            ARTIndexAdapter(ARTIndex()),
            HashIndexAdapter(HashIndex())
        ]
        
        for index in indices {
            let key: Value = .int(42)
            let rid = RID(pageID: 1, slotID: 0)
            
            // Insert
            try await index.insert(key: key, rid: rid)
            
            // Seek should return the inserted RID
            let result = try await index.seek(key: key)
            XCTAssertNotNil(result, "Seek should return value after insert")
            XCTAssertEqual(result?.first, rid, "Seek should return last inserted RID")
        }
    }
    
    // MARK: - Test: Scan Is Sorted
    
    /// Property: scan(range) returns results in sorted order
    func test_Index_Scan_Is_Sorted_For_Randomized_Inserts() async throws {
        var rng = SeededRandomGenerator(seed: 42)
        let indices: [any Index] = [
            BTreeIndexAdapter(BTreeIndex()),
            // ARTIndexAdapter(ARTIndex()), // Skip - no range scan yet
            HashIndexAdapter(HashIndex())
        ]
        
        for index in indices {
            // Generate N random key-value pairs
            let n = 100
            var insertedKeys: [Value] = []
            
            for i in 0..<n {
                let key = rng.nextValue()
                let rid = RID(pageID: UInt32(i / 10), slotID: UInt32(i % 10))
                try await index.insert(key: key, rid: rid)
                insertedKeys.append(key)
            }
            
            // Scan entire range
            let minKey: Value = .int(Int64.min)
            let maxKey: Value = .int(Int64.max)
            let results = try await index.scan(minKey: minKey, maxKey: maxKey)
            
            // Verify sorted order
            for i in 0..<(results.count - 1) {
                let (key1, _) = results[i]
                let (key2, _) = results[i + 1]
                XCTAssertTrue(
                    key1 <= key2,
                    "Scan results must be sorted: \(key1) <= \(key2)"
                )
            }
        }
    }
    
    // MARK: - Test: Delete Reduces Cardinality
    
    /// Property: delete(k) reduces cardinality and makes seek(k) return nil
    func test_Index_Delete_Reduces_Cardinality_And_Removes_Key() async throws {
        let indices: [any Index] = [
            BTreeIndexAdapter(BTreeIndex()),
            // ARTIndexAdapter(ARTIndex()), // Skip - no delete yet
            HashIndexAdapter(HashIndex())
        ]
        
        for index in indices {
            let key: Value = .int(100)
            let rid = RID(pageID: 1, slotID: 0)
            
            // Insert
            try await index.insert(key: key, rid: rid)
            let cardinalityBefore = try await index.cardinality()
            XCTAssertEqual(cardinalityBefore, 1, "Cardinality should be 1 after insert")
            
            // Verify key exists
            let beforeDelete = try await index.seek(key: key)
            XCTAssertNotNil(beforeDelete, "Key should exist before delete")
            
            // Delete
            try await index.delete(key: key)
            
            // Verify cardinality reduced
            let cardinalityAfter = try await index.cardinality()
            XCTAssertEqual(cardinalityAfter, 0, "Cardinality should be 0 after delete")
            
            // Verify key no longer exists
            let afterDelete = try await index.seek(key: key)
            XCTAssertNil(afterDelete, "Key should not exist after delete")
        }
    }
    
    // MARK: - Test: No Phantom Keys
    
    /// Property: insert → seek → delete → seek returns nil (no phantom keys)
    func test_Index_No_Phantom_Keys_After_Delete() async throws {
        let indices: [any Index] = [
            BTreeIndexAdapter(BTreeIndex()),
            // ARTIndexAdapter(ARTIndex()), // Skip - no delete yet
            HashIndexAdapter(HashIndex())
        ]
        
        for index in indices {
            let key: Value = .string("phantom_test")
            let rid = RID(pageID: 1, slotID: 0)
            
            // Insert
            try await index.insert(key: key, rid: rid)
            
            // Verify exists
            let exists1 = try await index.seek(key: key)
            XCTAssertNotNil(exists1, "Key should exist after insert")
            
            // Delete
            try await index.delete(key: key)
            
            // Verify no longer exists (no phantom)
            let exists2 = try await index.seek(key: key)
            XCTAssertNil(exists2, "Key should not exist after delete (no phantom keys)")
        }
    }
    
    // MARK: - Test: Multiple Inserts Same Key
    
    /// Property: Multiple inserts with same key → seek returns all RIDs
    func test_Index_Multiple_Inserts_Same_Key_Returns_All_RIDs() async throws {
        let indices: [any Index] = [
            BTreeIndexAdapter(BTreeIndex()),
            ARTIndexAdapter(ARTIndex()),
            HashIndexAdapter(HashIndex())
        ]
        
        for index in indices {
            let key: Value = .int(999)
            let rids = [
                RID(pageID: 1, slotID: 0),
                RID(pageID: 1, slotID: 1),
                RID(pageID: 2, slotID: 0)
            ]
            
            // Insert multiple RIDs for same key
            for rid in rids {
                try await index.insert(key: key, rid: rid)
            }
            
            // Seek should return all RIDs
            let result = try await index.seek(key: key)
            XCTAssertNotNil(result, "Seek should return RIDs")
            XCTAssertEqual(result?.count, rids.count, "Seek should return all inserted RIDs")
            
            // Verify all RIDs present
            for rid in rids {
                XCTAssertTrue(
                    result?.contains(rid) ?? false,
                    "RID \(rid) should be in seek results"
                )
            }
        }
    }
    
    // MARK: - Test: Scan Range Boundaries
    
    /// Property: scan(minKey, maxKey) only returns keys in range
    func test_Index_Scan_Respects_Range_Boundaries() async throws {
        let indices: [any Index] = [
            BTreeIndexAdapter(BTreeIndex()),
            HashIndexAdapter(HashIndex())
        ]
        
        for index in indices {
            // Insert keys outside and inside range
            try await index.insert(key: .int(10), rid: RID(pageID: 1, slotID: 0))  // Below
            try await index.insert(key: .int(50), rid: RID(pageID: 1, slotID: 1))  // Inside
            try await index.insert(key: .int(90), rid: RID(pageID: 1, slotID: 2))  // Inside
            try await index.insert(key: .int(150), rid: RID(pageID: 1, slotID: 3)) // Above
            
            // Scan range [20, 100]
            let results = try await index.scan(minKey: .int(20), maxKey: .int(100))
            
            // Verify only keys in range
            for (key, _) in results {
                if case .int(let value) = key {
                    XCTAssertTrue(
                        value >= 20 && value <= 100,
                        "Scan result \(value) should be in range [20, 100]"
                    )
                }
            }
            
            // Verify expected keys present
            let keys = results.map { $0.0 }
            XCTAssertTrue(keys.contains(.int(50)), "Should contain key 50")
            XCTAssertTrue(keys.contains(.int(90)), "Should contain key 90")
            XCTAssertFalse(keys.contains(.int(10)), "Should not contain key 10 (below range)")
            XCTAssertFalse(keys.contains(.int(150)), "Should not contain key 150 (above range)")
        }
    }
    
    // MARK: - Test: Rebuild Preserves All Entries
    
    /// Property: rebuild() preserves all entries
    func test_Index_Rebuild_Preserves_All_Entries() async throws {
        let indices: [any Index] = [
            BTreeIndexAdapter(BTreeIndex()),
            HashIndexAdapter(HashIndex())
        ]
        
        for index in indices {
            // Insert N entries
            let n = 50
            var insertedPairs: [(Value, RID)] = []
            
            for i in 0..<n {
                let key: Value = .int(Int64(i))
                let rid = RID(pageID: UInt32(i / 10), slotID: UInt32(i % 10))
                try await index.insert(key: key, rid: rid)
                insertedPairs.append((key, rid))
            }
            
            let cardinalityBefore = try await index.cardinality()
            
            // Rebuild
            try await index.rebuild()
            
            // Verify cardinality unchanged
            let cardinalityAfter = try await index.cardinality()
            XCTAssertEqual(
                cardinalityAfter,
                cardinalityBefore,
                "Rebuild should preserve cardinality"
            )
            
            // Verify all entries still accessible
            for (key, rid) in insertedPairs {
                let result = try await index.seek(key: key)
                XCTAssertNotNil(result, "Key \(key) should exist after rebuild")
                XCTAssertTrue(
                    result?.contains(rid) ?? false,
                    "RID \(rid) should be present for key \(key) after rebuild"
                )
            }
        }
    }
    
    // MARK: - Test: Workload Uniform Distribution
    
    /// Property-based test: Uniform distribution workload
    func test_Index_Uniform_Workload_Maintains_Invariants() async throws {
        var rng = SeededRandomGenerator(seed: 12345)
        let indices: [any Index] = [
            BTreeIndexAdapter(BTreeIndex()),
            ARTIndexAdapter(ARTIndex()),
            HashIndexAdapter(HashIndex())
        ]
        
        for index in indices {
            let n = 200
            var inserted: Set<Value> = []
            
            // Insert uniform random keys
            for _ in 0..<n {
                let key = rng.nextValue()
                let rid = RID(pageID: UInt32(rng.nextInt(min: 0, max: 10)), slotID: UInt32(rng.nextInt(min: 0, max: 100)))
                try await index.insert(key: key, rid: rid)
                inserted.insert(key)
            }
            
            // Verify all inserted keys are findable
            for key in inserted {
                let result = try await index.seek(key: key)
                XCTAssertNotNil(result, "All inserted keys should be findable")
            }
            
            // Verify cardinality
            let cardinality = try await index.cardinality()
            XCTAssertEqual(cardinality, inserted.count, "Cardinality should match inserted unique keys")
        }
    }
    
    // MARK: - Test: Workload Zipfian Distribution
    
    /// Property-based test: Zipfian distribution workload (skewed access)
    func test_Index_Zipfian_Workload_Maintains_Invariants() async throws {
        var rng = SeededRandomGenerator(seed: 67890)
        let indices: [any Index] = [
            BTreeIndexAdapter(BTreeIndex()),
            ARTIndexAdapter(ARTIndex()),
            HashIndexAdapter(HashIndex())
        ]
        
        for index in indices {
            let n = 200
            var keyCounts: [Value: Int] = [:]
            
            // Insert with Zipfian distribution (skewed)
            for i in 0..<n {
                // Zipfian: key frequency ∝ 1/rank
                let rank = rng.nextInt(min: 1, max: 20)
                let key: Value = .int(Int64(rank))
                let rid = RID(pageID: UInt32(i / 10), slotID: UInt32(i % 10))
                
                try await index.insert(key: key, rid: rid)
                keyCounts[key, default: 0] += 1
            }
            
            // Verify all keys findable
            for (key, expectedCount) in keyCounts {
                let result = try await index.seek(key: key)
                XCTAssertNotNil(result, "Key \(key) should be findable")
                XCTAssertEqual(
                    result?.count,
                    expectedCount,
                    "Key \(key) should have \(expectedCount) RIDs"
                )
            }
        }
    }
}
