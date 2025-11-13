import XCTest
@testable import ColibriCore

/// Contract tests: parametric, property-based
final class IndexContractTests2: XCTestCase {
    
    // MARK: - Contract: insert→seek returns value
    func testInsertSeekContract() async throws {
        let index: IndexProtocol = BTreeIndexWrapper(BTreeIndex())
        
        let testRID = RID(pageID: PageID(1), slotID: UInt32(0))
        try await index.insert(key: Value.int(42), rid: testRID)
        let result = try await index.seek(key: Value.int(42))
        
        XCTAssertNotNil(result, "Contract: insert→seek must return inserted RID")
        XCTAssertEqual(result?.first, testRID, "Contract: insert→seek must return inserted RID")
    }
    
    // MARK: - Contract: scan returns ordered sequence
    func testScanOrderedContract() async throws {
        let index: IndexProtocol = BTreeIndexWrapper(BTreeIndex())
        
        let rid1 = RID(pageID: PageID(1), slotID: UInt32(0))
        let rid2 = RID(pageID: PageID(1), slotID: UInt32(1))
        let rid3 = RID(pageID: PageID(1), slotID: UInt32(2))
        
        try await index.insert(key: Value.int(3), rid: rid3)
        try await index.insert(key: Value.int(1), rid: rid1)
        try await index.insert(key: Value.int(2), rid: rid2)
        
        let results = try await index.scan(minKey: Value.int(1), maxKey: Value.int(4))
        
        XCTAssertEqual(results.count, 3, "Scan must return all keys in range")
        XCTAssertEqual(results[0].0, Value.int(1), "Scan must be ordered")
        XCTAssertEqual(results[1].0, Value.int(2), "Scan must be ordered")
        XCTAssertEqual(results[2].0, Value.int(3), "Scan must be ordered")
    }
    
    // MARK: - Contract: delete reduces cardinality
    func testDeleteContract() async throws {
        let index: IndexProtocol = BTreeIndexWrapper(BTreeIndex())
        
        let testRID = RID(pageID: PageID(1), slotID: UInt32(0))
        try await index.insert(key: Value.int(1), rid: testRID)
        try await index.delete(key: Value.int(1))
        
        let result = try await index.seek(key: Value.int(1))
        XCTAssertNil(result, "Delete must remove key")
    }
    
    // MARK: - Contract: no phantom keys
    func testNoPhantomKeys() async throws {
        let index: IndexProtocol = BTreeIndexWrapper(BTreeIndex())
        
        // Insert and delete
        let testRID = RID(pageID: PageID(1), slotID: UInt32(0))
        try await index.insert(key: Value.int(1), rid: testRID)
        try await index.delete(key: Value.int(1))
        
        // Scan should not return deleted key
        let results = try await index.scan(minKey: Value.int(1), maxKey: Value.int(2))
        XCTAssertTrue(results.isEmpty, "No phantom keys after delete")
    }
}


