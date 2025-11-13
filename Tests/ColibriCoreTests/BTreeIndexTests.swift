import XCTest
@testable import ColibriCore

/// Test di correttezza per il B+Tree (spec/BTree.tla).
final class BTreeIndexTests: XCTestCase {
    private func makeRID(_ i: Int) -> RID {
        RID(pageID: UInt64(i / 32), slotID: UInt32(i % 32))
    }
    
    func testInsertAndSearchReturnsInsertedRID() throws {
        let index = BTreeIndex()
        
        for i in 0..<32 {
            try index.insert(key: .int(Int64(i)), rid: makeRID(i))
        }
        
        for i in 0..<32 {
            let rids = index.search(key: .int(Int64(i)))
            XCTAssertEqual(rids, [makeRID(i)], "La ricerca deve restituire il RID inserito per la chiave \(i)")
        }
    }
    
    func testRangeScanReturnsSortedKeysWithinBounds() throws {
        let index = BTreeIndex()
        
        for i in stride(from: 0, to: 50, by: 5) {
            try index.insert(key: .int(Int64(i)), rid: makeRID(i))
        }
        
        let results = index.rangeScan(minKey: .int(10), maxKey: .int(30))
        let extractedKeys = results.map { $0.0 }
        
        XCTAssertEqual(extractedKeys, [.int(10), .int(15), .int(20), .int(25), .int(30)])
        XCTAssertTrue(results.allSatisfy { !$0.1.isEmpty }, "Ogni voce deve avere almeno un RID associato")
    }
    
    func testDeleteRemovesKeyAndPreservesOtherEntries() throws {
        let index = BTreeIndex()
        try index.insert(key: .int(7), rid: makeRID(7))
        try index.insert(key: .int(21), rid: makeRID(21))
        
        XCTAssertEqual(index.search(key: .int(7)), [makeRID(7)])
        
        try index.delete(key: .int(7))
        
        XCTAssertNil(index.search(key: .int(7)))
        XCTAssertNotNil(index.search(key: .int(21)))
        XCTAssertTrue(index.checkKeyOrderInvariant())
        XCTAssertTrue(index.checkBalancedHeightInvariant())
    }
}

