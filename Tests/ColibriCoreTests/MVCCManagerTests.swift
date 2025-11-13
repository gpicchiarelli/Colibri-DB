import XCTest
@testable import ColibriCore

/// Test di base per l’implementazione MVCC (spec/MVCC.tla).
/// Verificano Snapshot Isolation, visibilità delle versioni e garbage degli abort.
final class MVCCManagerTests: XCTestCase {
    private func makeManager() -> MVCCManager {
        MVCCManager()
    }
    
    func testBeginTransactionCreatesSnapshot() async throws {
        let mvcc = makeManager()
        
        let snapshot1 = try await mvcc.beginTransaction(txId: 1)
        XCTAssertEqual(snapshot1.txId, 1)
        XCTAssertEqual(snapshot1.timestamp, 1)
        XCTAssertEqual(snapshot1.activeTransactions, [1])
        XCTAssertTrue(snapshot1.committedTransactions.isEmpty)
        
        let snapshot2 = try await mvcc.beginTransaction(txId: 2)
        XCTAssertEqual(snapshot2.txId, 2)
        XCTAssertEqual(snapshot2.timestamp, 2)
        XCTAssertEqual(snapshot2.activeTransactions, [1, 2])
    }
    
    func testCommittedVersionVisibleToLaterSnapshot() async throws {
        let mvcc = makeManager()
        
        _ = try await mvcc.beginTransaction(txId: 1)
        try await mvcc.write(txId: 1, key: "user:1", value: Value.int(Int64(42)))
        try await mvcc.commit(txId: 1)
        
        _ = try await mvcc.beginTransaction(txId: 2)
        let value = try await mvcc.read(txId: 2, key: "user:1")
        XCTAssertEqual(value, Value.int(Int64(42)))
        
        let snapshotInvariant = await mvcc.checkSnapshotIsolationInvariant()
        XCTAssertTrue(snapshotInvariant, "Inv_MVCC_SnapshotIsolation deve restare vero")
    }
    
    func testAbortRemovesUncommittedVersion() async throws {
        let mvcc = makeManager()
        
        _ = try await mvcc.beginTransaction(txId: 10)
        try await mvcc.write(txId: 10, key: "order:1", value: Value.string("pending"))
        try await mvcc.abort(txId: 10)
        
        _ = try await mvcc.beginTransaction(txId: 20)
        let readValue = try await mvcc.read(txId: 20, key: "order:1")
        XCTAssertNil(readValue)
        
        let wwInvariant = await mvcc.checkNoWriteWriteConflictsInvariant()
        XCTAssertTrue(wwInvariant, "Inv_MVCC_NoWriteWriteConflicts deve restare vero")
    }
}

