import XCTest
@testable import ColibriCore

final class TransactionManagerTests: XCTestCase {
    private actor StubWALManager: TransactionWALManager {
        func appendRecord(txId: TransactionID, record: String) async throws {}
        func flushLog() async throws {}
    }
    
    private actor StubMVCCManager: TransactionMVCCManager {
        func beginTransaction(txId: TxID) async throws -> Snapshot {
            Snapshot(txID: txId, startTS: UInt64(txId), xmin: UInt64(txId), xmax: UInt64(txId + 1), activeTxAtStart: [])
        }
        
        func read(txId: TxID, key: String) async throws -> String? { nil }
        func write(txId: TxID, key: String, value: String) async throws {}
        func commit(txId: TxID) async throws {}
        func abort(txId: TxID) async throws {}
    }
    
    private func makeManager() -> (TransactionManager, StubWALManager, StubMVCCManager) {
        let wal = StubWALManager()
        let mvcc = StubMVCCManager()
        let manager = TransactionManager(walManager: wal, mvccManager: mvcc, lockManager: nil)
        return (manager, wal, mvcc)
    }
    
    func testBeginTransactionAssignsSequentialIds() async throws {
        let (manager, _, _) = makeManager()
        
        let first = try await manager.beginTransaction()
        let second = try await manager.beginTransaction()
        
        XCTAssertEqual(first, 1)
        XCTAssertEqual(second, 2)
        
        let firstActive = await manager.isTransactionActive(txId: first)
        let secondActive = await manager.isTransactionActive(txId: second)
        XCTAssertTrue(firstActive)
        XCTAssertTrue(secondActive)
    }
    
    func testCommitTransitionsState() async throws {
        let (manager, _, _) = makeManager()
        
        let txId = try await manager.beginTransaction()
        try await manager.commitTransaction(txId: txId)
        
        let active = await manager.isTransactionActive(txId: txId)
        let committed = await manager.isTransactionCommitted(txId: txId)
        let aborted = await manager.isTransactionAborted(txId: txId)
        XCTAssertFalse(active)
        XCTAssertTrue(committed)
        XCTAssertFalse(aborted)
    }
    
    func testAbortTransitionsState() async throws {
        let (manager, _, _) = makeManager()
        
        let txId = try await manager.beginTransaction()
        try await manager.abortTransaction(txId: txId)
        
        let active = await manager.isTransactionActive(txId: txId)
        let aborted = await manager.isTransactionAborted(txId: txId)
        let committed = await manager.isTransactionCommitted(txId: txId)
        XCTAssertFalse(active)
        XCTAssertTrue(aborted)
        XCTAssertFalse(committed)
    }
    
    func testPrepareMarksPrepared() async throws {
        let (manager, _, _) = makeManager()
        
        let txId = try await manager.beginTransaction()
        try await manager.prepareTransaction(txId: txId)
        
        let prepared = await manager.isTransactionPrepared(txId: txId)
        XCTAssertTrue(prepared)
    }
    
    func testTwoPhaseCommitDecision() async throws {
        let (manager, _, _) = makeManager()
        
        let txId = try await manager.beginTransaction()
        try await manager.receiveVote(txId: txId, participant: "node1", vote: true)
        try await manager.receiveVote(txId: txId, participant: "node2", vote: true)
        
        let decision = try await manager.makeDecision(txId: txId)
        XCTAssertTrue(decision)
        
        try await manager.sendCommitAbort(txId: txId, decision: decision)
        let committed = await manager.isTransactionCommitted(txId: txId)
        XCTAssertTrue(committed)
    }
    
    func testTwoPhaseCommitAbort() async throws {
        let (manager, _, _) = makeManager()
        
        let txId = try await manager.beginTransaction()
        try await manager.receiveVote(txId: txId, participant: "node1", vote: true)
        try await manager.receiveVote(txId: txId, participant: "node2", vote: false)
        
        let decision = try await manager.makeDecision(txId: txId)
        XCTAssertFalse(decision)
        
        try await manager.sendCommitAbort(txId: txId, decision: decision)
        let aborted = await manager.isTransactionAborted(txId: txId)
        XCTAssertTrue(aborted)
    }
    
    func testInvariantsAfterCommit() async throws {
        let (manager, _, _) = makeManager()
        
        let txId = try await manager.beginTransaction()
        try await manager.commitTransaction(txId: txId)
        
        let invariantsHold = await manager.checkAllInvariants()
        XCTAssertTrue(invariantsHold)
    }
}
