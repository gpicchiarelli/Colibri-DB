import Foundation
import Testing
@testable import ColibriCore

@Suite("Transaction Manager")
struct TransactionManagerTests {
    // MARK: - Test Doubles
    
    private actor StubWALManager: TransactionWALManager {
        private(set) var records: [(TransactionID, String)] = []
        
        func appendRecord(txId: TransactionID, record: String) async throws {
            records.append((txId, record))
        }
        
        func flushLog() async throws {
            // no-op for tests
        }
    }
    
    private actor StubMVCCManager: TransactionMVCCManager {
        private var store: [String: String] = [:]
        
        func beginTransaction(txId: TxID) async throws -> Snapshot {
            Snapshot(
                txID: txId,
                startTS: UInt64(txId),
                xmin: UInt64(txId),
                xmax: UInt64(txId + 1),
                activeTxAtStart: []
            )
        }
        
        func read(txId: TxID, key: String) async throws -> String? {
            store[key]
        }
        
        func write(txId: TxID, key: String, value: String) async throws {
            store[key] = value
        }
        
        func commit(txId: TxID) async throws {}
        func abort(txId: TxID) async throws {}
    }
    
    private func makeManager() -> (TransactionManager, StubWALManager, StubMVCCManager) {
        let wal = StubWALManager()
        let mvcc = StubMVCCManager()
        let manager = TransactionManager(
            walManager: wal,
            mvccManager: mvcc,
            lockManager: nil
        )
        return (manager, wal, mvcc)
    }
    
    // MARK: - Tests
    
    @Test("Begin transaction allocates sequential TxID")
    func testBeginTransaction() async throws {
        let (manager, _, _) = makeManager()
        
        let first = try await manager.beginTransaction()
        let second = try await manager.beginTransaction()
        
        #expect(first == 1)
        #expect(second == 2)
        #expect(await manager.isTransactionActive(txId: first))
        #expect(await manager.isTransactionActive(txId: second))
        #expect(await manager.getActiveTransactionCount() == 2)
    }
    
    @Test("Commit transitions transaction to committed state")
    func testCommitTransaction() async throws {
        let (manager, _, _) = makeManager()
        
        let txId = try await manager.beginTransaction()
        try await manager.commitTransaction(txId: txId)
        
        #expect(!(await manager.isTransactionActive(txId: txId)))
        #expect(await manager.isTransactionCommitted(txId: txId))
        #expect(!(await manager.isTransactionAborted(txId: txId)))
        #expect(await manager.getActiveTransactionCount() == 0)
    }
    
    @Test("Abort transitions transaction to aborted state")
    func testAbortTransaction() async throws {
        let (manager, _, _) = makeManager()
        
        let txId = try await manager.beginTransaction()
        try await manager.abortTransaction(txId: txId)
        
        #expect(!(await manager.isTransactionActive(txId: txId)))
        #expect(await manager.isTransactionAborted(txId: txId))
        #expect(!(await manager.isTransactionCommitted(txId: txId)))
    }
    
    @Test("Prepare marks transaction as prepared")
    func testPrepareTransaction() async throws {
        let (manager, _, _) = makeManager()
        
        let txId = try await manager.beginTransaction()
        try await manager.prepareTransaction(txId: txId)
        
        #expect(await manager.isTransactionPrepared(txId: txId))
    }
    
    @Test("Two-phase commit decision reflects participant votes")
    func testTwoPhaseCommitDecision() async throws {
        let (manager, _, _) = makeManager()
        
        let txId = try await manager.beginTransaction()
        try await manager.receiveVote(txId: txId, participant: "node1", vote: true)
        try await manager.receiveVote(txId: txId, participant: "node2", vote: true)
        
        let decision = try await manager.makeDecision(txId: txId)
        #expect(decision == true)
        
        try await manager.sendCommitAbort(txId: txId, decision: decision)
        #expect(await manager.isTransactionCommitted(txId: txId))
    }
    
    @Test("Two-phase commit aborts on negative vote")
    func testTwoPhaseCommitAbort() async throws {
        let (manager, _, _) = makeManager()
        
        let txId = try await manager.beginTransaction()
        try await manager.receiveVote(txId: txId, participant: "node1", vote: true)
        try await manager.receiveVote(txId: txId, participant: "node2", vote: false)
        
        let decision = try await manager.makeDecision(txId: txId)
        #expect(decision == false)
        
        try await manager.sendCommitAbort(txId: txId, decision: decision)
        #expect(await manager.isTransactionAborted(txId: txId))
    }
    
    @Test("Invariants hold after basic workflow")
    func testInvariants() async throws {
        let (manager, _, _) = makeManager()
        
        let txId = try await manager.beginTransaction()
        try await manager.prepareTransaction(txId: txId)
        try await manager.commitTransaction(txId: txId)
        
        #expect(await manager.checkAllInvariants())
    }
}

