//
//  MVCCExtendedTests.swift
//  ColibrDB Tests
//
//  Extended MVCC tests for better coverage
//

import Foundation
@_spi(Experimental) import Testing
@testable import ColibriCore

@Suite("MVCC Extended Tests", .serialized)
struct MVCCExtendedTests {
    
    @Test("Transaction begins and commits successfully")
    func testBasicTransactionLifecycle() {
        let mvcc = MVCCManager()
        
        let tid: UInt64 = 1
        mvcc.begin(tid: tid)
        
        #expect(mvcc.activeTIDs.contains(tid))
        
        mvcc.commit(tid: tid)
        
        #expect(!mvcc.activeTIDs.contains(tid))
        #expect(mvcc.committedTIDs.contains(tid))
    }
    
    @Test("Transaction rollback removes from active")
    func testTransactionRollback() {
        let mvcc = MVCCManager()
        
        let tid: UInt64 = 2
        mvcc.begin(tid: tid)
        mvcc.rollback(tid: tid)
        
        #expect(!mvcc.activeTIDs.contains(tid))
        #expect(mvcc.abortedTIDs.contains(tid))
    }
    
    @Test("Register insert creates version")
    func testRegisterInsert() {
        let mvcc = MVCCManager()
        
        let tid: UInt64 = 3
        mvcc.begin(tid: tid)
        
        let row: Row = ["id": .int(1), "name": .string("test")]
        let rid = RID(pageId: 1, slotId: 0)
        
        mvcc.registerInsert(table: "test", rid: rid, row: row, tid: tid)
        
        let snapshot = mvcc.snapshot(for: tid)
        let visible = mvcc.visibleRows(table: "test", snapshot: snapshot, readerTID: tid)
        
        #expect(visible[rid] == row)
    }
    
    @Test("Snapshot isolation - uncommitted changes invisible")
    func testSnapshotIsolation() {
        let mvcc = MVCCManager()
        
        // Transaction 1: Insert
        let tid1: UInt64 = 10
        mvcc.begin(tid: tid1)
        let row: Row = ["id": .int(1)]
        let rid = RID(pageId: 1, slotId: 0)
        mvcc.registerInsert(table: "test", rid: rid, row: row, tid: tid1)
        
        // Transaction 2: Should not see T1's uncommitted insert
        let tid2: UInt64 = 11
        mvcc.begin(tid: tid2)
        let snapshot2 = mvcc.snapshot(for: tid2, isolationCutoff: tid2)
        let visible2 = mvcc.visibleRows(table: "test", snapshot: snapshot2, readerTID: tid2)
        
        #expect(visible2.isEmpty)
        
        // Commit T1
        mvcc.commit(tid: tid1)
        
        // T2 still shouldn't see it (snapshot isolation)
        let visible2After = mvcc.visibleRows(table: "test", snapshot: snapshot2, readerTID: tid2)
        #expect(visible2After.isEmpty)
        
        // New transaction should see it
        let tid3: UInt64 = 12
        mvcc.begin(tid: tid3)
        let snapshot3 = mvcc.snapshot(for: tid3)
        let visible3 = mvcc.visibleRows(table: "test", snapshot: snapshot3, readerTID: tid3)
        
        #expect(visible3.count == 1)
    }
    
    @Test("Delete marks row with tombstone")
    func testRegisterDelete() {
        let mvcc = MVCCManager()
        
        let tid: UInt64 = 20
        mvcc.begin(tid: tid)
        
        let row: Row = ["id": .int(1)]
        let rid = RID(pageId: 1, slotId: 0)
        
        mvcc.registerInsert(table: "test", rid: rid, row: row, tid: nil) // Committed
        mvcc.registerDelete(table: "test", rid: rid, row: row, tid: tid)
        
        let snapshot = mvcc.snapshot(for: tid)
        let visible = mvcc.visibleRows(table: "test", snapshot: snapshot, readerTID: tid)
        
        #expect(visible.isEmpty) // Deleted within same transaction
    }
    
    @Test("Concurrent transactions see correct versions")
    func testConcurrentTransactions() {
        let mvcc = MVCCManager()
        
        // Setup: Insert row outside any transaction
        let rid = RID(pageId: 1, slotId: 0)
        let originalRow: Row = ["id": .int(1), "value": .int(100)]
        mvcc.registerInsert(table: "test", rid: rid, row: originalRow, tid: nil)
        
        // T1: Read
        let tid1: UInt64 = 30
        mvcc.begin(tid: tid1)
        let snapshot1 = mvcc.snapshot(for: tid1)
        let visible1 = mvcc.visibleRows(table: "test", snapshot: snapshot1, readerTID: tid1)
        #expect(visible1[rid]?["value"] == .int(100))
        
        // T2: Update
        let tid2: UInt64 = 31
        mvcc.begin(tid: tid2)
        mvcc.registerDelete(table: "test", rid: rid, row: originalRow, tid: tid2)
        let updatedRow: Row = ["id": .int(1), "value": .int(200)]
        mvcc.registerInsert(table: "test", rid: rid, row: updatedRow, tid: tid2)
        mvcc.commit(tid: tid2)
        
        // T1 should still see old value (snapshot isolation)
        let stillVisible1 = mvcc.visibleRows(table: "test", snapshot: snapshot1, readerTID: tid1)
        #expect(stillVisible1[rid]?["value"] == .int(100))
        
        mvcc.commit(tid: tid1)
        
        // New transaction sees updated value
        let tid3: UInt64 = 32
        mvcc.begin(tid: tid3)
        let snapshot3 = mvcc.snapshot(for: tid3)
        let visible3 = mvcc.visibleRows(table: "test", snapshot: snapshot3, readerTID: tid3)
        #expect(visible3[rid]?["value"] == .int(200))
    }
    
    @Test("Undo insert removes version")
    func testUndoInsert() {
        let mvcc = MVCCManager()
        
        let tid: UInt64 = 40
        mvcc.begin(tid: tid)
        
        let row: Row = ["id": .int(1)]
        let rid = RID(pageId: 1, slotId: 0)
        
        mvcc.registerInsert(table: "test", rid: rid, row: row, tid: tid)
        mvcc.undoInsert(table: "test", rid: rid, tid: tid)
        
        let snapshot = mvcc.snapshot(for: tid)
        let visible = mvcc.visibleRows(table: "test", snapshot: snapshot, readerTID: tid)
        
        #expect(visible.isEmpty)
    }
    
    @Test("Multiple tables isolated")
    func testMultipleTables() {
        let mvcc = MVCCManager()
        
        let tid: UInt64 = 50
        mvcc.begin(tid: tid)
        
        let row1: Row = ["id": .int(1)]
        let rid1 = RID(pageId: 1, slotId: 0)
        mvcc.registerInsert(table: "table1", rid: rid1, row: row1, tid: tid)
        
        let row2: Row = ["id": .int(2)]
        let rid2 = RID(pageId: 1, slotId: 0)
        mvcc.registerInsert(table: "table2", rid: rid2, row: row2, tid: tid)
        
        let snapshot = mvcc.snapshot(for: tid)
        
        let visible1 = mvcc.visibleRows(table: "table1", snapshot: snapshot, readerTID: tid)
        let visible2 = mvcc.visibleRows(table: "table2", snapshot: snapshot, readerTID: tid)
        
        #expect(visible1.count == 1)
        #expect(visible2.count == 1)
        #expect(visible1[rid1] != nil)
        #expect(visible2[rid2] != nil)
    }
}

