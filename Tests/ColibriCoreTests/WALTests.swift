import Foundation
import Testing
@testable import ColibriCore

@Suite("WAL Core")
struct WALTests {
    // MARK: - Helpers
    
    private func makeWAL(config: GroupCommitConfig = GroupCommitConfig()) throws -> (FileWAL, URL) {
        let directory = try TestUtils.createTempDirectory()
        let walPath = directory.appendingPathComponent("wal.log")
        let wal = try FileWAL(walFilePath: walPath, config: config)
        return (wal, directory)
    }
    
    private func cleanup(_ directory: URL) {
        try? TestUtils.cleanupTempDirectory(directory)
    }
    
    // MARK: - Tests
    
    @Test("Initialization sets base LSNs")
    func testInitialization() async throws {
        let (wal, directory) = try makeWAL()
        defer { cleanup(directory) }
        
        #expect(await wal.getCurrentLSN() == 1)
        #expect(await wal.getFlushedLSN() == 0)
        #expect(await wal.getLastCheckpointLSN() == 0)
        #expect(await wal.getDirtyPageTable().isEmpty)
        #expect(await wal.getActiveTransactionTable().isEmpty)
    }
    
    @Test("Appending assigns sequential LSNs")
    func testAppendIncrementsLSN() async throws {
        let (wal, directory) = try makeWAL()
        defer { cleanup(directory) }
        
        let first = try await wal.append(kind: .heapInsert, txID: 1, pageID: 1, payload: nil)
        let second = try await wal.append(kind: .heapUpdate, txID: 1, pageID: 1, payload: nil)
        
        #expect(first == 1)
        #expect(second == 2)
        #expect(await wal.getCurrentLSN() == 3)
        #expect(await wal.getFlushedLSN() == 0)  // no flush yet
    }
    
    @Test("Flush persists pending records")
    func testFlushPersistsRecords() async throws {
        let (wal, directory) = try makeWAL()
        defer { cleanup(directory) }
        
        _ = try await wal.append(kind: .heapInsert, txID: 1, pageID: 1)
        _ = try await wal.append(kind: .heapUpdate, txID: 2, pageID: 2)
        
        try await wal.flush()
        
        #expect(await wal.getFlushedLSN() == 2)
        #expect(await wal.getAllRecords().count == 2)
    }
    
    @Test("Checkpoint updates last checkpoint LSN")
    func testCheckpoint() async throws {
        let (wal, directory) = try makeWAL()
        defer { cleanup(directory) }
        
        _ = try await wal.append(kind: .heapInsert, txID: 1, pageID: 1)
        try await wal.flush()
        
        let checkpointLSN = try await wal.checkpoint()
        
        #expect(checkpointLSN == 3)
        #expect(await wal.getLastCheckpointLSN() == checkpointLSN)
    }
    
    @Test("Crash blocks operations until recovery")
    func testCrashLifecycle() async throws {
        let (wal, directory) = try makeWAL()
        defer { cleanup(directory) }
        
        _ = try await wal.append(kind: .heapInsert, txID: 1, pageID: 1)
        try await wal.flush()
        
        await wal.simulateCrash()
        
        #expect(throws: DBError.crash) {
            try await wal.append(kind: .heapUpdate, txID: 1, pageID: 1)
        }
        #expect(throws: DBError.crash) {
            try await wal.flush()
        }
        #expect(throws: DBError.crash) {
            try await wal.checkpoint()
        }
        
        try await wal.recover()
        
        #expect(await wal.getCurrentLSN() == 3)
        #expect(await wal.getFlushedLSN() == 2)
        
        // Append succeeds again after recovery
        let postRecoveryLSN = try await wal.append(kind: .heapDelete, txID: 2, pageID: 2)
        #expect(postRecoveryLSN == 3)
    }
    
    @Test("Dirty page tracking maintains recLSN order")
    func testDirtyPageTracking() async throws {
        let (wal, directory) = try makeWAL()
        defer { cleanup(directory) }
        
        _ = try await wal.append(kind: .heapInsert, txID: 1, pageID: 10)
        _ = try await wal.append(kind: .heapUpdate, txID: 1, pageID: 20)
        
        try await wal.updatePageLSN(10, lsn: 1)
        try await wal.updatePageLSN(20, lsn: 2)
        
        let dirtyTable = await wal.getDirtyPageTable()
        #expect(dirtyTable[10] == 1)
        #expect(dirtyTable[20] == 2)
        
        // Flushing should not drop dirty entries until applied
        try await wal.flush()
        let dirtyAfterFlush = await wal.getDirtyPageTable()
        #expect(dirtyAfterFlush.count == 2)
        
        // Applying clears entry
        try await wal.applyToDataPage(10)
        let dirtyAfterApply = await wal.getDirtyPageTable()
        #expect(dirtyAfterApply[10] == nil)
        #expect(dirtyAfterApply[20] == 2)
    }
}

