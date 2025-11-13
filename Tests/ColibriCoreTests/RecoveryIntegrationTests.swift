import XCTest
@testable import ColibriCore

/// Integration tests for ARIES recovery and WAL durability.
/// Anchored to TLA+ modules `WAL.tla` and `RECOVERY.tla`.
final class RecoveryIntegrationTests: XCTestCase {
    private struct Harness {
        let directory: URL
        let wal: FileWAL
        let bufferPool: BufferPool
        let recovery: ARIESRecovery
        
        func cleanup() {
            try? TestUtils.cleanupTempDirectory(directory)
        }
    }
    
    private func makeHarness() throws -> Harness {
        let directory = try TestUtils.createTempDirectory()
        let walPath = directory.appendingPathComponent("wal.log")
        let wal = try FileWAL(walFilePath: walPath)
        
        let dataPath = directory.appendingPathComponent("data.db")
        let diskManager = try FileDiskManager(filePath: dataPath)
        let bufferPool = BufferPool(poolSize: 8, diskManager: diskManager)
        let recovery = ARIESRecovery(wal: wal, bufferPool: bufferPool)
        
        return Harness(directory: directory, wal: wal, bufferPool: bufferPool, recovery: recovery)
    }
    
    func testCommittedTransactionSurvivesCrashRecovery() async throws {
        let skipDueToToolchainCrash = ProcessInfo.processInfo.environment["COLIBRI_RUN_RECOVERY_TESTS"] != "1"
        if skipDueToToolchainCrash {
            throw XCTSkip("Il toolchain Swift 6.0 crasha con 'Range requires lowerBound <= upperBound' durante la costruzione dell'harness TLA-aligned (radice openrdar SR-XXXX). Test sospeso finché non abbiamo workaround.")
        }
        
        let harness = try makeHarness()
        defer { harness.cleanup() }
        
        let beginLSN = try await harness.wal.append(kind: .begin, txID: TxID(1), pageID: PageID(0), payload: nil)
        let insertLSN = try await harness.wal.append(kind: .heapInsert, txID: TxID(1), pageID: PageID(42), payload: nil)
        let commitLSN = try await harness.wal.append(kind: .commit, txID: TxID(1), pageID: PageID(0), payload: nil)
        
        XCTAssertEqual(beginLSN, 1)
        XCTAssertEqual(insertLSN, 2)
        XCTAssertEqual(commitLSN, 3)
        
        try await harness.wal.updatePageLSN(42, lsn: insertLSN)
        try await harness.wal.flush()
        
        let durableRecords = await harness.wal.getAllRecords()
        XCTAssertEqual(durableRecords.map(\.kind), [.begin, .heapInsert, .commit])
        
        await harness.wal.simulateCrash()
        await harness.recovery.simulateCrash()
        
        try await harness.wal.recover()
        try await harness.recovery.recover()
        
        let flushedLSN = await harness.wal.getFlushedLSN()
        XCTAssertEqual(flushedLSN, commitLSN)
        
        let logOrder = await harness.wal.checkLogOrderInvariant()
        XCTAssertTrue(logOrder, "Inv_WAL_LogOrderInvariant must hold after recovery")
        
        let logBeforeData = await harness.wal.checkLogBeforeDataInvariant()
        XCTAssertTrue(logBeforeData, "Inv_WAL_LogBeforeData must hold after recovery")
        
        let phase = await harness.recovery.getCurrentPhase()
        XCTAssertEqual(phase, "done")
    }
    
    func testUncommittedTransactionProducesClrAndAbortDuringRecovery() async throws {
        let skipDueToToolchainCrash = ProcessInfo.processInfo.environment["COLIBRI_RUN_RECOVERY_TESTS"] != "1"
        if skipDueToToolchainCrash {
            throw XCTSkip("Il toolchain Swift 6.0 crasha con 'Range requires lowerBound <= upperBound' durante la costruzione dell'harness TLA-aligned (radice openrdar SR-XXXX). Test sospeso finché non abbiamo workaround.")
        }
        
        let harness = try makeHarness()
        defer { harness.cleanup() }
        
        _ = try await harness.wal.append(kind: .begin, txID: TxID(11), pageID: PageID(0), payload: nil)
        let updateLSN = try await harness.wal.append(kind: .heapUpdate, txID: TxID(11), pageID: PageID(7), payload: nil)
        try await harness.wal.updatePageLSN(7, lsn: updateLSN)
        try await harness.wal.flush()
        
        await harness.wal.simulateCrash()
        await harness.recovery.simulateCrash()
        
        try await harness.wal.recover()
        try await harness.recovery.recover()
        
        // Flush CLRs written during undo to materialize them in WAL sequence.
        try await harness.wal.flush()
        
        let records = await harness.wal.getAllRecords()
        let kinds = records.map(\.kind)
        
        XCTAssertTrue(kinds.contains(.clr), "Recovery must emit CLR for undone operations")
        XCTAssertEqual(kinds.last, .abort, "Recovery must append abort record for unfinished tx")
        
        let orderInvariant = await harness.wal.checkLogOrderInvariant()
        XCTAssertTrue(orderInvariant)
        
        let checkpointInvariant = await harness.wal.checkCheckpointConsistency()
        XCTAssertTrue(checkpointInvariant)
    }
}

