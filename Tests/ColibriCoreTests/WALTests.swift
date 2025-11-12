import XCTest
@testable import ColibriCore

final class WALTests: XCTestCase {
    private func makeWAL() throws -> (FileWAL, URL) {
        let directory = try TestUtils.createTempDirectory()
        let path = directory.appendingPathComponent("wal.log")
        let wal = try FileWAL(walFilePath: path)
        return (wal, directory)
    }
    
    private func cleanup(_ directory: URL) {
        try? TestUtils.cleanupTempDirectory(directory)
    }
    
    func testInitialization() async throws {
        let (wal, directory) = try makeWAL()
        defer { cleanup(directory) }
        
        XCTAssertEqual(await wal.getCurrentLSN(), 1)
        XCTAssertEqual(await wal.getFlushedLSN(), 0)
        XCTAssertEqual(await wal.getLastCheckpointLSN(), 0)
        XCTAssertTrue(await wal.getAllRecords().isEmpty)
        XCTAssertTrue(await wal.getDirtyPageTable().isEmpty)
    }
    
    func testAppendIncrementsLSN() async throws {
        let (wal, directory) = try makeWAL()
        defer { cleanup(directory) }
        
        let lsn1 = try await wal.append(kind: .heapInsert, txID: 1, pageID: 1)
        let lsn2 = try await wal.append(kind: .heapUpdate, txID: 1, pageID: 1)
        let lsn3 = try await wal.append(kind: .heapDelete, txID: 2, pageID: 2)
        
        XCTAssertEqual(lsn1, 1)
        XCTAssertEqual(lsn2, 2)
        XCTAssertEqual(lsn3, 3)
        XCTAssertEqual(await wal.getCurrentLSN(), 4)
    }
    
    func testDirtyPageTracking() async throws {
        let (wal, directory) = try makeWAL()
        defer { cleanup(directory) }
        
        _ = try await wal.append(kind: .heapInsert, txID: 1, pageID: 10)
        _ = try await wal.append(kind: .heapUpdate, txID: 2, pageID: 20)
        
        try await wal.updatePageLSN(10, lsn: 1)
        try await wal.updatePageLSN(20, lsn: 2)
        
        let dpt = await wal.getDirtyPageTable()
        XCTAssertEqual(dpt[10], 1)
        XCTAssertEqual(dpt[20], 2)
    }
    
    func testCrashLifecycle() async throws {
        let (wal, directory) = try makeWAL()
        defer { cleanup(directory) }
        
        _ = try await wal.append(kind: .heapInsert, txID: 1, pageID: 1)
        await wal.simulateCrash()
        
        do {
            _ = try await wal.append(kind: .heapUpdate, txID: 1, pageID: 1)
            XCTFail("Expected crash error")
        } catch DBError.crash {
            // expected
        } catch {
            XCTFail("Unexpected error: \(error)")
        }
        
        try await wal.recover()
        let lsn = try await wal.append(kind: .heapInsert, txID: 2, pageID: 2)
        XCTAssertEqual(lsn, 2)
    }
    
    func testBaselineInvariants() async throws {
        let (wal, directory) = try makeWAL()
        defer { cleanup(directory) }
        
        XCTAssertTrue(await wal.checkLogBeforeDataInvariant())
        XCTAssertTrue(await wal.checkLogOrderInvariant())
        XCTAssertTrue(await wal.checkCheckpointConsistency())
    }
}
