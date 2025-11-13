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
        
        let current = await wal.getCurrentLSN()
        let flushed = await wal.getFlushedLSN()
        let checkpoint = await wal.getLastCheckpointLSN()
        let records = await wal.getAllRecords()
        let dpt = await wal.getDirtyPageTable()
        
        XCTAssertEqual(current, 1)
        XCTAssertEqual(flushed, 0)
        XCTAssertEqual(checkpoint, 0)
        XCTAssertTrue(records.isEmpty)
        XCTAssertTrue(dpt.isEmpty)
    }
    
    func testAppendIncrementsLSN() async throws {
        let (wal, directory) = try makeWAL()
        defer { cleanup(directory) }
        
        let lsn1 = try await wal.append(kind: .heapInsert, txID: TxID(1), pageID: PageID(1), payload: nil)
        let lsn2 = try await wal.append(kind: .heapUpdate, txID: TxID(1), pageID: PageID(1), payload: nil)
        let lsn3 = try await wal.append(kind: .heapDelete, txID: TxID(2), pageID: PageID(2), payload: nil)
        
        XCTAssertEqual(lsn1, 1)
        XCTAssertEqual(lsn2, 2)
        XCTAssertEqual(lsn3, 3)
        let current = await wal.getCurrentLSN()
        XCTAssertEqual(current, 4)
    }
    
    func testDirtyPageTracking() async throws {
        let (wal, directory) = try makeWAL()
        defer { cleanup(directory) }
        
        _ = try await wal.append(kind: .heapInsert, txID: TxID(1), pageID: PageID(10), payload: nil)
        _ = try await wal.append(kind: .heapUpdate, txID: TxID(2), pageID: PageID(20), payload: nil)
        
        try await wal.updatePageLSN(PageID(10), lsn: LSN(1))
        try await wal.updatePageLSN(PageID(20), lsn: LSN(2))
        
        let dpt = await wal.getDirtyPageTable()
        XCTAssertEqual(dpt[PageID(10)], LSN(1))
        XCTAssertEqual(dpt[PageID(20)], LSN(2))
    }
    
    func testCrashLifecycle() async throws {
        let (wal, directory) = try makeWAL()
        defer { cleanup(directory) }
        
        _ = try await wal.append(kind: .heapInsert, txID: TxID(1), pageID: PageID(1), payload: nil)
        await wal.simulateCrash()
        
        do {
            _ = try await wal.append(kind: .heapUpdate, txID: TxID(1), pageID: PageID(1), payload: nil)
            XCTFail("Expected crash error")
        } catch DBError.crash {
            // expected
        } catch {
            XCTFail("Unexpected error: \(error)")
        }
        
        try await wal.recover()
        let lsn = try await wal.append(kind: .heapInsert, txID: TxID(2), pageID: PageID(2), payload: nil)
        XCTAssertGreaterThan(lsn, 0)
    }
    
}
