import XCTest
import Foundation
@testable import ColibriCore

final class IsolatedComponentTest {
    
    func testCatalogCreation() throws {
        print("Creating Catalog...")
        let _ = Catalog()
        print("Catalog created successfully!")
    }
    
    func testFileWALCreation() throws {
        print("Creating temp directory...")
        let tempDir = FileManager.default.temporaryDirectory.appendingPathComponent(UUID().uuidString)
        try FileManager.default.createDirectory(at: tempDir, withIntermediateDirectories: true)
        
        print("Creating FileWAL...")
        let _ = try FileWAL(walFilePath: tempDir.appendingPathComponent("wal.log"))
        print("FileWAL created successfully!")
        
        try? FileManager.default.removeItem(at: tempDir)
    }
    
    func testBufferPoolCreation() throws {
        print("Creating temp directory...")
        let tempDir = FileManager.default.temporaryDirectory.appendingPathComponent(UUID().uuidString)
        try FileManager.default.createDirectory(at: tempDir, withIntermediateDirectories: true)
        
        print("Creating FileDiskManager...")
        let diskManager = try FileDiskManager(filePath: tempDir.appendingPathComponent("data.db"))
        
        print("Creating BufferPool...")
        let _ = BufferPool(poolSize: 10, diskManager: diskManager)
        print("BufferPool created successfully!")
        
        try? FileManager.default.removeItem(at: tempDir)
    }
    
    func testMVCCManagerCreation() throws {
        print("Creating MVCCManager...")
        let _ = MVCCManager()
        print("MVCCManager created successfully!")
    }
    
    func testHybridLogicalClockCreation() throws {
        print("Creating HybridLogicalClock...")
        let _ = HybridLogicalClock(nodeID: 1)
        print("HybridLogicalClock created successfully!")
    }
}


