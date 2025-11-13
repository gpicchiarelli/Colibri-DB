import XCTest
import Foundation
@testable import ColibriCore

final class MinimalDatabaseTest {
    
    func testDatabaseCreation() throws {
        print("Creating temp directory...")
        let tempDir = FileManager.default.temporaryDirectory.appendingPathComponent(UUID().uuidString)
        try FileManager.default.createDirectory(at: tempDir, withIntermediateDirectories: true)
        
        print("Creating config...")
        let config = ColibrìDBConfiguration(
            dataDirectory: tempDir,
            bufferPoolSize: 10,
            maxConnections: 5,
            walBufferSize: 1024,
            checkpointInterval: 300,
            logLevel: .info,
            enableStatistics: false,
            enableAutoAnalyze: false
        )
        
        print("Creating database instance...")
        let _ = try ColibrìDB(config: config)
        
        print("Database instance created successfully!")
        
        // Cleanup
        try? FileManager.default.removeItem(at: tempDir)
    }
}


