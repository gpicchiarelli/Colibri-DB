import Testing
import Foundation
@testable import ColibriCore

@Suite("Step By Step Init Test")
struct StepByStepInitTest {
    
    @Test("Initialize Components Step By Step")
    func testStepByStepInit() throws {
        print("Step 1: Creating temp directory...")
        let tempDir = FileManager.default.temporaryDirectory.appendingPathComponent(UUID().uuidString)
        try FileManager.default.createDirectory(at: tempDir, withIntermediateDirectories: true)
        
        print("Step 2: Creating Catalog...")
        let catalog = Catalog()
        
        print("Step 3: Creating FileWAL...")
        let wal = try FileWAL(walFilePath: tempDir.appendingPathComponent("wal.log"))
        
        print("Step 4: Creating FileDiskManager...")
        let diskManager = try FileDiskManager(filePath: tempDir.appendingPathComponent("data.db"))
        
        print("Step 5: Creating BufferPool...")
        let bufferPool = BufferPool(poolSize: 10, diskManager: diskManager)
        
        print("Step 6: Creating MVCCManager...")
        let mvccManager = MVCCManager()
        
        print("Step 7: Creating WAL Adapter...")
        let walAdapter = wal.asTransactionWALManager()
        
        print("Step 8: Creating MVCC Adapter...")
        let mvccAdapter = mvccManager.asTransactionMVCCManager()
        
        print("Step 9: Creating TransactionManager...")
        let transactionManager = TransactionManager(
            walManager: walAdapter,
            mvccManager: mvccAdapter,
            lockManager: nil
        )
        
        print("Step 10: Creating LockManager...")
        let _ = LockManager(transactionManager: transactionManager)
        
        print("Step 11: Creating ARIESRecovery...")
        let _ = ARIESRecovery(wal: wal, bufferPool: bufferPool)
        
        print("Step 12: Creating QueryExecutor...")
        let _ = QueryExecutor(transactionManager: transactionManager, catalog: catalog)
        
        print("Step 13: Creating StatisticsManagerActor...")
        let _ = StatisticsManagerActor()
        
        print("Step 14: Creating QueryOptimizer...")
        let _ = QueryOptimizer(catalog: catalog, statistics: StatisticsManagerActor())
        
        print("Step 15: Creating StatisticsMaintenanceManager...")
        let _ = StatisticsMaintenanceManager()
        
        print("Step 16: Creating HybridLogicalClock...")
        let clock = HybridLogicalClock(nodeID: 1)
        
        print("Step 17: Creating SchemaEvolutionManager...")
        let _ = SchemaEvolutionManager(
            transactionManager: transactionManager,
            catalog: catalog,
            clock: clock
        )
        
        print("Step 18: Creating WireProtocolHandler...")
        let _ = WireProtocolHandler()
        
        print("Step 19: Creating AuthenticationManager...")
        let authManager = AuthenticationManager()
        
        print("Step 20: Creating DatabaseServer...")
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
        
        // Create a mock database for the server
        print("Step 21: Creating ColibrìDB instance...")
        let db = try ColibrìDB(config: config)
        
        print("All components created successfully!")
        
        try? FileManager.default.removeItem(at: tempDir)
    }
}

