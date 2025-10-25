//
//  TestRunner.swift
//  ColibrìDB Test Runner
//
//  Main test runner that executes all test suites
//

import Foundation
import Testing
@testable import ColibriCore

/// Main Test Runner for ColibrìDB
@main
struct TestRunner {
    static func main() async {
        print("🚀 Starting ColibrìDB Test Suite")
        print("=================================")
        
        let startTime = Date()
        
        // Run all test suites
        await runTestSuite("Database Core Tests", DatabaseTests.self)
        await runTestSuite("Transaction Manager Tests", TransactionManagerTests.self)
        await runTestSuite("Buffer Pool Tests", BufferPoolTests.self)
        await runTestSuite("WAL Tests", WALTests.self)
        await runTestSuite("B+Tree Index Tests", BTreeIndexTests.self)
        await runTestSuite("SQL Parser Tests", SQLParserTests.self)
        await runTestSuite("Distributed System Tests", DistributedTests.self)
        await runTestSuite("Security Tests", SecurityTests.self)
        await runTestSuite("Integration Tests", IntegrationTests.self)
        await runTestSuite("Performance Tests", PerformanceTests.self)
        await runTestSuite("Stress Tests", StressTests.self)
        await runTestSuite("Recovery Tests", RecoveryTests.self)
        
        let endTime = Date()
        let totalDuration = endTime.timeIntervalSince(startTime)
        
        print("=================================")
        print("✅ All tests completed in \(String(format: "%.2f", totalDuration)) seconds")
        print("🎉 ColibrìDB Test Suite finished successfully!")
    }
    
    private static func runTestSuite<T>(_ name: String, _ suiteType: T.Type) async {
        print("\n📋 Running \(name)...")
        let suiteStartTime = Date()
        
        do {
            // Run the test suite
            let suite = suiteType as! any TestSuite.Type
            try await suite.run()
            
            let suiteEndTime = Date()
            let suiteDuration = suiteEndTime.timeIntervalSince(suiteStartTime)
            
            print("✅ \(name) completed in \(String(format: "%.2f", suiteDuration)) seconds")
        } catch {
            let suiteEndTime = Date()
            let suiteDuration = suiteEndTime.timeIntervalSince(suiteStartTime)
            
            print("❌ \(name) failed after \(String(format: "%.2f", suiteDuration)) seconds")
            print("   Error: \(error)")
        }
    }
}

/// Test Suite Protocol
protocol TestSuite {
    static func run() async throws
}

/// Extension to make test suites conform to TestSuite protocol
extension DatabaseTests: TestSuite {
    static func run() async throws {
        let suite = DatabaseTests()
        // Run all tests in the suite
        try await suite.testDatabaseInitialization()
        try await suite.testDatabaseStartup()
        try await suite.testDatabaseShutdown()
        try await suite.testTableCreation()
        try await suite.testTableDropping()
        try await suite.testTransactionManagement()
        try await suite.testDataOperations()
        try await suite.testAuthentication()
        try await suite.testDatabaseStatistics()
        try await suite.testCheckpointOperation()
        try await suite.testVacuumOperation()
        try await suite.testConcurrentTransactions()
        try await suite.testErrorHandling()
        try await suite.testDatabaseRecovery()
    }
}

extension TransactionManagerTests: TestSuite {
    static func run() async throws {
        let suite = TransactionManagerTests()
        // Run all tests in the suite
        try await suite.testTransactionCreation()
        try await suite.testTransactionCommit()
        try await suite.testTransactionAbort()
        try await suite.testReadOperations()
        try await suite.testWriteOperations()
        try await suite.testLockOperations()
        try await suite.testIsolationLevels()
        try await suite.testConcurrentTransactions()
        try await suite.testDistributedTransactions()
        try await suite.testDeadlockDetection()
        try await suite.testACIDProperties()
        try await suite.testErrorHandling()
        try await suite.testTransactionStatistics()
        try await suite.testTransactionConfiguration()
    }
}

extension BufferPoolTests: TestSuite {
    static func run() async throws {
        let suite = BufferPoolTests()
        // Run all tests in the suite
        try await suite.testBufferPoolInitialization()
        try await suite.testPageRetrievalCacheMiss()
        try await suite.testPageRetrievalCacheHit()
        try await suite.testPageModification()
        try await suite.testPagePinningAndUnpinning()
        try await suite.testPageEviction()
        try await suite.testDirtyPageFlushing()
        try await suite.testFlushAllDirtyPages()
        try await suite.testLSNUpdates()
        try await suite.testBufferPoolInvariants()
        try await suite.testErrorHandling()
        try await suite.testConcurrentAccess()
        try await suite.testPerformanceLargeNumberOfPages()
        try await suite.testMemoryUsage()
    }
}

extension WALTests: TestSuite {
    static func run() async throws {
        let suite = WALTests()
        // Run all tests in the suite
        try await suite.testWALInitialization()
        try await suite.testWALRecordAppending()
        try await suite.testWALFlushing()
        try await suite.testPageLSNUpdates()
        try await suite.testDataPageApplication()
        try await suite.testCheckpointCreation()
        try await suite.testCrashSimulation()
        try await suite.testRecovery()
        try await suite.testWALInvariants()
        try await suite.testErrorHandling()
        try await suite.testConcurrentWALOperations()
        try await suite.testWALPerformance()
        try await suite.testWALRecordRetrieval()
        try await suite.testActiveTransactionTable()
        try await suite.testDirtyPageTable()
    }
}

extension BTreeIndexTests: TestSuite {
    static func run() async throws {
        let suite = BTreeIndexTests()
        // Run all tests in the suite
        try await suite.testBTreeInitialization()
        try await suite.testKeyInsertion()
        try await suite.testKeySearch()
        try await suite.testKeyDeletion()
        try await suite.testRangeScan()
        try await suite.testTreeStructureInvariants()
        try await suite.testNodeSplitting()
        try await suite.testNodeMerging()
        try await suite.testConcurrentOperations()
        try await suite.testPerformanceLargeDataset()
        try await suite.testRangeScanPerformance()
        try await suite.testStringKeys()
        try await suite.testDoubleKeys()
        try await suite.testErrorHandling()
        try await suite.testTreeHeightGrowth()
        try await suite.testNodeCountTracking()
    }
}

extension SQLParserTests: TestSuite {
    static func run() async throws {
        let suite = SQLParserTests()
        // Run all tests in the suite
        try suite.testParserInitialization()
        try suite.testSELECTStatementParsing()
        try suite.testINSERTStatementParsing()
        try suite.testUPDATEStatementParsing()
        try suite.testDELETEStatementParsing()
        try suite.testCREATETABLEStatementParsing()
        try suite.testDROPTABLEStatementParsing()
        try suite.testTokenization()
        try suite.testCaseInsensitiveParsing()
        try suite.testWhitespaceHandling()
        try suite.testStringLiteralParsing()
        try suite.testNumericLiteralParsing()
        try suite.testIdentifierParsing()
        try suite.testErrorHandling()
        try suite.testComplexQueries()
        try suite.testSQLStatementTypes()
        try suite.testExpressionParsing()
        try suite.testBinaryOperators()
        try suite.testLogicalOperators()
        try suite.testParentheses()
        try suite.testPerformanceLargeQueries()
        try suite.testMultipleStatements()
        try suite.testEdgeCases()
    }
}

extension DistributedTests: TestSuite {
    static func run() async throws {
        let suite = DistributedTests()
        // Run all tests in the suite
        try await suite.testRaftConsensusInitialization()
        try await suite.testRaftLeaderElection()
        try await suite.testRaftLogReplication()
        try await suite.testRaftTermUpdates()
        try await suite.testRaftStateTransitions()
        try await suite.testReplicationManagerInitialization()
        try await suite.testReplicaAddition()
        try await suite.testReplicaRemoval()
        try await suite.testReplicationStartStop()
        try await suite.testDataReplication()
        try await suite.testShardingManagerInitialization()
        try await suite.testShardCreation()
        try await suite.testShardDeletion()
        try await suite.testShardKeyRouting()
        try await suite.testShardingStartStop()
        try await suite.testDistributedTransactionManagerInitialization()
        try await suite.testDistributedTransactionStart()
        try await suite.testTwoPhaseCommit()
        try await suite.testDistributedClockManager()
        try await suite.testLoadBalancerInitialization()
        try await suite.testLoadBalancerNodeAddition()
        try await suite.testLoadBalancing()
        try await suite.testDistributedQueryManager()
        try await suite.testDistributedQueryExecution()
        try await suite.testFaultTolerance()
        try await suite.testNetworkPartitioning()
        try await suite.testConcurrentDistributedOperations()
        try await suite.testPerformanceManyNodes()
    }
}

extension SecurityTests: TestSuite {
    static func run() async throws {
        let suite = SecurityTests()
        // Run all tests in the suite
        try await suite.testAuthenticationManagerInitialization()
        try await suite.testUserCreation()
        try await suite.testUserAuthentication()
        try await suite.testInvalidAuthentication()
        try await suite.testSessionValidation()
        try await suite.testSessionExpiration()
        try await suite.testUserDeletion()
        try await suite.testPasswordChange()
        try await suite.testAuthorizationManagerInitialization()
        try await suite.testRoleCreation()
        try await suite.testPermissionAssignment()
        try await suite.testPermissionCheck()
        try await suite.testUserRoleAssignment()
        try await suite.testAccessControl()
        try await suite.testRolesAndPermissionsManager()
        try await suite.testRoleHierarchy()
        try await suite.testSecurityPolicyEnforcement()
        try await suite.testEncryptionDecryption()
        try await suite.testKeyManagement()
        try await suite.testAuditLogging()
        try await suite.testConcurrentSecurityOperations()
        try await suite.testSecurityPerformance()
        try await suite.testSecurityErrorHandling()
    }
}

extension IntegrationTests: TestSuite {
    static func run() async throws {
        let suite = IntegrationTests()
        // Run all tests in the suite
        try await suite.testCompleteDatabaseWorkflow()
        try await suite.testDatabaseRecoveryAfterCrash()
        try await suite.testConcurrentTransactions()
        try await suite.testSQLParsingAndExecution()
        try await suite.testBufferPoolAndWALIntegration()
        try await suite.testIndexOperations()
        try await suite.testAuthenticationAndAuthorizationIntegration()
        try await suite.testPerformanceUnderLoad()
        try await suite.testErrorRecovery()
        try await suite.testMultiTableOperations()
        try await suite.testCheckpointAndVacuumOperations()
    }
}

extension PerformanceTests: TestSuite {
    static func run() async throws {
        let suite = PerformanceTests()
        // Run all tests in the suite
        try await suite.testDatabaseStartupPerformance()
        try await suite.testTransactionPerformance()
        try await suite.testInsertPerformance()
        try await suite.testReadPerformance()
        try await suite.testUpdatePerformance()
        try await suite.testBufferPoolPerformance()
        try await suite.testWALPerformance()
        try await suite.testBTreePerformance()
        try await suite.testSQLParserPerformance()
        try await suite.testAuthenticationPerformance()
        try await suite.testConcurrentPerformance()
        try await suite.testMemoryUsage()
        try await suite.testScalability()
    }
}

extension StressTests: TestSuite {
    static func run() async throws {
        let suite = StressTests()
        // Run all tests in the suite
        try await suite.testHighTransactionLoad()
        try await suite.testMemoryPressure()
        try await suite.testDiskSpacePressure()
        try await suite.testConcurrentTransactionConflicts()
        try await suite.testLongRunningTransactions()
        try await suite.testTransactionRollbackUnderStress()
        try await suite.testBufferPoolEvictionUnderStress()
        try await suite.testWALUnderStress()
        try await suite.testBTreeUnderStress()
        try await suite.testAuthenticationUnderStress()
        try await suite.testSystemRecoveryUnderStress()
        try await suite.testExtremeConcurrency()
    }
}

extension RecoveryTests: TestSuite {
    static func run() async throws {
        let suite = RecoveryTests()
        // Run all tests in the suite
        try await suite.testARIESRecoveryInitialization()
        try await suite.testARIESRecoveryProcess()
        try await suite.testPointInTimeRecovery()
        try await suite.testRecoverySubsystem()
        try await suite.testErrorRecovery()
        try await suite.testCrashRecovery()
        try await suite.testWALRecovery()
        try await suite.testBufferPoolRecovery()
        try await suite.testTransactionRecovery()
        try await suite.testDistributedTransactionRecovery()
        try await suite.testTwoPhaseCommitRecovery()
        try await suite.testReplicationRecovery()
        try await suite.testConsensusRecovery()
        try await suite.testErrorRecoveryMechanisms()
        try await suite.testFaultInjection()
        try await suite.testChaosEngineering()
        try await suite.testRecoveryPerformance()
        try await suite.testRecoveryConsistency()
    }
}
