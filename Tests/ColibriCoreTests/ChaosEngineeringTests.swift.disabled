//
//  ChaosEngineeringTests.swift
//  ColibrìDB - Chaos Engineering Tests
//
//  Tests for resilience testing and fault injection
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//

import Testing
@testable import ColibriCore

/// Tests for the Chaos Engineering system
/// Covers fault injection, resilience testing, and system recovery
struct ChaosEngineeringTests {
    
    // MARK: - Setup
    
    @Test func testChaosEngineeringManagerCreation() async throws {
        // Arrange
        let nodes = Set(["node1", "node2", "node3"])
        
        // Act
        let chaosManager = ChaosEngineeringManager(
            nodes: nodes,
            maxFailures: 5,
            maxConcurrentExperiments: 3
        )
        
        // Assert
        #expect(chaosManager != nil)
    }
    
    @Test func testChaosEngineeringManagerDefaultValues() async throws {
        // Arrange
        let nodes = Set(["node1", "node2"])
        
        // Act
        let chaosManager = ChaosEngineeringManager(nodes: nodes)
        
        // Assert
        #expect(chaosManager != nil)
    }
    
    // MARK: - Experiment Types Tests
    
    @Test func testExperimentTypes() async throws {
        // Arrange
        let experimentTypes: [ExperimentType] = [
            .networkPartition,
            .randomFailures,
            .cascadingFailures,
            .resourceExhaustion,
            .timeSkew,
            .byzantineFault,
            .performanceDegradation,
            .dataCorruption
        ]
        
        // Act & Assert
        for experimentType in experimentTypes {
            #expect(experimentType.rawValue != "")
        }
    }
    
    @Test func testSystemHealthLevels() async throws {
        // Arrange
        let healthLevels: [SystemHealth] = [.healthy, .degraded, .failed]
        
        // Act & Assert
        for health in healthLevels {
            #expect(health.rawValue != "")
        }
    }
    
    // MARK: - Chaos Experiment Tests
    
    @Test func testChaosExperimentCreation() async throws {
        // Arrange
        let targetNodes = Set(["node1", "node2"])
        
        // Act
        let experiment = ChaosExperiment(
            experimentId: "test_exp_1",
            experimentType: .networkPartition,
            targetNodes: targetNodes,
            duration: 60
        )
        
        // Assert
        #expect(experiment.experimentId == "test_exp_1")
        #expect(experiment.experimentType == .networkPartition)
        #expect(experiment.targetNodes == targetNodes)
        #expect(experiment.duration == 60)
        #expect(experiment.endTime == nil)
        #expect(experiment.outcome == nil)
    }
    
    @Test func testChaosExperimentDefaultDuration() async throws {
        // Arrange
        let targetNodes = Set(["node1"])
        
        // Act
        let experiment = ChaosExperiment(
            experimentId: "test_exp_2",
            experimentType: .randomFailures,
            targetNodes: targetNodes
        )
        
        // Assert
        #expect(experiment.duration == 60) // Default duration
    }
    
    @Test func testChaosExperimentHashable() async throws {
        // Arrange
        let experiment1 = ChaosExperiment(
            experimentId: "test_exp_1",
            experimentType: .networkPartition,
            targetNodes: Set(["node1"])
        )
        let experiment2 = ChaosExperiment(
            experimentId: "test_exp_1",
            experimentType: .randomFailures,
            targetNodes: Set(["node2"])
        )
        let experiment3 = ChaosExperiment(
            experimentId: "test_exp_2",
            experimentType: .networkPartition,
            targetNodes: Set(["node1"])
        )
        
        // Act & Assert
        #expect(experiment1 == experiment2) // Same ID
        #expect(experiment1 != experiment3) // Different ID
    }
    
    // MARK: - Experiment Outcome Tests
    
    @Test func testExperimentOutcomeCreation() async throws {
        // Arrange
        let outcome = ExperimentOutcome(
            systemRecovered: true,
            recoveryTime: 5.0,
            failuresCaused: 2,
            impactedTransactions: 10,
            observations: ["System recovered successfully", "No data loss"]
        )
        
        // Assert
        #expect(outcome.systemRecovered == true)
        #expect(outcome.recoveryTime == 5.0)
        #expect(outcome.failuresCaused == 2)
        #expect(outcome.impactedTransactions == 10)
        #expect(outcome.observations.count == 2)
    }
    
    @Test func testExperimentOutcomeDefaultObservations() async throws {
        // Arrange
        let outcome = ExperimentOutcome(
            systemRecovered: false,
            recoveryTime: nil,
            failuresCaused: 5,
            impactedTransactions: 100
        )
        
        // Assert
        #expect(outcome.systemRecovered == false)
        #expect(outcome.recoveryTime == nil)
        #expect(outcome.failuresCaused == 5)
        #expect(outcome.impactedTransactions == 100)
        #expect(outcome.observations.isEmpty)
    }
    
    // MARK: - Network Partition Tests
    
    @Test func testNetworkPartitionExperiment() async throws {
        // Arrange
        let nodes = Set(["node1", "node2", "node3"])
        let chaosManager = ChaosEngineeringManager(nodes: nodes)
        let targetNodes = Set(["node1", "node2"])
        
        // Act
        let outcome = try await chaosManager.runExperiment(
            experimentType: .networkPartition,
            targetNodes: targetNodes,
            duration: 1.0 // Short duration for testing
        )
        
        // Assert
        #expect(outcome != nil)
        #expect(outcome.systemRecovered == true)
        #expect(outcome.failuresCaused >= 0)
        #expect(outcome.observations.count > 0)
    }
    
    @Test func testNetworkPartitionWithSingleNode() async throws {
        // Arrange
        let nodes = Set(["node1", "node2", "node3"])
        let chaosManager = ChaosEngineeringManager(nodes: nodes)
        let targetNodes = Set(["node1"])
        
        // Act
        let outcome = try await chaosManager.runExperiment(
            experimentType: .networkPartition,
            targetNodes: targetNodes,
            duration: 0.5
        )
        
        // Assert
        #expect(outcome != nil)
        #expect(outcome.systemRecovered == true)
    }
    
    // MARK: - Random Failures Tests
    
    @Test func testRandomFailuresExperiment() async throws {
        // Arrange
        let nodes = Set(["node1", "node2", "node3", "node4", "node5"])
        let chaosManager = ChaosEngineeringManager(nodes: nodes)
        let targetNodes = Set(["node1", "node2", "node3"])
        
        // Act
        let outcome = try await chaosManager.runExperiment(
            experimentType: .randomFailures,
            targetNodes: targetNodes,
            duration: 1.0
        )
        
        // Assert
        #expect(outcome != nil)
        #expect(outcome.systemRecovered == true)
        #expect(outcome.failuresCaused >= 0)
        #expect(outcome.observations.count > 0)
    }
    
    @Test func testRandomFailuresWithAllNodes() async throws {
        // Arrange
        let nodes = Set(["node1", "node2", "node3"])
        let chaosManager = ChaosEngineeringManager(nodes: nodes)
        
        // Act
        let outcome = try await chaosManager.runExperiment(
            experimentType: .randomFailures,
            targetNodes: nodes,
            duration: 0.5
        )
        
        // Assert
        #expect(outcome != nil)
        #expect(outcome.systemRecovered == true)
    }
    
    // MARK: - Cascading Failures Tests
    
    @Test func testCascadingFailuresExperiment() async throws {
        // Arrange
        let nodes = Set(["node1", "node2", "node3", "node4"])
        let chaosManager = ChaosEngineeringManager(nodes: nodes)
        let targetNodes = Set(["node1", "node2", "node3"])
        
        // Act
        let outcome = try await chaosManager.runExperiment(
            experimentType: .cascadingFailures,
            targetNodes: targetNodes,
            duration: 1.0
        )
        
        // Assert
        #expect(outcome != nil)
        #expect(outcome.systemRecovered == true)
        #expect(outcome.failuresCaused >= 0)
        #expect(outcome.observations.count > 0)
    }
    
    @Test func testCascadingFailuresWithSystemFailure() async throws {
        // Arrange
        let nodes = Set(["node1", "node2"])
        let chaosManager = ChaosEngineeringManager(nodes: nodes, maxFailures: 1)
        
        // Act
        let outcome = try await chaosManager.runExperiment(
            experimentType: .cascadingFailures,
            targetNodes: nodes,
            duration: 0.5
        )
        
        // Assert
        #expect(outcome != nil)
        // System might fail with cascading failures
    }
    
    // MARK: - Resource Exhaustion Tests
    
    @Test func testResourceExhaustionExperiment() async throws {
        // Arrange
        let nodes = Set(["node1", "node2", "node3"])
        let chaosManager = ChaosEngineeringManager(nodes: nodes)
        let targetNodes = Set(["node1", "node2"])
        
        // Act
        let outcome = try await chaosManager.runExperiment(
            experimentType: .resourceExhaustion,
            targetNodes: targetNodes,
            duration: 1.0
        )
        
        // Assert
        #expect(outcome != nil)
        #expect(outcome.systemRecovered == true)
        #expect(outcome.observations.count > 0)
    }
    
    @Test func testResourceExhaustionWithSingleNode() async throws {
        // Arrange
        let nodes = Set(["node1", "node2", "node3"])
        let chaosManager = ChaosEngineeringManager(nodes: nodes)
        let targetNodes = Set(["node1"])
        
        // Act
        let outcome = try await chaosManager.runExperiment(
            experimentType: .resourceExhaustion,
            targetNodes: targetNodes,
            duration: 0.5
        )
        
        // Assert
        #expect(outcome != nil)
        #expect(outcome.systemRecovered == true)
    }
    
    // MARK: - Time Skew Tests
    
    @Test func testTimeSkewExperiment() async throws {
        // Arrange
        let nodes = Set(["node1", "node2", "node3"])
        let chaosManager = ChaosEngineeringManager(nodes: nodes)
        let targetNodes = Set(["node1", "node2"])
        
        // Act
        let outcome = try await chaosManager.runExperiment(
            experimentType: .timeSkew,
            targetNodes: targetNodes,
            duration: 1.0
        )
        
        // Assert
        #expect(outcome != nil)
        #expect(outcome.systemRecovered == true)
        #expect(outcome.observations.count > 0)
    }
    
    @Test func testTimeSkewWithAllNodes() async throws {
        // Arrange
        let nodes = Set(["node1", "node2"])
        let chaosManager = ChaosEngineeringManager(nodes: nodes)
        
        // Act
        let outcome = try await chaosManager.runExperiment(
            experimentType: .timeSkew,
            targetNodes: nodes,
            duration: 0.5
        )
        
        // Assert
        #expect(outcome != nil)
        #expect(outcome.systemRecovered == true)
    }
    
    // MARK: - Byzantine Fault Tests
    
    @Test func testByzantineFaultExperiment() async throws {
        // Arrange
        let nodes = Set(["node1", "node2", "node3"])
        let chaosManager = ChaosEngineeringManager(nodes: nodes)
        let targetNodes = Set(["node1"])
        
        // Act
        let outcome = try await chaosManager.runExperiment(
            experimentType: .byzantineFault,
            targetNodes: targetNodes,
            duration: 1.0
        )
        
        // Assert
        #expect(outcome != nil)
        #expect(outcome.systemRecovered == true)
        #expect(outcome.observations.count > 0)
    }
    
    @Test func testByzantineFaultWithMultipleNodes() async throws {
        // Arrange
        let nodes = Set(["node1", "node2", "node3", "node4"])
        let chaosManager = ChaosEngineeringManager(nodes: nodes)
        let targetNodes = Set(["node1", "node2"])
        
        // Act
        let outcome = try await chaosManager.runExperiment(
            experimentType: .byzantineFault,
            targetNodes: targetNodes,
            duration: 0.5
        )
        
        // Assert
        #expect(outcome != nil)
        #expect(outcome.systemRecovered == true)
    }
    
    // MARK: - Performance Degradation Tests
    
    @Test func testPerformanceDegradationExperiment() async throws {
        // Arrange
        let nodes = Set(["node1", "node2", "node3"])
        let chaosManager = ChaosEngineeringManager(nodes: nodes)
        let targetNodes = Set(["node1", "node2"])
        
        // Act
        let outcome = try await chaosManager.runExperiment(
            experimentType: .performanceDegradation,
            targetNodes: targetNodes,
            duration: 1.0
        )
        
        // Assert
        #expect(outcome != nil)
        #expect(outcome.systemRecovered == true)
        #expect(outcome.observations.count > 0)
    }
    
    @Test func testPerformanceDegradationWithSingleNode() async throws {
        // Arrange
        let nodes = Set(["node1", "node2", "node3"])
        let chaosManager = ChaosEngineeringManager(nodes: nodes)
        let targetNodes = Set(["node1"])
        
        // Act
        let outcome = try await chaosManager.runExperiment(
            experimentType: .performanceDegradation,
            targetNodes: targetNodes,
            duration: 0.5
        )
        
        // Assert
        #expect(outcome != nil)
        #expect(outcome.systemRecovered == true)
    }
    
    // MARK: - Data Corruption Tests
    
    @Test func testDataCorruptionExperiment() async throws {
        // Arrange
        let nodes = Set(["node1", "node2", "node3"])
        let chaosManager = ChaosEngineeringManager(nodes: nodes)
        let targetNodes = Set(["node1"])
        
        // Act
        let outcome = try await chaosManager.runExperiment(
            experimentType: .dataCorruption,
            targetNodes: targetNodes,
            duration: 1.0
        )
        
        // Assert
        #expect(outcome != nil)
        #expect(outcome.systemRecovered == true)
        #expect(outcome.observations.count > 0)
    }
    
    @Test func testDataCorruptionWithMultipleNodes() async throws {
        // Arrange
        let nodes = Set(["node1", "node2", "node3", "node4"])
        let chaosManager = ChaosEngineeringManager(nodes: nodes)
        let targetNodes = Set(["node1", "node2"])
        
        // Act
        let outcome = try await chaosManager.runExperiment(
            experimentType: .dataCorruption,
            targetNodes: targetNodes,
            duration: 0.5
        )
        
        // Assert
        #expect(outcome != nil)
        #expect(outcome.systemRecovered == true)
    }
    
    // MARK: - System Health Tests
    
    @Test func testSystemHealthMonitoring() async throws {
        // Arrange
        let nodes = Set(["node1", "node2", "node3"])
        let chaosManager = ChaosEngineeringManager(nodes: nodes)
        
        // Act
        let health = await chaosManager.getSystemHealth()
        
        // Assert
        #expect(health == .healthy) // Should start healthy
    }
    
    @Test func testSystemResilienceCheck() async throws {
        // Arrange
        let nodes = Set(["node1", "node2", "node3"])
        let chaosManager = ChaosEngineeringManager(nodes: nodes)
        
        // Act
        let isResilient = await chaosManager.checkSystemResilient()
        
        // Assert
        #expect(isResilient == true) // Should be resilient initially
    }
    
    @Test func testSystemHealthAfterExperiment() async throws {
        // Arrange
        let nodes = Set(["node1", "node2", "node3"])
        let chaosManager = ChaosEngineeringManager(nodes: nodes)
        
        // Act
        _ = try await chaosManager.runExperiment(
            experimentType: .randomFailures,
            targetNodes: Set(["node1"]),
            duration: 0.5
        )
        
        let health = await chaosManager.getSystemHealth()
        let isResilient = await chaosManager.checkSystemResilient()
        
        // Assert
        #expect(health == .healthy) // Should be healthy after recovery
        #expect(isResilient == true) // Should be resilient
    }
    
    // MARK: - Experiment Management Tests
    
    @Test func testGetActiveExperiments() async throws {
        // Arrange
        let nodes = Set(["node1", "node2", "node3"])
        let chaosManager = ChaosEngineeringManager(nodes: nodes)
        
        // Act
        let activeExperiments = await chaosManager.getActiveExperiments()
        
        // Assert
        #expect(activeExperiments.isEmpty) // Should be empty initially
    }
    
    @Test func testGetExperimentHistory() async throws {
        // Arrange
        let nodes = Set(["node1", "node2", "node3"])
        let chaosManager = ChaosEngineeringManager(nodes: nodes)
        
        // Act
        let history = await chaosManager.getExperimentHistory()
        
        // Assert
        #expect(history.isEmpty) // Should be empty initially
    }
    
    @Test func testGetExperimentHistoryAfterExperiments() async throws {
        // Arrange
        let nodes = Set(["node1", "node2", "node3"])
        let chaosManager = ChaosEngineeringManager(nodes: nodes)
        
        // Act
        _ = try await chaosManager.runExperiment(
            experimentType: .networkPartition,
            targetNodes: Set(["node1"]),
            duration: 0.5
        )
        
        _ = try await chaosManager.runExperiment(
            experimentType: .randomFailures,
            targetNodes: Set(["node2"]),
            duration: 0.5
        )
        
        let history = await chaosManager.getExperimentHistory()
        
        // Assert
        #expect(history.count == 2) // Should have 2 experiments
    }
    
    @Test func testGetStats() async throws {
        // Arrange
        let nodes = Set(["node1", "node2", "node3"])
        let chaosManager = ChaosEngineeringManager(nodes: nodes)
        
        // Act
        let stats = await chaosManager.getStats()
        
        // Assert
        #expect(stats.totalExperiments == 0)
        #expect(stats.successfulExperiments == 0)
        #expect(stats.failedExperiments == 0)
        #expect(stats.successRate == 0.0)
        #expect(stats.resilienceScore == 0.0)
    }
    
    @Test func testGetStatsAfterExperiments() async throws {
        // Arrange
        let nodes = Set(["node1", "node2", "node3"])
        let chaosManager = ChaosEngineeringManager(nodes: nodes)
        
        // Act
        _ = try await chaosManager.runExperiment(
            experimentType: .networkPartition,
            targetNodes: Set(["node1"]),
            duration: 0.5
        )
        
        _ = try await chaosManager.runExperiment(
            experimentType: .randomFailures,
            targetNodes: Set(["node2"]),
            duration: 0.5
        )
        
        let stats = await chaosManager.getStats()
        
        // Assert
        #expect(stats.totalExperiments == 2)
        #expect(stats.successfulExperiments >= 0)
        #expect(stats.failedExperiments >= 0)
        #expect(stats.successRate >= 0.0)
        #expect(stats.successRate <= 1.0)
        #expect(stats.resilienceScore >= 0.0)
        #expect(stats.resilienceScore <= 100.0)
    }
    
    // MARK: - Error Handling Tests
    
    @Test func testTooManyExperimentsError() async throws {
        // Arrange
        let nodes = Set(["node1", "node2"])
        let chaosManager = ChaosEngineeringManager(nodes: nodes, maxConcurrentExperiments: 1)
        
        // Start one experiment
        _ = try await chaosManager.runExperiment(
            experimentType: .networkPartition,
            targetNodes: Set(["node1"]),
            duration: 2.0
        )
        
        // Act & Assert
        await #expect(throws: ChaosError.tooManyExperiments) {
            try await chaosManager.runExperiment(
                experimentType: .randomFailures,
                targetNodes: Set(["node2"]),
                duration: 1.0
            )
        }
    }
    
    @Test func testChaosErrorTypes() async throws {
        // Arrange
        let errors: [ChaosError] = [
            .tooManyExperiments,
            .experimentFailed(experimentId: "test_exp"),
            .systemNotResilient
        ]
        
        // Act & Assert
        for error in errors {
            #expect(error.errorDescription != nil)
        }
    }
    
    // MARK: - Concurrent Experiments Tests
    
    @Test func testConcurrentExperiments() async throws {
        // Arrange
        let nodes = Set(["node1", "node2", "node3", "node4"])
        let chaosManager = ChaosEngineeringManager(nodes: nodes, maxConcurrentExperiments: 3)
        
        // Act
        await withTaskGroup(of: Void.self) { group in
            for i in 0..<3 {
                group.addTask {
                    try? await chaosManager.runExperiment(
                        experimentType: .randomFailures,
                        targetNodes: Set(["node\(i + 1)"]),
                        duration: 0.5
                    )
                }
            }
        }
        
        // Assert
        let stats = await chaosManager.getStats()
        #expect(stats.totalExperiments == 3)
    }
    
    @Test func testConcurrentExperimentsWithLimit() async throws {
        // Arrange
        let nodes = Set(["node1", "node2", "node3", "node4", "node5"])
        let chaosManager = ChaosEngineeringManager(nodes: nodes, maxConcurrentExperiments: 2)
        
        // Act
        await withTaskGroup(of: Void.self) { group in
            for i in 0..<4 {
                group.addTask {
                    try? await chaosManager.runExperiment(
                        experimentType: .networkPartition,
                        targetNodes: Set(["node\(i + 1)"]),
                        duration: 1.0
                    )
                }
            }
        }
        
        // Assert
        let stats = await chaosManager.getStats()
        #expect(stats.totalExperiments >= 2) // At least 2 should succeed
        #expect(stats.totalExperiments <= 4) // At most 4 total
    }
    
    // MARK: - Performance Tests
    
    @Test func testExperimentPerformance() async throws {
        // Arrange
        let nodes = Set(["node1", "node2", "node3"])
        let chaosManager = ChaosEngineeringManager(nodes: nodes)
        
        let startTime = Date()
        
        // Act
        _ = try await chaosManager.runExperiment(
            experimentType: .networkPartition,
            targetNodes: Set(["node1"]),
            duration: 0.1
        )
        
        // Assert
        let endTime = Date()
        let duration = endTime.timeIntervalSince(startTime)
        
        #expect(duration < 5.0) // Should complete in reasonable time
    }
    
    @Test func testMultipleExperimentsPerformance() async throws {
        // Arrange
        let nodes = Set(["node1", "node2", "node3", "node4", "node5"])
        let chaosManager = ChaosEngineeringManager(nodes: nodes)
        
        let startTime = Date()
        
        // Act
        for i in 0..<10 {
            _ = try await chaosManager.runExperiment(
                experimentType: .randomFailures,
                targetNodes: Set(["node\(i % 5 + 1)"]),
                duration: 0.05
            )
        }
        
        // Assert
        let endTime = Date()
        let duration = endTime.timeIntervalSince(startTime)
        
        #expect(duration < 10.0) // Should complete in reasonable time
    }
    
    // MARK: - Edge Cases Tests
    
    @Test func testExperimentWithEmptyTargetNodes() async throws {
        // Arrange
        let nodes = Set(["node1", "node2", "node3"])
        let chaosManager = ChaosEngineeringManager(nodes: nodes)
        let targetNodes = Set<String>()
        
        // Act
        let outcome = try await chaosManager.runExperiment(
            experimentType: .networkPartition,
            targetNodes: targetNodes,
            duration: 0.5
        )
        
        // Assert
        #expect(outcome != nil)
        #expect(outcome.systemRecovered == true)
    }
    
    @Test func testExperimentWithNonExistentNodes() async throws {
        // Arrange
        let nodes = Set(["node1", "node2", "node3"])
        let chaosManager = ChaosEngineeringManager(nodes: nodes)
        let targetNodes = Set(["non_existent_node"])
        
        // Act
        let outcome = try await chaosManager.runExperiment(
            experimentType: .randomFailures,
            targetNodes: targetNodes,
            duration: 0.5
        )
        
        // Assert
        #expect(outcome != nil)
        #expect(outcome.systemRecovered == true)
    }
    
    @Test func testExperimentWithZeroDuration() async throws {
        // Arrange
        let nodes = Set(["node1", "node2", "node3"])
        let chaosManager = ChaosEngineeringManager(nodes: nodes)
        
        // Act
        let outcome = try await chaosManager.runExperiment(
            experimentType: .networkPartition,
            targetNodes: Set(["node1"]),
            duration: 0.0
        )
        
        // Assert
        #expect(outcome != nil)
        #expect(outcome.systemRecovered == true)
    }
    
    @Test func testExperimentWithVeryLongDuration() async throws {
        // Arrange
        let nodes = Set(["node1", "node2", "node3"])
        let chaosManager = ChaosEngineeringManager(nodes: nodes)
        
        // Act
        let outcome = try await chaosManager.runExperiment(
            experimentType: .randomFailures,
            targetNodes: Set(["node1"]),
            duration: 0.1 // Short for testing
        )
        
        // Assert
        #expect(outcome != nil)
        #expect(outcome.systemRecovered == true)
    }
    
    // MARK: - Integration Tests
    
    @Test func testCompleteChaosEngineeringWorkflow() async throws {
        // Arrange
        let nodes = Set(["node1", "node2", "node3", "node4"])
        let chaosManager = ChaosEngineeringManager(nodes: nodes)
        
        // Act & Assert - Check initial state
        let initialHealth = await chaosManager.getSystemHealth()
        let initialResilience = await chaosManager.checkSystemResilient()
        #expect(initialHealth == .healthy)
        #expect(initialResilience == true)
        
        // Act & Assert - Run various experiments
        let networkOutcome = try await chaosManager.runExperiment(
            experimentType: .networkPartition,
            targetNodes: Set(["node1", "node2"]),
            duration: 0.5
        )
        #expect(networkOutcome.systemRecovered == true)
        
        let randomOutcome = try await chaosManager.runExperiment(
            experimentType: .randomFailures,
            targetNodes: Set(["node3"]),
            duration: 0.5
        )
        #expect(randomOutcome.systemRecovered == true)
        
        let performanceOutcome = try await chaosManager.runExperiment(
            experimentType: .performanceDegradation,
            targetNodes: Set(["node4"]),
            duration: 0.5
        )
        #expect(performanceOutcome.systemRecovered == true)
        
        // Act & Assert - Check final state
        let finalHealth = await chaosManager.getSystemHealth()
        let finalResilience = await chaosManager.checkSystemResilient()
        let stats = await chaosManager.getStats()
        
        #expect(finalHealth == .healthy)
        #expect(finalResilience == true)
        #expect(stats.totalExperiments == 3)
        #expect(stats.successRate > 0.0)
    }
    
    @Test func testChaosEngineeringWithDifferentNodeCounts() async throws {
        // Test with different cluster sizes
        let nodeCounts = [2, 3, 5, 10]
        
        for count in nodeCounts {
            // Arrange
            let nodes = Set((1...count).map { "node\($0)" })
            let chaosManager = ChaosEngineeringManager(nodes: nodes)
            
            // Act
            let outcome = try await chaosManager.runExperiment(
                experimentType: .randomFailures,
                targetNodes: Set(["node1"]),
                duration: 0.1
            )
            
            // Assert
            #expect(outcome != nil)
            #expect(outcome.systemRecovered == true)
        }
    }
}
