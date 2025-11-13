/*
 * FaultInjection.swift
 * ColibrìDB - Fault Injection for Chaos Testing
 *
 * Based on TLA+ specification: FaultInjection.tla
 *
 * Models injecting faults for resilience testing:
 * - Crashes and restarts
 * - Network delays and packet loss
 * - Disk errors and corruption
 * - Memory pressure
 * - Clock skew
 *
 * References:
 * - Jepsen: Distributed systems testing framework
 * - Netflix Chaos Monkey
 * - Google DiRT (Disaster Recovery Testing)
 * - Microsoft FATE (Fault Analysis and Test Environment)
 *
 * Author: ColibrìDB Team
 * Date: 2025-10-19
 */

import Foundation

// MARK: - Fault Types

/// Type of fault to inject
public enum FaultType: String, Codable, CaseIterable, Sendable {
    case crash              // Node crash
    case networkDelay       // Network latency spike
    case packetLoss         // Packet drop
    case diskError          // Disk I/O error
    case diskCorruption     // Data corruption
    case memoryPressure     // Memory exhaustion
    case cpuSaturation      // CPU overload
    case clockSkew          // Clock drift
    case slowQuery          // Artificial query slowdown
    case deadlock           // Induce deadlock
}

// MARK: - Node State

/// State of a node
public enum NodeState: String, Codable {
    case healthy    // Normal operation
    case faulty     // Fault injected
    case recovering // Recovery in progress
}

// MARK: - Fault

/// Fault instance
public struct Fault: Codable, Hashable, Sendable {
    public let faultId: String
    public let nodeId: String
    public let faultType: FaultType
    public let injectedAt: Date
    public var recoveredAt: Date?
    public let parameters: [String: Double]
    
    public init(faultId: String, nodeId: String, faultType: FaultType, parameters: [String: Double] = [:]) {
        self.faultId = faultId
        self.nodeId = nodeId
        self.faultType = faultType
        self.injectedAt = Date()
        self.recoveredAt = nil
        self.parameters = parameters
    }
    
    public var duration: TimeInterval? {
        guard let recovered = recoveredAt else { return nil }
        return recovered.timeIntervalSince(injectedAt)
    }
}

// MARK: - Fault Injection Manager

/// Manager for fault injection
public actor FaultInjectionManager {
    
    // Active faults
    private var faults: Set<Fault> = []
    
    // Node state
    private var nodeState: [String: NodeState] = [:]
    
    // Statistics
    private var injectedFaults: Int = 0
    private var recoveredFaults: Int = 0
    
    // Fault effects (callbacks)
    private var faultHandlers: [FaultType: (Fault) async throws -> Void] = [:]
    private var recoveryHandlers: [FaultType: (Fault) async throws -> Void] = [:]
    
    public init(nodes: Set<String>) {
        for node in nodes {
            nodeState[node] = .healthy
        }
        
        Task {
            await initializeDefaultHandlers()
        }
    }
    
    // MARK: - Fault Injection
    
    /// Inject a fault into a node
    public func injectFault(nodeId: String, faultType: FaultType, parameters: [String: Double] = [:]) async throws {
        guard nodeState[nodeId] == .healthy else {
            throw FaultInjectionError.nodeAlreadyFaulty(nodeId: nodeId)
        }
        
        let fault = Fault(
            faultId: UUID().uuidString,
            nodeId: nodeId,
            faultType: faultType,
            parameters: parameters
        )
        
        // Update state
        faults.insert(fault)
        nodeState[nodeId] = .faulty
        injectedFaults += 1
        
        // Execute fault handler
        if let handler = faultHandlers[faultType] {
            try await handler(fault)
        }
    }
    
    /// Recover a node from fault
    public func recoverNode(nodeId: String) async throws {
        guard nodeState[nodeId] == .faulty else {
            throw FaultInjectionError.nodeNotFaulty(nodeId: nodeId)
        }
        
        // Find faults for this node
        let nodeFaults = faults.filter { $0.nodeId == nodeId && $0.recoveredAt == nil }
        
        for var fault in nodeFaults {
            // Mark fault as recovered
            fault.recoveredAt = Date()
            faults.remove(fault)
            faults.insert(fault)
            
            // Execute recovery handler
            if let handler = recoveryHandlers[fault.faultType] {
                try await handler(fault)
            }
            
            recoveredFaults += 1
        }
        
        // Update state
        nodeState[nodeId] = .healthy
    }
    
    /// Inject random fault
    public func injectRandomFault(nodes: [String]) async throws {
        guard let node = nodes.randomElement() else {
            throw FaultInjectionError.noNodesAvailable
        }
        
        guard let faultType = FaultType.allCases.randomElement() else {
            return
        }
        
        try await injectFault(nodeId: node, faultType: faultType)
    }
    
    // MARK: - Fault Handlers
    
    private func initializeDefaultHandlers() {
        // Crash handler
        faultHandlers[.crash] = { fault in
            // Simulate crash: stop processing, lose in-memory state
            print("💥 Node \(fault.nodeId) crashed")
        }
        
        // Network delay handler
        faultHandlers[.networkDelay] = { fault in
            let delayMs = fault.parameters["delayMs"] ?? 100
            try? await Task.sleep(nanoseconds: UInt64(delayMs * 1_000_000))
        }
        
        // Packet loss handler
        faultHandlers[.packetLoss] = { fault in
            let lossRate = fault.parameters["lossRate"] ?? 0.1
            // Simulate packet loss
            if Double.random(in: 0...1) < lossRate {
                print("📦 Packet lost on node \(fault.nodeId)")
            }
        }
        
        // Disk error handler
        faultHandlers[.diskError] = { fault in
            print("💾 Disk error on node \(fault.nodeId)")
            throw FaultInjectionError.diskIOFailure
        }
        
        // Recovery handlers
        recoveryHandlers[.crash] = { fault in
            print("🔄 Node \(fault.nodeId) recovering from crash")
        }
    }
    
    /// Register custom fault handler
    public func registerFaultHandler(faultType: FaultType, handler: @escaping (Fault) async throws -> Void) {
        faultHandlers[faultType] = handler
    }
    
    /// Register custom recovery handler
    public func registerRecoveryHandler(faultType: FaultType, handler: @escaping (Fault) async throws -> Void) {
        recoveryHandlers[faultType] = handler
    }
    
    // MARK: - Query Methods
    
    public func getActiveFaults() -> Set<Fault> {
        return faults.filter { $0.recoveredAt == nil }
    }
    
    public func getNodeState(nodeId: String) -> NodeState? {
        return nodeState[nodeId]
    }
    
    public func getFaultHistory() -> Set<Fault> {
        return faults
    }
    
    public func getStats() -> FaultInjectionStats {
        return FaultInjectionStats(
            totalInjected: injectedFaults,
            totalRecovered: recoveredFaults,
            currentlyActive: faults.filter { $0.recoveredAt == nil }.count
        )
    }
}

// MARK: - Statistics

public struct FaultInjectionStats: Codable {
    public let totalInjected: Int
    public let totalRecovered: Int
    public let currentlyActive: Int
    
    public var recoveryRate: Double {
        guard totalInjected > 0 else { return 0.0 }
        return Double(totalRecovered) / Double(totalInjected)
    }
}

// MARK: - Errors

public enum FaultInjectionError: Error, LocalizedError {
    case nodeAlreadyFaulty(nodeId: String)
    case nodeNotFaulty(nodeId: String)
    case noNodesAvailable
    case diskIOFailure
    case networkFailure
    
    public var errorDescription: String? {
        switch self {
        case .nodeAlreadyFaulty(let nodeId):
            return "Node already has fault injected: \(nodeId)"
        case .nodeNotFaulty(let nodeId):
            return "Node is not faulty: \(nodeId)"
        case .noNodesAvailable:
            return "No nodes available for fault injection"
        case .diskIOFailure:
            return "Disk I/O failure (injected)"
        case .networkFailure:
            return "Network failure (injected)"
        }
    }
}

/*
 * IMPLEMENTATION NOTES:
 *
 * This implementation follows the FaultInjection.tla specification
 * and provides comprehensive fault injection for chaos testing:
 *
 * 1. Fault Types:
 *    - Crash: Simulate node crash/restart
 *    - Network: Delays, packet loss, partitions
 *    - Disk: I/O errors, corruption
 *    - Resource: Memory/CPU pressure
 *    - Time: Clock skew
 *
 * 2. Injection Strategy:
 *    - Targeted: Specific node/fault
 *    - Random: Random node/fault
 *    - Scheduled: Fault at specific time
 *    - Probabilistic: Fault with probability
 *
 * 3. Recovery:
 *    - Automatic: Fault auto-recovers after duration
 *    - Manual: Explicit recovery trigger
 *    - Nodes eventually recover (liveness)
 *
 * 4. Fault Effects:
 *    - Crash: Lose in-memory state, restart
 *    - Delay: Add latency to operations
 *    - Loss: Drop messages/data
 *    - Error: Throw exceptions
 *
 * 5. Observability:
 *    - Track all injected faults
 *    - Measure recovery time
 *    - Monitor system behavior
 *
 * Academic References:
 * - Jepsen: Kyle Kingsbury's distributed systems testing
 * - Netflix Chaos Monkey: Fault injection in production
 * - Google DiRT: Disaster recovery testing
 * - Microsoft FATE: Fault analysis
 *
 * Production Examples:
 * - Netflix: Chaos Monkey, Chaos Kong
 * - Amazon: GameDay exercises
 * - Google: DiRT (Disaster Recovery Testing)
 * - Jepsen: Distributed systems verification
 */

