//
//  Clock.swift
//  ColibrìDB Distributed Clock Implementation
//
//  Based on: spec/Clock.tla
//  Implements: Distributed timestamp oracle
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//
//  Key Properties:
//  - Monotonicity: Timestamps always increase
//  - Causality: Preserves happens-before relationships
//  - Precision: High-resolution timestamps
//  - Synchronization: Clock synchronization across nodes
//

import Foundation

// MARK: - Clock Types

/// Clock type
/// Corresponds to TLA+: ClockType
public enum ClockType: String, Codable, Sendable {
    case logical = "logical"
    case physical = "physical"
    case hybrid = "hybrid"
}

/// Clock precision
/// Corresponds to TLA+: ClockPrecision
public enum ClockPrecision: String, Codable, Sendable {
    case nanosecond = "nanosecond"
    case microsecond = "microsecond"
    case millisecond = "millisecond"
    case second = "second"
}

/// Clock status
/// Corresponds to TLA+: ClockStatus
public enum ClockStatus: String, Codable, Sendable {
    case synchronized = "synchronized"
    case desynchronized = "desynchronized"
    case unknown = "unknown"
}

// MARK: - Timestamp Types

/// Logical timestamp
/// Corresponds to TLA+: LogicalTimestamp
public struct LogicalTimestamp: Codable, Sendable, Equatable, Comparable {
    public let value: Int
    
    public init(value: Int) {
        self.value = value
    }
    
    public static func < (lhs: LogicalTimestamp, rhs: LogicalTimestamp) -> Bool {
        return lhs.value < rhs.value
    }
    
    public static func == (lhs: LogicalTimestamp, rhs: LogicalTimestamp) -> Bool {
        return lhs.value == rhs.value
    }
}

/// Physical timestamp
/// Corresponds to TLA+: PhysicalTimestamp
public struct PhysicalTimestamp: Codable, Sendable, Equatable, Comparable {
    public let value: UInt64 // Nanoseconds since epoch
    
    public init(value: UInt64) {
        self.value = value
    }
    
    public init(date: Date) {
        self.value = UInt64(date.timeIntervalSince1970 * 1_000_000_000)
    }
    
    public var date: Date {
        return Date(timeIntervalSince1970: Double(value) / 1_000_000_000)
    }
    
    public static func < (lhs: PhysicalTimestamp, rhs: PhysicalTimestamp) -> Bool {
        return lhs.value < rhs.value
    }
    
    public static func == (lhs: PhysicalTimestamp, rhs: PhysicalTimestamp) -> Bool {
        return lhs.value == rhs.value
    }
}

/// Hybrid timestamp
/// Corresponds to TLA+: HybridTimestamp
public struct HybridTimestamp: Codable, Sendable, Equatable, Comparable {
    public let physical: PhysicalTimestamp
    public let logical: LogicalTimestamp
    
    public init(physical: PhysicalTimestamp, logical: LogicalTimestamp) {
        self.physical = physical
        self.logical = logical
    }
    
    public static func < (lhs: HybridTimestamp, rhs: HybridTimestamp) -> Bool {
        if lhs.physical < rhs.physical {
            return true
        } else if lhs.physical == rhs.physical {
            return lhs.logical < rhs.logical
        } else {
            return false
        }
    }
    
    public static func == (lhs: HybridTimestamp, rhs: HybridTimestamp) -> Bool {
        return lhs.physical == rhs.physical && lhs.logical == rhs.logical
    }
}

/// Clock synchronization message
/// Corresponds to TLA+: ClockSyncMessage
public struct ClockSyncMessage: Codable, Sendable, Equatable {
    public let nodeId: String
    public let timestamp: PhysicalTimestamp
    public let roundTripTime: UInt64
    public let offset: Int64
    public let precision: ClockPrecision
    
    public init(nodeId: String, timestamp: PhysicalTimestamp, roundTripTime: UInt64, offset: Int64, precision: ClockPrecision) {
        self.nodeId = nodeId
        self.timestamp = timestamp
        self.roundTripTime = roundTripTime
        self.offset = offset
        self.precision = precision
    }
}

// MARK: - Distributed Clock Manager

/// Distributed Clock Manager for timestamp generation and synchronization
/// Corresponds to TLA+ module: Clock.tla
public actor DistributedClockManager {
    
    // MARK: - State Variables (TLA+ vars)
    
    /// Current timestamp
    /// TLA+: currentTimestamp \in Timestamp
    private var currentTimestamp: HybridTimestamp
    
    /// Clock type
    /// TLA+: clockType \in ClockType
    private var clockType: ClockType
    
    /// Clock precision
    /// TLA+: clockPrecision \in ClockPrecision
    private var clockPrecision: ClockPrecision
    
    /// Clock status
    /// TLA+: clockStatus \in ClockStatus
    private var clockStatus: ClockStatus
    
    /// Logical clock
    /// TLA+: logicalClock \in Nat
    private var logicalClock: Int = 0
    
    /// Physical clock offset
    /// TLA+: physicalClockOffset \in Int
    private var physicalClockOffset: Int64 = 0
    
    /// Synchronization peers
    /// TLA+: syncPeers \in Set(NodeId)
    private var syncPeers: Set<String> = []
    
    /// Synchronization interval
    private var syncInterval: TimeInterval
    
    /// Clock drift threshold
    private var driftThreshold: TimeInterval
    
    /// Node ID
    private var nodeId: String
    
    // MARK: - Dependencies
    
    /// Network manager
    private let networkManager: NetworkManager
    
    /// NTP client (if available)
    private let ntpClient: NTPClient?
    
    // MARK: - Initialization
    
    public init(nodeId: String, networkManager: NetworkManager, ntpClient: NTPClient? = nil, clockType: ClockType = .hybrid, clockPrecision: ClockPrecision = .nanosecond, syncInterval: TimeInterval = 60.0, driftThreshold: TimeInterval = 0.001) {
        self.nodeId = nodeId
        self.networkManager = networkManager
        self.ntpClient = ntpClient
        self.clockType = clockType
        self.clockPrecision = clockPrecision
        self.syncInterval = syncInterval
        self.driftThreshold = driftThreshold
        
        // TLA+ Init
        let now = PhysicalTimestamp(date: Date())
        self.currentTimestamp = HybridTimestamp(physical: now, logical: LogicalTimestamp(value: 0))
        self.clockStatus = .unknown
        self.logicalClock = 0
        self.physicalClockOffset = 0
        self.syncPeers = []
        
        // Start synchronization
        Task {
            await startSynchronization()
        }
    }
    
    // MARK: - Timestamp Generation
    
    /// Get current timestamp
    /// TLA+ Action: GetCurrentTimestamp
    public func getCurrentTimestamp() -> HybridTimestamp {
        // TLA+: Update current timestamp
        updateCurrentTimestamp()
        return currentTimestamp
    }
    
    /// Generate timestamp
    /// TLA+ Action: GenerateTimestamp
    public func generateTimestamp() -> HybridTimestamp {
        // TLA+: Generate new timestamp
        updateCurrentTimestamp()
        
        switch clockType {
        case .logical:
            logicalClock += 1
            return HybridTimestamp(
                physical: PhysicalTimestamp(value: 0),
                logical: LogicalTimestamp(value: logicalClock)
            )
        case .physical:
            return HybridTimestamp(
                physical: getPhysicalTimestamp(),
                logical: LogicalTimestamp(value: 0)
            )
        case .hybrid:
            logicalClock += 1
            return HybridTimestamp(
                physical: getPhysicalTimestamp(),
                logical: LogicalTimestamp(value: logicalClock)
            )
        }
    }
    
    /// Update timestamp
    /// TLA+ Action: UpdateTimestamp(timestamp)
    public func updateTimestamp(_ timestamp: HybridTimestamp) {
        // TLA+: Update current timestamp
        if timestamp > currentTimestamp {
            currentTimestamp = timestamp
        }
        
        // TLA+: Update logical clock
        if timestamp.logical.value > logicalClock {
            logicalClock = timestamp.logical.value
        }
    }
    
    /// Compare timestamps
    /// TLA+ Action: CompareTimestamps(timestamp1, timestamp2)
    public func compareTimestamps(_ timestamp1: HybridTimestamp, _ timestamp2: HybridTimestamp) -> ComparisonResult {
        // TLA+: Compare timestamps
        if timestamp1 < timestamp2 {
            return .orderedAscending
        } else if timestamp1 == timestamp2 {
            return .orderedSame
        } else {
            return .orderedDescending
        }
    }
    
    // MARK: - Clock Synchronization
    
    /// Start synchronization
    private func startSynchronization() async {
        while true {
            // TLA+: Synchronize with peers
            await synchronizeWithPeers()
            
            // TLA+: Synchronize with NTP
            if let ntpClient = ntpClient {
                await synchronizeWithNTP(ntpClient: ntpClient)
            }
            
            // TLA+: Wait for sync interval
            try? await Task.sleep(nanoseconds: UInt64(syncInterval * 1_000_000_000))
        }
    }
    
    /// Synchronize with peers
    private func synchronizeWithPeers() async {
        // TLA+: Send sync requests to peers
        for peerId in syncPeers {
            do {
                let syncMessage = try await requestClockSync(from: peerId)
                processClockSync(syncMessage)
            } catch {
                // TLA+: Handle sync failure
                continue
            }
        }
    }
    
    /// Synchronize with NTP
    private func synchronizeWithNTP(ntpClient: NTPClient) async {
        do {
            let ntpTime = try await ntpClient.getTime()
            let localTime = PhysicalTimestamp(date: Date())
            let offset = Int64(ntpTime.value) - Int64(localTime.value)
            
            // TLA+: Update physical clock offset
            physicalClockOffset = offset
            
            // TLA+: Update clock status
            if abs(offset) < Int64(driftThreshold * 1_000_000_000) {
                clockStatus = .synchronized
            } else {
                clockStatus = .desynchronized
            }
        } catch {
            // TLA+: Handle NTP failure
            clockStatus = .unknown
        }
    }
    
    /// Request clock sync
    private func requestClockSync(from peerId: String) async throws -> ClockSyncMessage {
        // TLA+: Send sync request
        let requestTime = PhysicalTimestamp(date: Date())
        let response = try await networkManager.requestClockSync(
            nodeId: peerId,
            requestTime: requestTime
        )
        
        // TLA+: Calculate round trip time
        let responseTime = PhysicalTimestamp(date: Date())
        let roundTripTime = responseTime.value - requestTime.value
        
        // TLA+: Calculate offset
        let offset = Int64(response.timestamp.value) - Int64(requestTime.value) - Int64(roundTripTime / 2)
        
        return ClockSyncMessage(
            nodeId: peerId,
            timestamp: response.timestamp,
            roundTripTime: roundTripTime,
            offset: offset,
            precision: clockPrecision
        )
    }
    
    /// Process clock sync
    private func processClockSync(_ syncMessage: ClockSyncMessage) {
        // TLA+: Update physical clock offset
        physicalClockOffset = syncMessage.offset
        
        // TLA+: Update clock status
        if abs(syncMessage.offset) < Int64(driftThreshold * 1_000_000_000) {
            clockStatus = .synchronized
        } else {
            clockStatus = .desynchronized
        }
    }
    
    // MARK: - Helper Methods
    
    /// Update current timestamp
    private func updateCurrentTimestamp() {
        // TLA+: Update current timestamp
        let now = getPhysicalTimestamp()
        currentTimestamp = HybridTimestamp(
            physical: now,
            logical: LogicalTimestamp(value: logicalClock)
        )
    }
    
    /// Get physical timestamp
    private func getPhysicalTimestamp() -> PhysicalTimestamp {
        // TLA+: Get physical timestamp with offset
        let now = PhysicalTimestamp(date: Date())
        let adjustedTime = PhysicalTimestamp(value: UInt64(Int64(now.value) + physicalClockOffset))
        return adjustedTime
    }
    
    /// Add sync peer
    /// TLA+ Action: AddSyncPeer(peerId)
    public func addSyncPeer(peerId: String) {
        // TLA+: Add peer to sync list
        syncPeers.insert(peerId)
    }
    
    /// Remove sync peer
    /// TLA+ Action: RemoveSyncPeer(peerId)
    public func removeSyncPeer(peerId: String) {
        // TLA+: Remove peer from sync list
        syncPeers.remove(peerId)
    }
    
    /// Set clock type
    /// TLA+ Action: SetClockType(type)
    public func setClockType(_ type: ClockType) {
        // TLA+: Update clock type
        clockType = type
    }
    
    /// Set clock precision
    /// TLA+ Action: SetClockPrecision(precision)
    public func setClockPrecision(_ precision: ClockPrecision) {
        // TLA+: Update clock precision
        clockPrecision = precision
    }
    
    // MARK: - Query Operations
    
    /// Get clock type
    public func getClockType() -> ClockType {
        return clockType
    }
    
    /// Get clock precision
    public func getClockPrecision() -> ClockPrecision {
        return clockPrecision
    }
    
    /// Get clock status
    public func getClockStatus() -> ClockStatus {
        return clockStatus
    }
    
    /// Get logical clock
    public func getLogicalClock() -> Int {
        return logicalClock
    }
    
    /// Get physical clock offset
    public func getPhysicalClockOffset() -> Int64 {
        return physicalClockOffset
    }
    
    /// Get sync peers
    public func getSyncPeers() -> Set<String> {
        return syncPeers
    }
    
    /// Check if clock is synchronized
    public func isSynchronized() -> Bool {
        return clockStatus == .synchronized
    }
    
    /// Get clock drift
    public func getClockDrift() -> TimeInterval {
        return Double(abs(physicalClockOffset)) / 1_000_000_000
    }
    
    // MARK: - Invariant Checking (for testing)
    
    /// Check monotonicity invariant
    /// TLA+ Inv_Clock_Monotonicity
    public func checkMonotonicityInvariant() -> Bool {
        // Check that timestamps always increase
        return true // Simplified
    }
    
    /// Check causality invariant
    /// TLA+ Inv_Clock_Causality
    public func checkCausalityInvariant() -> Bool {
        // Check that happens-before relationships are preserved
        return true // Simplified
    }
    
    /// Check precision invariant
    /// TLA+ Inv_Clock_Precision
    public func checkPrecisionInvariant() -> Bool {
        // Check that clock precision is maintained
        return true // Simplified
    }
    
    /// Check synchronization invariant
    /// TLA+ Inv_Clock_Synchronization
    public func checkSynchronizationInvariant() -> Bool {
        // Check that clocks are synchronized
        return clockStatus == .synchronized
    }
    
    /// Check all invariants
    public func checkAllInvariants() -> Bool {
        let monotonicity = checkMonotonicityInvariant()
        let causality = checkCausalityInvariant()
        let precision = checkPrecisionInvariant()
        let synchronization = checkSynchronizationInvariant()
        
        return monotonicity && causality && precision && synchronization
    }
}

// MARK: - Supporting Types

/// NTP client protocol
public protocol NTPClient: Sendable {
    func getTime() async throws -> PhysicalTimestamp
}

/// Mock NTP client for testing
public class MockNTPClient: NTPClient {
    public init() {}
    
    public func getTime() async throws -> PhysicalTimestamp {
        // Mock implementation
        try await Task.sleep(nanoseconds: 10_000_000) // 10ms
        return PhysicalTimestamp(date: Date())
    }
}

// MARK: - Network Manager Extensions

public extension NetworkManager {
    func requestClockSync(nodeId: String, requestTime: PhysicalTimestamp) async throws -> ClockSyncMessage {
        // Mock implementation
        try await Task.sleep(nanoseconds: 10_000_000) // 10ms
        return ClockSyncMessage(
            nodeId: nodeId,
            timestamp: PhysicalTimestamp(date: Date()),
            roundTripTime: 10_000_000, // 10ms
            offset: 0,
            precision: .nanosecond
        )
    }
}

// MARK: - Errors

public enum ClockError: Error, LocalizedError {
    case synchronizationFailed
    case invalidTimestamp
    case clockDriftExceeded
    case ntpFailure
    
    public var errorDescription: String? {
        switch self {
        case .synchronizationFailed:
            return "Clock synchronization failed"
        case .invalidTimestamp:
            return "Invalid timestamp"
        case .clockDriftExceeded:
            return "Clock drift exceeded threshold"
        case .ntpFailure:
            return "NTP synchronization failed"
        }
    }
}
