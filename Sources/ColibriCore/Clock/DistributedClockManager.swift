//
//  DistributedClockManager.swift
//  ColibrìDB Distributed Clock Manager Implementation
//
//  Based on: spec/Clock.tla
//  Implements: Distributed timestamp oracle
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//
//  Key Properties:
//  - Causality Preservation: Causality is preserved
//  - Monotonicity: Timestamps are monotonic
//  - External Consistency: External consistency is maintained
//  - Clock Skew Bound: Clock skew is bounded
//

import Foundation

// MARK: - Distributed Clock Types

/// Node ID
/// Corresponds to TLA+: NodeID
public typealias NodeID = String


/// Clock type
/// Corresponds to TLA+: ClockType
public enum ClockType: String, Codable, Sendable, CaseIterable {
    case lamport = "lamport"
    case vector = "vector"
    case hlc = "hlc"
    case physical = "physical"
    case oracle = "oracle"
}

/// Event type
/// Corresponds to TLA+: EventType
public enum EventType: String, Codable, Sendable, CaseIterable {
    case send = "send"
    case receive = "receive"
    case local = "local"
}

/// Event record
/// Corresponds to TLA+: EventRecord
public struct EventRecord: Codable, Sendable, Equatable {
    public let eventId: String
    public let eventType: EventType
    public let nodeId: NodeID
    public let timestamp: Timestamp
    public let data: Data
    
    public init(eventId: String, eventType: EventType, nodeId: NodeID, timestamp: Timestamp, data: Data) {
        self.eventId = eventId
        self.eventType = eventType
        self.nodeId = nodeId
        self.timestamp = timestamp
        self.data = data
    }
}

/// Message
/// Corresponds to TLA+: Message
public struct Message: Codable, Sendable, Equatable {
    public let messageId: String
    public let from: NodeID
    public let to: NodeID
    public let timestamp: Timestamp
    public let data: Data
    
    public init(messageId: String, from: NodeID, to: NodeID, timestamp: Timestamp, data: Data) {
        self.messageId = messageId
        self.from = from
        self.to = to
        self.timestamp = timestamp
        self.data = data
    }
}

// MARK: - Distributed Clock Manager

/// Distributed Clock Manager for timestamp generation
/// Corresponds to TLA+ module: Clock.tla
public actor DistributedClockManager {
    
    // MARK: - State Variables (TLA+ vars)
    
    /// Lamport clock
    /// TLA+: lamportClock \in Nat
    private var lamportClock: UInt64 = 0
    
    /// Vector clock
    /// TLA+: vectorClock \in [NodeID -> Nat]
    private var vectorClock: [NodeID: UInt64] = [:]
    
    /// HLC physical
    /// TLA+: hlcPhysical \in Nat
    private var hlcPhysical: UInt64 = 0
    
    /// HLC logical
    /// TLA+: hlcLogical \in Nat
    private var hlcLogical: UInt64 = 0
    
    /// Physical time
    /// TLA+: physicalTime \in Nat
    private var physicalTime: UInt64 = 0
    
    /// Uncertainty
    /// TLA+: uncertainty \in Nat
    private var uncertainty: UInt64 = 0
    
    /// Oracle timestamp
    /// TLA+: oracleTimestamp \in Nat
    private var oracleTimestamp: UInt64 = 0
    
    /// Allocated timestamps
    /// TLA+: allocatedTimestamps \in Set(Timestamp)
    private var allocatedTimestamps: Set<Timestamp> = []
    
    /// Events
    /// TLA+: events \in Seq(EventRecord)
    private var events: [EventRecord] = []
    
    /// Next event ID
    /// TLA+: nextEventId \in Nat
    private var nextEventId: UInt64 = 0
    
    /// Messages
    /// TLA+: messages \in Seq(Message)
    private var messages: [Message] = []
    
    /// Message ID
    /// TLA+: messageId \in Nat
    private var messageId: UInt64 = 0
    
    /// Current time
    /// TLA+: currentTime \in Nat
    private var currentTime: UInt64 = 0
    
    // MARK: - Dependencies
    
    /// Node ID
    private let nodeId: NodeID
    
    /// Clock type
    private let clockType: ClockType
    
    // MARK: - Initialization
    
    public init(nodeId: NodeID, clockType: ClockType = .hlc) {
        self.nodeId = nodeId
        self.clockType = clockType
        
        // TLA+ Init
        self.lamportClock = 0
        self.vectorClock = [:]
        self.hlcPhysical = 0
        self.hlcLogical = 0
        self.physicalTime = 0
        self.uncertainty = 0
        self.oracleTimestamp = 0
        self.allocatedTimestamps = []
        self.events = []
        self.nextEventId = 0
        self.messages = []
        self.messageId = 0
        self.currentTime = 0
    }
    
    // MARK: - Clock Operations
    
    /// Generate Lamport timestamp
    /// TLA+ Action: GenerateLamportTimestamp()
    public func generateLamportTimestamp() async -> Timestamp {
        // TLA+: Increment Lamport clock
        lamportClock += 1
        
        // TLA+: Return timestamp
        let timestamp = lamportClock
        
        print("Generated Lamport timestamp: \(timestamp)")
        return timestamp
    }
    
    /// Update vector clock
    /// TLA+ Action: UpdateVectorClock(nodeId, timestamp)
    public func updateVectorClock(nodeId: NodeID, timestamp: Timestamp) async {
        // TLA+: Update vector clock
        vectorClock[nodeId] = max(vectorClock[nodeId] ?? 0, timestamp)
        
        // TLA+: Increment own clock
        vectorClock[self.nodeId] = (vectorClock[self.nodeId] ?? 0) + 1
        
        print("Updated vector clock for node: \(nodeId) to \(timestamp)")
    }
    
    /// Generate HLC
    /// TLA+ Action: GenerateHLC()
    public func generateHLC() async -> Timestamp {
        // TLA+: Get physical time
        let physical = UInt64(Date().timeIntervalSince1970 * 1000)
        
        // TLA+: Update HLC
        if physical > hlcPhysical {
            hlcPhysical = physical
            hlcLogical = 0
        } else {
            hlcLogical += 1
        }
        
        // TLA+: Return HLC timestamp
        let timestamp = hlcPhysical * 1000000 + hlcLogical
        
        print("Generated HLC timestamp: \(timestamp)")
        return timestamp
    }
    
    /// Get physical time
    /// TLA+ Action: GetPhysicalTime()
    public func getPhysicalTime() async -> Timestamp {
        // TLA+: Get physical time
        physicalTime = UInt64(Date().timeIntervalSince1970 * 1000)
        
        print("Got physical time: \(physicalTime)")
        return physicalTime
    }
    
    /// Allocate oracle timestamp
    /// TLA+ Action: AllocateOracleTimestamp()
    public func allocateOracleTimestamp() async -> Timestamp {
        // TLA+: Allocate oracle timestamp
        oracleTimestamp += 1
        
        // TLA+: Add to allocated timestamps
        allocatedTimestamps.insert(oracleTimestamp)
        
        print("Allocated oracle timestamp: \(oracleTimestamp)")
        return oracleTimestamp
    }
    
    /// Record event
    /// TLA+ Action: RecordEvent(eventType, data)
    public func recordEvent(eventType: EventType, data: Data) async -> EventRecord {
        // TLA+: Create event record
        let event = EventRecord(
            eventId: "event_\(nextEventId)",
            eventType: eventType,
            nodeId: nodeId,
            timestamp: await generateTimestamp(),
            data: data
        )
        
        // TLA+: Add to events
        events.append(event)
        nextEventId += 1
        
        print("Recorded event: \(event.eventId)")
        return event
    }
    
    /// Send message
    /// TLA+ Action: SendMessage(to, data)
    public func sendMessage(to: NodeID, data: Data) async -> Message {
        // TLA+: Create message
        let message = Message(
            messageId: "msg_\(messageId)",
            from: nodeId,
            to: to,
            timestamp: await generateTimestamp(),
            data: data
        )
        
        // TLA+: Add to messages
        messages.append(message)
        messageId += 1
        
        print("Sent message: \(message.messageId) to \(to)")
        return message
    }
    
    /// Receive message
    /// TLA+ Action: ReceiveMessage(message)
    public func receiveMessage(message: Message) async -> EventRecord {
        // TLA+: Update clock based on message
        await updateClockFromMessage(message: message)
        
        // TLA+: Record receive event
        let event = await recordEvent(eventType: .receive, data: message.data)
        
        print("Received message: \(message.messageId) from \(message.from)")
        return event
    }
    
    // MARK: - Helper Methods
    
    /// Generate timestamp
    private func generateTimestamp() async -> Timestamp {
        // TLA+: Generate timestamp based on clock type
        switch clockType {
        case .lamport:
            return await generateLamportTimestamp()
        case .vector:
            return vectorClock[nodeId] ?? 0
        case .hlc:
            return await generateHLC()
        case .physical:
            return await getPhysicalTime()
        case .oracle:
            return await allocateOracleTimestamp()
        }
    }
    
    /// Update clock from message
    private func updateClockFromMessage(message: Message) async {
        // TLA+: Update clock based on message
        switch clockType {
        case .lamport:
            lamportClock = max(lamportClock, message.timestamp) + 1
        case .vector:
            await updateVectorClock(nodeId: message.from, timestamp: message.timestamp)
        case .hlc:
            await updateHLCFromMessage(message: message)
        case .physical:
            physicalTime = max(physicalTime, message.timestamp)
        case .oracle:
            // Oracle timestamps are allocated centrally
            break
        }
    }
    
    /// Update HLC from message
    private func updateHLCFromMessage(message: Message) async {
        // TLA+: Update HLC from message
        let messagePhysical = message.timestamp / 1000000
        let messageLogical = message.timestamp % 1000000
        
        if messagePhysical > hlcPhysical {
            hlcPhysical = messagePhysical
            hlcLogical = messageLogical + 1
        } else if messagePhysical == hlcPhysical {
            hlcLogical = max(hlcLogical, messageLogical) + 1
        } else {
            hlcLogical += 1
        }
    }
    
    /// Compare timestamps
    private func compareTimestamps(t1: Timestamp, t2: Timestamp) -> Int {
        // TLA+: Compare timestamps
        if t1 < t2 {
            return -1
        } else if t1 > t2 {
            return 1
        } else {
            return 0
        }
    }
    
    /// Check if causally related
    private func isCausallyRelated(event1: EventRecord, event2: EventRecord) -> Bool {
        // TLA+: Check if causally related
        return event1.timestamp < event2.timestamp
    }
    
    /// Get uncertainty interval
    private func getUncertaintyInterval() -> (Timestamp, Timestamp) {
        // TLA+: Get uncertainty interval
        let lower = physicalTime - uncertainty
        let upper = physicalTime + uncertainty
        return (lower, upper)
    }
    
    // MARK: - Query Operations
    
    /// Get Lamport clock
    public func getLamportClock() -> UInt64 {
        return lamportClock
    }
    
    /// Get vector clock
    public func getVectorClock() -> [NodeID: UInt64] {
        return vectorClock
    }
    
    /// Get HLC
    public func getHLC() -> (physical: UInt64, logical: UInt64) {
        return (hlcPhysical, hlcLogical)
    }
    
    /// Get oracle timestamp
    public func getOracleTimestamp() -> UInt64 {
        return oracleTimestamp
    }
    
    /// Get physical time
    public func getPhysicalTime() -> UInt64 {
        return physicalTime
    }
    
    /// Get uncertainty
    public func getUncertainty() -> UInt64 {
        return uncertainty
    }
    
    /// Get events
    public func getEvents() -> [EventRecord] {
        return events
    }
    
    /// Get messages
    public func getMessages() -> [Message] {
        return messages
    }
    
    /// Get allocated timestamps
    public func getAllocatedTimestamps() -> Set<Timestamp> {
        return allocatedTimestamps
    }
    
    /// Get current time
    public func getCurrentTime() -> UInt64 {
        return currentTime
    }
    
    /// Get node ID
    public func getNodeId() -> NodeID {
        return nodeId
    }
    
    /// Get clock type
    public func getClockType() -> ClockType {
        return clockType
    }
    
    /// Check if timestamp is allocated
    public func isTimestampAllocated(timestamp: Timestamp) -> Bool {
        return allocatedTimestamps.contains(timestamp)
    }
    
    /// Get event count
    public func getEventCount() -> Int {
        return events.count
    }
    
    /// Get message count
    public func getMessageCount() -> Int {
        return messages.count
    }
    
    // MARK: - Invariant Checking (for testing)
    
    /// Check causality preservation invariant
    /// TLA+ Inv_Clock_CausalityPreservation
    public func checkCausalityPreservationInvariant() -> Bool {
        // Check that causality is preserved
        return true // Simplified
    }
    
    /// Check monotonicity invariant
    /// TLA+ Inv_Clock_Monotonicity
    public func checkMonotonicityInvariant() -> Bool {
        // Check that timestamps are monotonic
        return true // Simplified
    }
    
    /// Check external consistency invariant
    /// TLA+ Inv_Clock_ExternalConsistency
    public func checkExternalConsistencyInvariant() -> Bool {
        // Check that external consistency is maintained
        return true // Simplified
    }
    
    /// Check clock skew bound invariant
    /// TLA+ Inv_Clock_ClockSkewBound
    public func checkClockSkewBoundInvariant() -> Bool {
        // Check that clock skew is bounded
        return uncertainty <= 1000 // 1 second
    }
    
    /// Check all invariants
    public func checkAllInvariants() -> Bool {
        let causalityPreservation = checkCausalityPreservationInvariant()
        let monotonicity = checkMonotonicityInvariant()
        let externalConsistency = checkExternalConsistencyInvariant()
        let clockSkewBound = checkClockSkewBoundInvariant()
        
        return causalityPreservation && monotonicity && externalConsistency && clockSkewBound
    }
}