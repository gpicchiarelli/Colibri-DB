//
//  Clock.swift
//  ColibrìDB Distributed Clock (Lamport/Hybrid Logical Clock)
//
//  Based on: spec/Clock.tla
//  Implements: Hybrid Logical Clock for distributed timestamps
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//

import Foundation

/// Hybrid Logical Clock
/// Combines physical time with logical counter for total ordering
/// Based on: "Logical Physical Clocks" (Kulkarni & Demirbas, 2014)
public actor HybridLogicalClock {
    // MARK: - State
    
    /// Physical time component (milliseconds since epoch)
    private var physicalTime: UInt64 = 0
    
    /// Logical counter
    private var logicalCounter: UInt64 = 0
    
    /// Node ID for disambiguation
    private let nodeID: UInt64
    
    // MARK: - Initialization
    
    public init(nodeID: UInt64) {
        self.nodeID = nodeID
        self.physicalTime = currentPhysicalTime()
        self.logicalCounter = 0
    }
    
    // MARK: - Clock Operations
    
    /// Generate new timestamp for local event
    public func tick() -> Timestamp {
        let currentTime = currentPhysicalTime()
        
        if currentTime > physicalTime {
            // Physical time advanced
            physicalTime = currentTime
            logicalCounter = 0
        } else {
            // Physical time same or behind, increment logical
            logicalCounter += 1
        }
        
        return encodeTimestamp()
    }
    
    /// Update clock on receiving message
    public func update(receivedTimestamp: Timestamp) -> Timestamp {
        let (recvPhysical, recvLogical, _) = decodeTimestamp(receivedTimestamp)
        let currentTime = currentPhysicalTime()
        
        let maxPhysical = max(currentTime, max(physicalTime, recvPhysical))
        
        if maxPhysical == physicalTime && maxPhysical == recvPhysical {
            // Both clocks at same physical time
            logicalCounter = max(logicalCounter, recvLogical) + 1
        } else if maxPhysical == physicalTime {
            // Our physical time is max
            logicalCounter += 1
        } else if maxPhysical == recvPhysical {
            // Received physical time is max
            physicalTime = recvPhysical
            logicalCounter = recvLogical + 1
        } else {
            // Current time is max
            physicalTime = currentTime
            logicalCounter = 0
        }
        
        physicalTime = maxPhysical
        
        return encodeTimestamp()
    }
    
    // MARK: - Private Helpers
    
    private func currentPhysicalTime() -> UInt64 {
        return UInt64(Date().timeIntervalSince1970 * 1000)  // milliseconds
    }
    
    private func encodeTimestamp() -> Timestamp {
        // Encode: physical (48 bits) | logical (12 bits) | nodeID (4 bits)
        return (physicalTime << 16) | ((logicalCounter & 0xFFF) << 4) | (nodeID & 0xF)
    }
    
    private func decodeTimestamp(_ timestamp: Timestamp) -> (UInt64, UInt64, UInt64) {
        let physical = timestamp >> 16
        let logical = (timestamp >> 4) & 0xFFF
        let node = timestamp & 0xF
        return (physical, logical, node)
    }
}

