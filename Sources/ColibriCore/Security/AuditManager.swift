//
//  AuditManager.swift
//  ColibrìDB Audit Manager
//
//  Implements: Audit logging and tracking
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//

import Foundation

// MARK: - Types

/// Audit event type
public enum AuditEventType: String, Codable, Sendable {
    case login
    case logout
    case query
    case dataModification
    case schemaChange
    case accessDenied
}

/// Audit event
public struct AuditEvent: Codable, @unchecked Sendable {
    public let eventId: String
    public let eventType: AuditEventType
    public let userId: String?
    public let timestamp: Date
    public let details: String
    public let success: Bool
    
    public init(eventId: String = UUID().uuidString, eventType: AuditEventType, userId: String? = nil, timestamp: Date = Date(), details: String, success: Bool = true) {
        self.eventId = eventId
        self.eventType = eventType
        self.userId = userId
        self.timestamp = timestamp
        self.details = details
        self.success = success
    }
}

// MARK: - Protocol Definition

/// Audit manager protocol
public protocol AuditManager: Sendable {
    func log(_ event: AuditEvent) async
    func getAuditLog(limit: Int) async -> [AuditEvent]
}

// MARK: - Protocol Implementation

/// Default audit manager implementation
public actor DefaultAuditManager: AuditManager {
    // MARK: - Properties
    
    private var events: [AuditEvent] = []
    private let maxEvents: Int
    
    // MARK: - Initialization
    
    /// Initialize audit manager
    /// - Parameter maxEvents: Maximum number of events to keep in memory
    public init(maxEvents: Int = 10000) {
        self.maxEvents = maxEvents
    }
    
    // MARK: - Protocol Implementation
    
    /// Log an audit event
    /// - Parameter event: Audit event to log
    public func log(_ event: AuditEvent) async {
        events.append(event)
        // Keep only the most recent events
        if events.count > maxEvents {
            events.removeFirst(events.count - maxEvents)
        }
    }
    
    /// Get audit log entries
    /// - Parameter limit: Maximum number of events to return
    /// - Returns: Array of audit events
    public func getAuditLog(limit: Int = 100) async -> [AuditEvent] {
        return Array(events.suffix(limit))
    }
}

