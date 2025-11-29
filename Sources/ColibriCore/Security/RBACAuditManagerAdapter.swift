//
//  RBACAuditManagerAdapter.swift
//  ColibrìDB RBAC Audit Manager Adapter
//
//  Adapter to make RBACManager compatible with AuditManager protocol
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//

import Foundation

/// Adapter to use RBACManager's audit log as AuditManager
public actor RBACAuditManagerAdapter: AuditManager {
    // MARK: - Properties
    
    private let rbacManager: RBACManager
    
    // MARK: - Initialization
    
    /// Initialize RBAC audit manager adapter
    /// - Parameter rbacManager: RBAC manager to adapt
    public init(rbacManager: RBACManager) {
        self.rbacManager = rbacManager
    }
    
    // MARK: - Protocol Implementation
    
    /// Log an audit event
    /// - Parameter event: Audit event to log
    public func log(_ event: AuditEvent) async {
        // RBACManager already logs events, so we just need to access them
        // The event is already logged by RBACManager operations
    }
    
    /// Get audit log entries from RBAC manager
    /// - Parameter limit: Maximum number of events to return
    /// - Returns: Array of audit events
    public func getAuditLog(limit: Int = 100) async -> [AuditEvent] {
        let rbacEvents = await rbacManager.getAuditLog()
        let sliced = rbacEvents.suffix(limit)
        return sliced.map { event in
            let eventType = mapEventType(event.event)
            let timestamp = Date(timeIntervalSince1970: TimeInterval(event.time))
            let userId = event.user ?? event.admin
            let detailsComponents: [String] = [
                "event=\(event.event)",
                event.role.map { "role=\($0)" },
                event.permission.map { "permission=\(String(describing: $0))" },
                event.sessionId.map { "session=\($0)" }
            ].compactMap { $0 }
            let details = detailsComponents.joined(separator: "; ")
            
            return AuditEvent(
                eventType: eventType,
                userId: userId,
                timestamp: timestamp,
                details: details.isEmpty ? event.event : details,
                success: true
            )
        }
    }
    
    // MARK: - Private Helpers
    
    /// Map RBAC event name to audit event type
    /// - Parameter eventName: RBAC event name
    /// - Returns: Corresponding audit event type
    private func mapEventType(_ eventName: String) -> AuditEventType {
        switch eventName {
        case "LOGIN", "SESSION_STARTED":
            return .login
        case "LOGOUT", "SESSION_ENDED":
            return .logout
        case "PERMISSION_DENIED", "ACCESS_DENIED":
            return .accessDenied
        case "ROLE_ASSIGNED", "ROLE_REVOKED", "PERMISSION_GRANTED", "PERMISSION_REVOKED":
            return .dataModification
        default:
            return .query
        }
    }
}

extension RBACAuditManagerAdapter: PolicyAuditLogger {
    public func auditEvent(event: String, metadata: [String: String]) async throws {
        let details = metadata.map { "\($0.key)=\($0.value)" }.sorted().joined(separator: "; ")
        let auditEvent = AuditEvent(
            eventType: mapEventType(event),
            userId: metadata["user"] ?? metadata["admin"],
            details: details.isEmpty ? event : details,
            success: true
        )
        await log(auditEvent)
    }
}

