//
//  RBACAuditManagerAdapter.swift
//  ColibrìDB RBAC Audit Manager Adapter
//
//  Adapter to make RBACManager compatible with AuditManager protocol
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//

import Foundation

/// Audit manager protocol (for PolicyManager)
public protocol AuditManager: Sendable {
    func log(_ event: AuditEvent) async
    func getAuditLog(limit: Int) async -> [AuditEvent]
}

/// Adapter to use RBACManager's audit log as AuditManager
public actor RBACAuditManagerAdapter: AuditManager {
    private let rbacManager: RBACManager
    
    public init(rbacManager: RBACManager) {
        self.rbacManager = rbacManager
    }
    
    public func log(_ event: AuditEvent) async {
        // RBACManager already logs events, so we just need to access them
        // The event is already logged by RBACManager operations
    }
    
    public func getAuditLog(limit: Int = 100) async -> [AuditEvent] {
        return await rbacManager.getAuditLog()
    }
}

