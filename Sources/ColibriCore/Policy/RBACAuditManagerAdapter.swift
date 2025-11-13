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
    private let rbacManager: RBACManager
    
    public init(rbacManager: RBACManager) {
        self.rbacManager = rbacManager
    }
    
    public func auditEvent(event: String, metadata: [String: String]) async throws {
        // RBACManager already logs events internally, so we just need to access them
        // The event is already logged by RBACManager operations
        // This is a no-op adapter since RBACManager handles its own audit logging
    }
}

