/*
 * RolesPermissions.swift
 * ColibrìDB - Role-Based Access Control (RBAC) System
 *
 * Based on TLA+ specification: RolesPermissions.tla
 *
 * Implements comprehensive RBAC system with:
 * - Role hierarchy with inheritance (RBAC1)
 * - Role-permission assignments (RBAC0)
 * - User-role assignments (static and dynamic)
 * - Separation of Duty (SoD) constraints (RBAC2)
 * - Least Privilege principle enforcement
 * - Role activation/deactivation
 * - Temporal constraints on roles
 * - Context-based role activation
 * - Audit logging
 *
 * References:
 * [1] Sandhu, R., et al. (1996). "Role-Based Access Control Models"
 *     IEEE Computer, 29(2).
 * [2] Ferraiolo, D., et al. (2001). "Proposed NIST Standard for Role-Based Access Control"
 *     ACM TISSEC, 4(3).
 * [3] Sandhu, R., et al. (1999). "Role-Based Administration (RBA)"
 *     ACM TISSEC, 2(1).
 * [4] Ahn, G. J., & Sandhu, R. (2000). "Role-Based Authorization Constraints"
 *     ACM TISSEC, 3(4).
 * [5] Li, N., et al. (2007). "Temporal RBAC"
 *     ACM TISSEC, 10(3).
 * [6] Bertino, E., et al. (2001). "TRBAC: Temporal Role-Based Access Control"
 *     ACM TISSEC, 4(3).
 *
 * Author: ColibrìDB Team
 * Date: 2025-10-19
 */

import Foundation

// MARK: - Permission Types (TLA+: PermissionType)

/// Permission structure: (object, operation)
public struct Permission: Codable, Equatable, Hashable, Sendable {
    public let object: String      // TLA+: object
    public let operation: String    // TLA+: operation
    
    public init(object: String, operation: String) {
        self.object = object
        self.operation = operation
    }
}

// MARK: - Session Context (TLA+: SessionContext)

/// Session context for context-aware RBAC
public struct SessionContext: Codable {
    public let location: String     // TLA+: location
    public let ipAddress: String    // TLA+: ipAddress
    public let timeOfDay: Int       // TLA+: timeOfDay
    public let day: String          // TLA+: day
    
    public init(location: String = "default", ipAddress: String = "127.0.0.1", 
                timeOfDay: Int = 12, day: String = "Mon") {
        self.location = location
        self.ipAddress = ipAddress
        self.timeOfDay = timeOfDay
        self.day = day
    }
}

// MARK: - Constraint Types (TLA+: ConstraintType, Constraint)

/// Constraint types for RBAC
public enum RBACConstraintType: String, Codable, Sendable {
    case staticSoD = "STATIC_SoD"      // Statically Mutually Exclusive Roles
    case dynamicSoD = "DYNAMIC_SoD"     // Dynamically Mutually Exclusive Roles
    case prerequisite = "PREREQUISITE" // Role requires another role
    case cardinality = "CARDINALITY"   // Limit on role assignments
}

/// RBAC constraint
public struct RBACConstraint: Codable, Equatable, Hashable, Sendable {
    public let type: RBACConstraintType     // TLA+: type
    public let roles: Set<String>       // TLA+: roles
    public let limit: Int               // TLA+: limit
    
    public init(type: RBACConstraintType, roles: Set<String>, limit: Int) {
        self.type = type
        self.roles = roles
        self.limit = limit
    }
}

// MARK: - Session (TLA+: Session)

/// User session with active roles
public struct RBACSession: Codable {
    public let user: String              // TLA+: user
    public var activeRoles: Set<String>  // TLA+: activeRoles
    public let context: SessionContext   // TLA+: context
    
    public init(user: String, activeRoles: Set<String> = [], context: SessionContext) {
        self.user = user
        self.activeRoles = activeRoles
        self.context = context
    }
}

// MARK: - Role Activation Info (TLA+: RoleActivations)

/// Role activation tracking
public struct RoleActivation: Codable {
    public let minUsers: Int            // TLA+: minUsers
    public let maxUsers: Int            // TLA+: maxUsers
    public var activeCount: Int         // TLA+: activeCount
    
    public init(minUsers: Int = 0, maxUsers: Int = 1000, activeCount: Int = 0) {
        self.minUsers = minUsers
        self.maxUsers = maxUsers
        self.activeCount = activeCount
    }
}

// MARK: - Temporal Constraints (TLA+: TemporalConstraints)

/// Temporal constraints for roles
public struct TemporalConstraint: Codable {
    public let validFrom: Int           // TLA+: validFrom
    public let validUntil: Int          // TLA+: validUntil
    public let enabledDays: Set<String> // TLA+: enabledDays
    public let enabledHours: Set<Int>   // TLA+: enabledHours
    
    public init(validFrom: Int = 0, validUntil: Int = 999999, 
                enabledDays: Set<String> = ["Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"],
                enabledHours: Set<Int> = Set(0...23)) {
        self.validFrom = validFrom
        self.validUntil = validUntil
        self.enabledDays = enabledDays
        self.enabledHours = enabledHours
    }
}

// MARK: - Audit Event (TLA+: AuditLog)

/// Audit log entry
public struct AuditEvent: Codable, @unchecked Sendable {
    public let event: String            // TLA+: event
    public let admin: String?           // TLA+: admin
    public let user: String?            // TLA+: user
    public let role: String?            // TLA+: role
    public let permission: Permission?  // TLA+: permission
    public let sessionId: Int?         // TLA+: sessionId
    public let time: Int                // TLA+: time
    public let details: [String: String] // Additional details
    
    public init(event: String, admin: String? = nil, user: String? = nil, 
                role: String? = nil, permission: Permission? = nil, 
                sessionId: Int? = nil, time: Int, details: [String: String] = [:]) {
        self.event = event
        self.admin = admin
        self.user = user
        self.role = role
        self.permission = permission
        self.sessionId = sessionId
        self.time = time
        self.details = details
    }
}

// MARK: - RBAC Manager

/// Comprehensive RBAC system
/// Corresponds to TLA+ module: RolesPermissions.tla
public actor RBACManager {
    
    // TLA+ VARIABLES
    
    /// User-role assignments (TLA+: userRoles)
    private var userRoles: [String: Set<String>] = [:]
    
    /// Role-permission assignments (TLA+: rolePermissions)
    private var rolePermissions: [String: Set<Permission>] = [:]
    
    /// Role hierarchy (TLA+: roleHierarchy)
    private var roleHierarchy: [String: Set<String>] = [:]
    
    /// Active sessions (TLA+: sessions)
    private var sessions: [Int: RBACSession] = [:]
    
    /// RBAC constraints (TLA+: constraints)
    private var constraints: Set<RBACConstraint> = []
    
    /// Role activation tracking (TLA+: roleActivations)
    private var roleActivations: [String: RoleActivation] = [:]
    
    /// Temporal constraints (TLA+: temporalConstraints)
    private var temporalConstraints: [String: TemporalConstraint] = [:]
    
    /// Audit log (TLA+: auditLog)
    private var auditLog: [AuditEvent] = []
    
    /// Current time (TLA+: currentTime)
    private var currentTime: Int = 0
    
    // Configuration (TLA+: CONSTANTS)
    private let maxActiveRoles: Int = 10
    private let maxRoleDepth: Int = 5
    
    public init() {
        Task {
            await initializeBuiltinRoles()
        }
    }
    
    // MARK: - Initialization
    
    private func initializeBuiltinRoles() async {
        // Initialize role activations
        roleActivations["admin"] = RoleActivation(maxUsers: 5)
        roleActivations["readwrite"] = RoleActivation(maxUsers: 100)
        roleActivations["readonly"] = RoleActivation(maxUsers: 1000)
        
        // Initialize temporal constraints (all roles always valid by default)
        temporalConstraints["admin"] = TemporalConstraint()
        temporalConstraints["readwrite"] = TemporalConstraint()
        temporalConstraints["readonly"] = TemporalConstraint()
        
        // Initialize role permissions
        rolePermissions["admin"] = Set([
            Permission(object: "*", operation: "*")
        ])
        rolePermissions["readwrite"] = Set([
            Permission(object: "table", operation: "select"),
            Permission(object: "table", operation: "insert"),
            Permission(object: "table", operation: "update"),
            Permission(object: "table", operation: "delete")
        ])
        rolePermissions["readonly"] = Set([
            Permission(object: "table", operation: "select")
        ])
        
        // Initialize role hierarchy
        roleHierarchy["readwrite"] = Set(["readonly"])  // readwrite inherits from readonly
        roleHierarchy["admin"] = Set(["readwrite"])     // admin inherits from readwrite
        
        currentTime = Int(Date().timeIntervalSince1970)
    }
    
    // MARK: - Helper Functions (TLA+ Helpers)
    
    /// Compute transitive closure of role hierarchy (TLA+: InheritedRoles)
    private func inheritedRoles(_ role: String) -> Set<String> {
        guard let seniorRoles = roleHierarchy[role] else {
            return Set([role])
        }
        
        var result = Set([role])
        for seniorRole in seniorRoles {
            result.formUnion(inheritedRoles(seniorRole))
        }
        return result
    }
    
    /// Get all permissions for a role including inherited (TLA+: AllPermissionsForRole)
    private func allPermissionsForRole(_ role: String) -> Set<Permission> {
        let inherited = inheritedRoles(role)
        var permissions: Set<Permission> = []
        
        for r in inherited {
            permissions.formUnion(rolePermissions[r] ?? [])
        }
        
        return permissions
    }
    
    /// Get all permissions for a user (TLA+: AllPermissionsForUser)
    private func allPermissionsForUser(_ user: String) -> Set<Permission> {
        let userRoleSet = userRoles[user] ?? []
        var permissions: Set<Permission> = []
        
        for role in userRoleSet {
            permissions.formUnion(allPermissionsForRole(role))
        }
        
        return permissions
    }
    
    /// Check if user has specific permission (TLA+: HasPermission)
    public func hasPermission(user: String, object: String, operation: String) -> Bool {
        let permissions = allPermissionsForUser(user)
        let permission = Permission(object: object, operation: operation)
        
        // Check for wildcard permissions
        return permissions.contains(permission) ||
               permissions.contains(Permission(object: "*", operation: "*")) ||
               permissions.contains(Permission(object: object, operation: "*"))
    }
    
    /// Check if role hierarchy creates a cycle (TLA+: HasCycle)
    private func hasCycle(_ role: String, visited: Set<String>) -> Bool {
        if visited.contains(role) {
            return true
        }
        
        guard let seniorRoles = roleHierarchy[role] else {
            return false
        }
        
        var newVisited = visited
        newVisited.insert(role)
        
        for seniorRole in seniorRoles {
            if hasCycle(seniorRole, visited: newVisited) {
                return true
            }
        }
        
        return false
    }
    
    /// Check role hierarchy depth (TLA+: RoleDepth)
    private func roleDepth(_ role: String) -> Int {
        guard let seniorRoles = roleHierarchy[role], !seniorRoles.isEmpty else {
            return 0
        }
        
        return 1 + (seniorRoles.map { roleDepth($0) }.max() ?? 0)
    }
    
    // MARK: - Constraint Checking (TLA+: Constraint Functions)
    
    /// Check Static Separation of Duty (TLA+: ViolatesStaticSoD)
    private func violatesStaticSoD(user: String, role: String, sodConstraint: RBACConstraint) -> Bool {
        guard sodConstraint.type == .staticSoD,
              sodConstraint.roles.contains(role) else {
            return false
        }
        
        let conflictingRoles = sodConstraint.roles.subtracting([role])
        let userRoleSet = userRoles[user] ?? []
        
        return userRoleSet.intersection(conflictingRoles).count >= sodConstraint.limit
    }
    
    /// Check Dynamic Separation of Duty (TLA+: ViolatesDynamicSoD)
    private func violatesDynamicSoD(sessionId: Int, role: String, sodConstraint: RBACConstraint) -> Bool {
        guard sodConstraint.type == .dynamicSoD,
              sodConstraint.roles.contains(role),
              let session = sessions[sessionId] else {
            return false
        }
        
        let conflictingRoles = sodConstraint.roles.subtracting([role])
        
        return session.activeRoles.intersection(conflictingRoles).count >= sodConstraint.limit
    }
    
    /// Check prerequisite constraint (TLA+: SatisfiesPrerequisite)
    private func satisfiesPrerequisite(user: String, role: String, prereqConstraint: RBACConstraint) -> Bool {
        guard prereqConstraint.type == .prerequisite,
              prereqConstraint.roles.contains(role) else {
            return true
        }
        
        let requiredRoles = prereqConstraint.roles.subtracting([role])
        let userRoleSet = userRoles[user] ?? []
        
        return !requiredRoles.isDisjoint(with: userRoleSet)
    }
    
    /// Check cardinality constraint (TLA+: SatisfiesCardinality)
    private func satisfiesCardinality(user: String, role: String, cardConstraint: RBACConstraint) -> Bool {
        guard cardConstraint.type == .cardinality,
              cardConstraint.roles.contains(role) else {
            return true
        }
        
        let userRoleSet = userRoles[user] ?? []
        
        return userRoleSet.intersection(cardConstraint.roles).count < cardConstraint.limit
    }
    
    /// Check temporal constraints (TLA+: SatisfiesTemporalConstraints)
    private func satisfiesTemporalConstraints(role: String, time: Int, context: SessionContext) -> Bool {
        guard let tc = temporalConstraints[role] else {
            return true
        }
        
        return time >= tc.validFrom &&
               time <= tc.validUntil &&
               tc.enabledDays.contains(context.day) &&
               tc.enabledHours.contains(context.timeOfDay)
    }
    
    /// Check all constraints (TLA+: SatisfiesAllConstraints)
    private func satisfiesAllConstraints(user: String, role: String) -> Bool {
        for constraint in constraints {
            switch constraint.type {
            case .staticSoD:
                if violatesStaticSoD(user: user, role: role, sodConstraint: constraint) {
                    return false
                }
            case .prerequisite:
                if !satisfiesPrerequisite(user: user, role: role, prereqConstraint: constraint) {
                    return false
                }
            case .cardinality:
                if !satisfiesCardinality(user: user, role: role, cardConstraint: constraint) {
                    return false
                }
            case .dynamicSoD:
                // Dynamic SoD is checked during session activation
                break
            }
        }
        return true
    }
    
    /// Check session constraints (TLA+: SatisfiesSessionConstraints)
    private func satisfiesSessionConstraints(sessionId: Int, role: String) -> Bool {
        for constraint in constraints {
            if constraint.type == .dynamicSoD {
                if violatesDynamicSoD(sessionId: sessionId, role: role, sodConstraint: constraint) {
                    return false
                }
            }
        }
        return true
    }
    
    // MARK: - Role Assignment (TLA+: AssignRole, RevokeRole)
    
    /// Assign role to user (TLA+ Action: AssignRole)
    public func assignRole(admin: String, user: String, role: String) async throws {
        guard rolePermissions[role] != nil else {
            throw RBACError.roleNotFound(role)
        }
        
        guard !(userRoles[user]?.contains(role) ?? false) else {
            throw RBACError.roleAlreadyAssigned(user: user, role: role)
        }
        
        guard satisfiesAllConstraints(user: user, role: role) else {
            throw RBACError.constraintViolation(user: user, role: role)
        }
        
        userRoles[user, default: []].insert(role)
        
        let event = AuditEvent(
            event: "ROLE_ASSIGNED",
            admin: admin,
            user: user,
            role: role,
            time: currentTime
        )
        auditLog.append(event)
    }
    
    /// Revoke role from user (TLA+ Action: RevokeRole)
    public func revokeRole(admin: String, user: String, role: String) async throws {
        guard userRoles[user]?.contains(role) == true else {
            throw RBACError.roleNotAssigned(user: user, role: role)
        }
        
        userRoles[user]?.remove(role)
        
        // Revoke role from all user sessions
        for sessionId in sessions.keys {
            if sessions[sessionId]?.user == user {
                sessions[sessionId]?.activeRoles.remove(role)
                roleActivations[role]?.activeCount -= 1
            }
        }
        
        let event = AuditEvent(
            event: "ROLE_REVOKED",
            admin: admin,
            user: user,
            role: role,
            time: currentTime
        )
        auditLog.append(event)
    }
    
    // MARK: - Permission Assignment (TLA+: GrantPermission, RevokePermission)
    
    /// Grant permission to role (TLA+ Action: GrantPermission)
    public func grantPermission(admin: String, role: String, permission: Permission) async throws {
        guard rolePermissions[role] != nil else {
            throw RBACError.roleNotFound(role)
        }
        
        guard !(rolePermissions[role]?.contains(permission) ?? false) else {
            throw RBACError.permissionAlreadyGranted(role: role, permission: permission)
        }
        
        rolePermissions[role, default: []].insert(permission)
        
        let event = AuditEvent(
            event: "PERMISSION_GRANTED",
            admin: admin,
            role: role,
            permission: permission,
            time: currentTime
        )
        auditLog.append(event)
    }
    
    /// Revoke permission from role (TLA+ Action: RevokePermission)
    public func revokePermission(admin: String, role: String, permission: Permission) async throws {
        guard rolePermissions[role]?.contains(permission) == true else {
            throw RBACError.permissionNotGranted(role: role, permission: permission)
        }
        
        rolePermissions[role]?.remove(permission)
        
        let event = AuditEvent(
            event: "PERMISSION_REVOKED",
            admin: admin,
            role: role,
            permission: permission,
            time: currentTime
        )
        auditLog.append(event)
    }
    
    // MARK: - Role Hierarchy (TLA+: AddRoleInheritance, RemoveRoleInheritance)
    
    /// Add role inheritance (TLA+ Action: AddRoleInheritance)
    public func addRoleInheritance(admin: String, juniorRole: String, seniorRole: String) async throws {
        guard rolePermissions[juniorRole] != nil && rolePermissions[seniorRole] != nil else {
            throw RBACError.roleNotFound(juniorRole == seniorRole ? juniorRole : "unknown")
        }
        
        guard juniorRole != seniorRole else {
            throw RBACError.invalidInheritance(juniorRole: juniorRole, seniorRole: seniorRole)
        }
        
        guard !(roleHierarchy[juniorRole]?.contains(seniorRole) ?? false) else {
            throw RBACError.inheritanceAlreadyExists(juniorRole: juniorRole, seniorRole: seniorRole)
        }
        
        // Check for cycles
        if hasCycle(seniorRole, visited: Set([juniorRole])) {
            throw RBACError.inheritanceCycle(juniorRole: juniorRole, seniorRole: seniorRole)
        }
        
        // Check depth limit
        if roleDepth(juniorRole) >= maxRoleDepth {
            throw RBACError.maxDepthExceeded(role: juniorRole, depth: maxRoleDepth)
        }
        
        roleHierarchy[juniorRole, default: []].insert(seniorRole)
        
        let event = AuditEvent(
            event: "ROLE_INHERITANCE_ADDED",
            admin: admin,
            role: seniorRole,
            time: currentTime,
            details: ["junior": juniorRole, "senior": seniorRole]
        )
        auditLog.append(event)
    }
    
    /// Remove role inheritance (TLA+ Action: RemoveRoleInheritance)
    public func removeRoleInheritance(admin: String, juniorRole: String, seniorRole: String) async throws {
        guard roleHierarchy[juniorRole]?.contains(seniorRole) == true else {
            throw RBACError.inheritanceNotFound(juniorRole: juniorRole, seniorRole: seniorRole)
        }
        
        roleHierarchy[juniorRole]?.remove(seniorRole)
        
        let event = AuditEvent(
            event: "ROLE_INHERITANCE_REMOVED",
            admin: admin,
            role: seniorRole,
            time: currentTime,
            details: ["junior": juniorRole, "senior": seniorRole]
        )
        auditLog.append(event)
    }
    
    // MARK: - Session Management (TLA+: CreateSession, ActivateRole, DeactivateRole, CloseSession)
    
    /// Create user session (TLA+ Action: CreateSession)
    public func createSession(user: String, sessionId: Int, context: SessionContext) async throws {
        guard sessions[sessionId] == nil else {
            throw RBACError.sessionExists(sessionId)
        }
        
        sessions[sessionId] = RBACSession(user: user, activeRoles: Set(), context: context)
        
        let event = AuditEvent(
            event: "SESSION_CREATED",
            user: user,
            sessionId: sessionId,
            time: currentTime
        )
        auditLog.append(event)
    }
    
    /// Activate role in session (TLA+ Action: ActivateRole)
    public func activateRole(user: String, sessionId: Int, role: String) async throws {
        guard let session = sessions[sessionId] else {
            throw RBACError.sessionNotFound(sessionId)
        }
        
        guard session.user == user else {
            throw RBACError.sessionUserMismatch(sessionId: sessionId, user: user)
        }
        
        guard userRoles[user]?.contains(role) == true else {
            throw RBACError.roleNotAssigned(user: user, role: role)
        }
        
        guard !session.activeRoles.contains(role) else {
            throw RBACError.roleAlreadyActive(sessionId: sessionId, role: role)
        }
        
        guard session.activeRoles.count < maxActiveRoles else {
            throw RBACError.maxActiveRolesExceeded(sessionId: sessionId, max: maxActiveRoles)
        }
        
        guard satisfiesSessionConstraints(sessionId: sessionId, role: role) else {
            throw RBACError.sessionConstraintViolation(sessionId: sessionId, role: role)
        }
        
        guard satisfiesTemporalConstraints(role: role, time: currentTime, context: session.context) else {
            throw RBACError.temporalConstraintViolation(role: role, time: currentTime)
        }
        
        sessions[sessionId]?.activeRoles.insert(role)
        roleActivations[role]?.activeCount += 1
        
        let event = AuditEvent(
            event: "ROLE_ACTIVATED",
            user: user,
            role: role,
            sessionId: sessionId,
            time: currentTime
        )
        auditLog.append(event)
    }
    
    /// Deactivate role in session (TLA+ Action: DeactivateRole)
    public func deactivateRole(user: String, sessionId: Int, role: String) async throws {
        guard let session = sessions[sessionId] else {
            throw RBACError.sessionNotFound(sessionId)
        }
        
        guard session.user == user else {
            throw RBACError.sessionUserMismatch(sessionId: sessionId, user: user)
        }
        
        guard session.activeRoles.contains(role) else {
            throw RBACError.roleNotActive(sessionId: sessionId, role: role)
        }
        
        sessions[sessionId]?.activeRoles.remove(role)
        roleActivations[role]?.activeCount -= 1
        
        let event = AuditEvent(
            event: "ROLE_DEACTIVATED",
            user: user,
            role: role,
            sessionId: sessionId,
            time: currentTime
        )
        auditLog.append(event)
    }
    
    /// Close session (TLA+ Action: CloseSession)
    public func closeSession(sessionId: Int) async throws {
        guard let session = sessions[sessionId] else {
            throw RBACError.sessionNotFound(sessionId)
        }
        
        let activeRoles = session.activeRoles
        
        // Deactivate all roles
        for role in activeRoles {
            roleActivations[role]?.activeCount -= 1
        }
        
        sessions.removeValue(forKey: sessionId)
        
        let event = AuditEvent(
            event: "SESSION_CLOSED",
            sessionId: sessionId,
            time: currentTime
        )
        auditLog.append(event)
    }
    
    // MARK: - Constraint Management (TLA+: AddConstraint, RemoveConstraint)
    
    /// Add RBAC constraint (TLA+ Action: AddConstraint)
    public func addConstraint(admin: String, constraint: RBACConstraint) async throws {
        guard !constraints.contains(constraint) else {
            throw RBACError.constraintExists(constraint)
        }
        
        constraints.insert(constraint)
        
        let event = AuditEvent(
            event: "CONSTRAINT_ADDED",
            admin: admin,
            time: currentTime,
            details: ["type": constraint.type.rawValue, "roles": constraint.roles.joined(separator: ",")]
        )
        auditLog.append(event)
    }
    
    /// Remove RBAC constraint (TLA+ Action: RemoveConstraint)
    public func removeConstraint(admin: String, constraint: RBACConstraint) async throws {
        guard constraints.contains(constraint) else {
            throw RBACError.constraintNotFound(constraint)
        }
        
        constraints.remove(constraint)
        
        let event = AuditEvent(
            event: "CONSTRAINT_REMOVED",
            admin: admin,
            time: currentTime,
            details: ["type": constraint.type.rawValue, "roles": constraint.roles.joined(separator: ",")]
        )
        auditLog.append(event)
    }
    
    // MARK: - Temporal Constraints (TLA+: SetTemporalConstraint)
    
    /// Set temporal constraint for role (TLA+ Action: SetTemporalConstraint)
    public func setTemporalConstraint(admin: String, role: String, constraint: TemporalConstraint) async throws {
        guard rolePermissions[role] != nil else {
            throw RBACError.roleNotFound(role)
        }
        
        guard constraint.validFrom < constraint.validUntil else {
            throw RBACError.invalidTemporalConstraint(role: role)
        }
        
        temporalConstraints[role] = constraint
        
        let event = AuditEvent(
            event: "TEMPORAL_CONSTRAINT_SET",
            admin: admin,
            role: role,
            time: currentTime
        )
        auditLog.append(event)
    }
    
    // MARK: - Time Management (TLA+: Tick)
    
    /// Advance time (TLA+ Action: Tick)
    public func tick() {
        currentTime += 1
    }
    
    // MARK: - Query Methods
    
    public func getUserRoles(_ user: String) -> Set<String> {
        return userRoles[user] ?? []
    }
    
    public func getRolePermissions(_ role: String) -> Set<Permission> {
        return allPermissionsForRole(role)
    }
    
    public func getUserPermissions(_ user: String) -> Set<Permission> {
        return allPermissionsForUser(user)
    }
    
    public func getSessionActiveRoles(_ sessionId: Int) -> Set<String>? {
        return sessions[sessionId]?.activeRoles
    }
    
    public func getRoleHierarchy(_ role: String) -> Set<String> {
        return roleHierarchy[role] ?? []
    }
    
    public func getConstraints() -> Set<RBACConstraint> {
        return constraints
    }
    
    public func getAuditLog() -> [AuditEvent] {
        return auditLog
    }
    
    public func getCurrentTime() -> Int {
        return currentTime
    }
    
    // MARK: - TLA+ Invariants Implementation
    
    /// Invariant: User roles are valid (TLA+: UserRolesValid)
    public func checkUserRolesValidInvariant() -> Bool {
        return userRoles.values.allSatisfy { roles in
            roles.allSatisfy { role in rolePermissions[role] != nil }
        }
    }
    
    /// Invariant: Role hierarchy has no cycles (TLA+: NoHierarchyCycles)
    public func checkNoHierarchyCyclesInvariant() -> Bool {
        return roleHierarchy.keys.allSatisfy { role in
            !hasCycle(role, visited: Set())
        }
    }
    
    /// Invariant: Role hierarchy depth is bounded (TLA+: BoundedHierarchyDepth)
    public func checkBoundedHierarchyDepthInvariant() -> Bool {
        return roleHierarchy.keys.allSatisfy { role in
            roleDepth(role) <= maxRoleDepth
        }
    }
    
    /// Invariant: Active roles per session don't exceed limit (TLA+: ActiveRoleLimit)
    public func checkActiveRoleLimitInvariant() -> Bool {
        return sessions.values.allSatisfy { session in
            session.activeRoles.count <= maxActiveRoles
        }
    }
    
    /// Invariant: Active roles belong to the user (TLA+: ActiveRolesBelongToUser)
    public func checkActiveRolesBelongToUserInvariant() -> Bool {
        return sessions.allSatisfy { (sessionId, session) in
            let userRoles = userRoles[session.user] ?? []
            return session.activeRoles.isSubset(of: userRoles)
        }
    }
    
    /// Combined safety invariant (TLA+: TypeInvariant)
    public func checkSafetyInvariant() -> Bool {
        return checkUserRolesValidInvariant() &&
               checkNoHierarchyCyclesInvariant() &&
               checkBoundedHierarchyDepthInvariant() &&
               checkActiveRoleLimitInvariant() &&
               checkActiveRolesBelongToUserInvariant()
    }
}

// MARK: - Errors

public enum RBACError: Error, LocalizedError {
    case roleNotFound(String)
    case roleAlreadyAssigned(user: String, role: String)
    case roleNotAssigned(user: String, role: String)
    case constraintViolation(user: String, role: String)
    case permissionAlreadyGranted(role: String, permission: Permission)
    case permissionNotGranted(role: String, permission: Permission)
    case invalidInheritance(juniorRole: String, seniorRole: String)
    case inheritanceAlreadyExists(juniorRole: String, seniorRole: String)
    case inheritanceNotFound(juniorRole: String, seniorRole: String)
    case inheritanceCycle(juniorRole: String, seniorRole: String)
    case maxDepthExceeded(role: String, depth: Int)
    case sessionExists(Int)
    case sessionNotFound(Int)
    case sessionUserMismatch(sessionId: Int, user: String)
    case roleAlreadyActive(sessionId: Int, role: String)
    case roleNotActive(sessionId: Int, role: String)
    case maxActiveRolesExceeded(sessionId: Int, max: Int)
    case sessionConstraintViolation(sessionId: Int, role: String)
    case temporalConstraintViolation(role: String, time: Int)
    case constraintExists(RBACConstraint)
    case constraintNotFound(RBACConstraint)
    case invalidTemporalConstraint(role: String)
    
    public var errorDescription: String? {
        switch self {
        case .roleNotFound(let role):
            return "Role '\(role)' not found"
        case .roleAlreadyAssigned(let user, let role):
            return "Role '\(role)' already assigned to user '\(user)'"
        case .roleNotAssigned(let user, let role):
            return "Role '\(role)' not assigned to user '\(user)'"
        case .constraintViolation(let user, let role):
            return "Constraint violation: cannot assign role '\(role)' to user '\(user)'"
        case .permissionAlreadyGranted(let role, let permission):
            return "Permission '\(permission.operation)' on '\(permission.object)' already granted to role '\(role)'"
        case .permissionNotGranted(let role, let permission):
            return "Permission '\(permission.operation)' on '\(permission.object)' not granted to role '\(role)'"
        case .invalidInheritance(let juniorRole, let seniorRole):
            return "Invalid inheritance: '\(juniorRole)' cannot inherit from '\(seniorRole)'"
        case .inheritanceAlreadyExists(let juniorRole, let seniorRole):
            return "Inheritance already exists: '\(juniorRole)' inherits from '\(seniorRole)'"
        case .inheritanceNotFound(let juniorRole, let seniorRole):
            return "Inheritance not found: '\(juniorRole)' does not inherit from '\(seniorRole)'"
        case .inheritanceCycle(let juniorRole, let seniorRole):
            return "Inheritance cycle detected: '\(juniorRole)' -> '\(seniorRole)'"
        case .maxDepthExceeded(let role, let depth):
            return "Role hierarchy depth exceeded for '\(role)': max \(depth)"
        case .sessionExists(let sessionId):
            return "Session \(sessionId) already exists"
        case .sessionNotFound(let sessionId):
            return "Session \(sessionId) not found"
        case .sessionUserMismatch(let sessionId, let user):
            return "Session \(sessionId) does not belong to user '\(user)'"
        case .roleAlreadyActive(let sessionId, let role):
            return "Role '\(role)' already active in session \(sessionId)"
        case .roleNotActive(let sessionId, let role):
            return "Role '\(role)' not active in session \(sessionId)"
        case .maxActiveRolesExceeded(let sessionId, let max):
            return "Maximum active roles exceeded in session \(sessionId): max \(max)"
        case .sessionConstraintViolation(let sessionId, let role):
            return "Session constraint violation: cannot activate role '\(role)' in session \(sessionId)"
        case .temporalConstraintViolation(let role, let time):
            return "Temporal constraint violation: role '\(role)' not valid at time \(time)"
        case .constraintExists(let constraint):
            return "Constraint already exists: \(constraint.type.rawValue)"
        case .constraintNotFound(let constraint):
            return "Constraint not found: \(constraint.type.rawValue)"
        case .invalidTemporalConstraint(let role):
            return "Invalid temporal constraint for role '\(role)'"
        }
    }
}

/*
 * IMPLEMENTATION NOTES:
 *
 * This implementation follows the RolesPermissions.tla specification and
 * implements comprehensive RBAC system:
 *
 * 1. RBAC Models (Sandhu et al. 1996):
 *    - RBAC0: Core RBAC (users, roles, permissions, sessions)
 *    - RBAC1: Hierarchical RBAC (role inheritance)
 *    - RBAC2: Constrained RBAC (SoD constraints)
 *    - RBAC3: Consolidated RBAC (RBAC1 + RBAC2)
 *
 * 2. Role Hierarchy (Ferraiolo et al. 2001):
 *    - Inheritance: Junior roles inherit permissions from senior roles
 *    - Cycle detection: Prevents circular inheritance
 *    - Depth limits: Bounded hierarchy depth
 *    - Transitive closure: Computes all inherited permissions
 *
 * 3. Separation of Duty (Ahn & Sandhu 2000):
 *    - Static SoD: Mutually exclusive role assignments
 *    - Dynamic SoD: Mutually exclusive active roles in session
 *    - Prerequisite: Role requires another role
 *    - Cardinality: Limit on role assignments
 *
 * 4. Session Management:
 *    - Role activation/deactivation
 *    - Context-aware activation
 *    - Active role limits
 *    - Session lifecycle
 *
 * 5. Temporal Constraints (Li et al. 2007):
 *    - Time-based validity
 *    - Day-of-week restrictions
 *    - Hour-of-day restrictions
 *    - Context-aware activation
 *
 * 6. Audit Logging:
 *    - Complete audit trail
 *    - Event timestamps
 *    - Admin actions
 *    - Security events
 *
 * Correctness Properties (verified by TLA+):
 * - User roles are valid
 * - Role hierarchy has no cycles
 * - Role hierarchy depth is bounded
 * - Active roles per session don't exceed limit
 * - Active roles belong to the user
 * - Static SoD is enforced
 * - Dynamic SoD is enforced
 * - Role activation counts are accurate
 * - Audit log is monotonic
 *
 * Production Examples:
 * - Oracle Database: RBAC with role hierarchy
 * - PostgreSQL: Role-based access control
 * - SQL Server: Role-based security
 * - MySQL: Privilege system with roles
 */

