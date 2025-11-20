//
//  PrivilegeManager.swift
//  GRANT/REVOKE privilege management using sys_privileges
//

import Foundation

/// Privilege type (SQL-standard)
public enum PrivilegeType: String, Codable, Sendable {
    case select = "SELECT"
    case insert = "INSERT"
    case update = "UPDATE"
    case delete = "DELETE"
    case usage = "USAGE"
    case execute = "EXECUTE"
    case alter = "ALTER"
    case create = "CREATE"
    case drop = "DROP"
    case grant = "GRANT"
}

/// Object type for privileges
public enum PrivilegeObjectType: String, Codable, Sendable {
    case database = "DATABASE"
    case schema = "SCHEMA"
    case table = "TABLE"
    case column = "COLUMN"
    case view = "VIEW"
    case sequence = "SEQUENCE"
    case index = "INDEX"
}

/// Grantee kind (USER or ROLE)
public enum GranteeKind: String, Codable, Sendable {
    case user = "USER"
    case role = "ROLE"
}

/// Privilege manager: handles GRANT/REVOKE operations using sys_privileges
public actor PrivilegeManager {
    private let db: ColibrìDB
    private let schema = "colibri_sys"
    
    // In-memory privilege cache
    private struct PrivilegeKey: Hashable, Sendable {
        let granteeKind: GranteeKind
        let granteeId: Int64
        let objectType: PrivilegeObjectType
        let objectId: Int64
        let privilegeType: PrivilegeType
    }
    private var privileges: Set<PrivilegeKey> = []
    private var grantOptions: [PrivilegeKey: Bool] = [:]
    
    // Role membership cache (for transitive privilege resolution)
    private var roleMembers: [Int64: Set<Int64>] = [:] // role_id -> set of member_role_ids
    
    public init(database: ColibrìDB) {
        self.db = database
    }
    
    /// Load all privileges and role memberships from sys_* tables at startup
    public func loadAll() async throws {
        let tx = try await db.beginTransaction()
        defer { Task { try? await db.abort(txId: tx) } }
        
        try await loadPrivileges(txId: tx)
        try await loadRoleMembers(txId: tx)
    }
    
    // MARK: - Loading
    
    private func loadPrivileges(txId: TxID) async throws {
        let sql = "SELECT grantee_kind, grantee_id, object_type, object_id, privilege_type, grant_option FROM \(schema).sys_privileges;"
        let result = try await db.executeQuery(sql, txId: txId)
        
        for row in result.rows {
            guard
                let granteeKindStr = extractString(row["grantee_kind"]),
                let granteeKind = GranteeKind(rawValue: granteeKindStr),
                let granteeId = extractInt64(row["grantee_id"]),
                let objectTypeStr = extractString(row["object_type"]),
                let objectType = PrivilegeObjectType(rawValue: objectTypeStr),
                let objectId = extractInt64(row["object_id"]),
                let privilegeTypeStr = extractString(row["privilege_type"]),
                let privilegeType = PrivilegeType(rawValue: privilegeTypeStr),
                let grantOption = extractBool(row["grant_option"])
            else { continue }
            
            let key = PrivilegeKey(granteeKind: granteeKind, granteeId: granteeId, objectType: objectType, objectId: objectId, privilegeType: privilegeType)
            privileges.insert(key)
            grantOptions[key] = grantOption != 0
        }
    }
    
    private func loadRoleMembers(txId: TxID) async throws {
        let sql = "SELECT role_id, member_role_id FROM \(schema).sys_role_members;"
        let result = try await db.executeQuery(sql, txId: txId)
        
        for row in result.rows {
            guard
                let roleId = extractInt64(row["role_id"]),
                let memberRoleId = extractInt64(row["member_role_id"])
            else { continue }
            
            roleMembers[roleId, default: []].insert(memberRoleId)
        }
    }
    
    // MARK: - GRANT Operations
    
    /// Grant a privilege to a user or role
    public func grant(
        privilege: PrivilegeType,
        on objectType: PrivilegeObjectType,
        objectId: Int64,
        to granteeKind: GranteeKind,
        granteeId: Int64,
        grantorId: Int64,
        withGrantOption: Bool = false
    ) async throws {
        let tx = try await db.beginTransaction()
        do {
            // Insert or update privilege in sys_privileges
            let sql = """
            INSERT INTO \(schema).sys_privileges (privilege_id, grantee_kind, grantee_id, object_type, object_id, privilege_type, grantor_id, grant_option)
            VALUES ((SELECT COALESCE(MAX(privilege_id), 0) + 1 FROM \(schema).sys_privileges), '\(granteeKind.rawValue)', \(granteeId), '\(objectType.rawValue)', \(objectId), '\(privilege.rawValue)', \(grantorId), \(withGrantOption ? 1 : 0))
            ON CONFLICT (grantee_kind, grantee_id, object_type, object_id, privilege_type)
            DO UPDATE SET grant_option = EXCLUDED.grant_option, grantor_id = EXCLUDED.grantor_id;
            """
            
            _ = try await db.executeQuery(sql, txId: tx)
            try await db.commit(txId: tx)
            
            // Update cache
            let key = PrivilegeKey(granteeKind: granteeKind, granteeId: granteeId, objectType: objectType, objectId: objectId, privilegeType: privilege)
            privileges.insert(key)
            grantOptions[key] = withGrantOption
        } catch {
            try? await db.abort(txId: tx)
            throw error
        }
    }
    
    /// Revoke a privilege from a user or role
    public func revoke(
        privilege: PrivilegeType,
        on objectType: PrivilegeObjectType,
        objectId: Int64,
        from granteeKind: GranteeKind,
        granteeId: Int64,
        cascade: Bool = false
    ) async throws {
        let tx = try await db.beginTransaction()
        do {
            var sql = """
            DELETE FROM \(schema).sys_privileges
            WHERE grantee_kind = '\(granteeKind.rawValue)' AND grantee_id = \(granteeId)
            AND object_type = '\(objectType.rawValue)' AND object_id = \(objectId)
            AND privilege_type = '\(privilege.rawValue)';
            """
            
            if cascade {
                // Cascade revoke: also revoke from all grantees who received this privilege via GRANT OPTION
                sql += """
                DELETE FROM \(schema).sys_privileges
                WHERE grantor_id IN (
                    SELECT user_id FROM \(schema).sys_users WHERE username IN (
                        SELECT username FROM \(schema).sys_users WHERE user_id = \(granteeId)
                    )
                ) AND object_type = '\(objectType.rawValue)' AND object_id = \(objectId)
                AND privilege_type = '\(privilege.rawValue)';
                """
            }
            
            _ = try await db.executeQuery(sql, txId: tx)
            try await db.commit(txId: tx)
            
            // Update cache
            let key = PrivilegeKey(granteeKind: granteeKind, granteeId: granteeId, objectType: objectType, objectId: objectId, privilegeType: privilege)
            privileges.remove(key)
            grantOptions.removeValue(forKey: key)
        } catch {
            try? await db.abort(txId: tx)
            throw error
        }
    }
    
    // MARK: - Permission Checking
    
    /// Check if a user/role has a specific privilege on an object
    /// Resolves role memberships transitively
    public func hasPrivilege(
        userId: Int64,
        roles: [Int64], // Direct roles for the user
        privilege: PrivilegeType,
        on objectType: PrivilegeObjectType,
        objectId: Int64
    ) -> Bool {
        // Check direct user privilege
        let userKey = PrivilegeKey(granteeKind: .user, granteeId: userId, objectType: objectType, objectId: objectId, privilegeType: privilege)
        if privileges.contains(userKey) {
            return true
        }
        
        // Check role privileges (with transitive closure)
        let effectiveRoles = computeRoleClosure(roles)
        for roleId in effectiveRoles {
            let roleKey = PrivilegeKey(granteeKind: .role, granteeId: roleId, objectType: objectType, objectId: objectId, privilegeType: privilege)
            if privileges.contains(roleKey) {
                return true
            }
        }
        
        return false
    }
    
    /// Check if a user can grant a privilege (has GRANT OPTION)
    public func canGrant(
        userId: Int64,
        roles: [Int64],
        privilege: PrivilegeType,
        on objectType: PrivilegeObjectType,
        objectId: Int64
    ) -> Bool {
        let userKey = PrivilegeKey(granteeKind: .user, granteeId: userId, objectType: objectType, objectId: objectId, privilegeType: privilege)
        if privileges.contains(userKey), grantOptions[userKey] == true {
            return true
        }
        
        let effectiveRoles = computeRoleClosure(roles)
        for roleId in effectiveRoles {
            let roleKey = PrivilegeKey(granteeKind: .role, granteeId: roleId, objectType: objectType, objectId: objectId, privilegeType: privilege)
            if privileges.contains(roleKey), grantOptions[roleKey] == true {
                return true
            }
        }
        
        return false
    }
    
    /// Compute transitive closure of role memberships
    private func computeRoleClosure(_ initialRoles: [Int64]) -> Set<Int64> {
        var closure: Set<Int64> = Set(initialRoles)
        var queue = initialRoles
        
        while !queue.isEmpty {
            let roleId = queue.removeFirst()
            if let members = roleMembers[roleId] {
                for memberId in members {
                    if !closure.contains(memberId) {
                        closure.insert(memberId)
                        queue.append(memberId)
                    }
                }
            }
        }
        
        return closure
    }
    
    // MARK: - Helper Extractors
    
    private func extractInt64(_ value: Value?) -> Int64? {
        guard let v = value, case .int(let i) = v else { return nil }
        return i
    }
    
    private func extractString(_ value: Value?) -> String? {
        guard let v = value, case .string(let s) = v else { return nil }
        return s
    }
    
    private func extractBool(_ value: Value?) -> Int? {
        guard let v = value, case .bool(let b) = v else {
            if let i = extractInt64(value) { return Int(i) }
            return nil
        }
        return b ? 1 : 0
    }
    
    private func extractInt(_ value: Value?) -> Int? {
        guard let i64 = extractInt64(value) else { return nil }
        return Int(i64)
    }
}

