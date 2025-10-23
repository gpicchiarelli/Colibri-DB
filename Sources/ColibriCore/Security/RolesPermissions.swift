//
//  RolesPermissions.swift
//  Based on: spec/RolesPermissions.tla
//

import Foundation

/// Permission types for database operations
public enum Permission: String, Codable, Sendable, CaseIterable {
    case all = "all"
    case select = "select"
    case insert = "insert"
    case update = "update"
    case delete = "delete"
    case create = "create"
    case drop = "drop"
    case alter = "alter"
    case index = "index"
    case execute = "execute"
}

public struct Role {
    public let name: String
    public let permissions: Set<Permission>
    public let inheritsFrom: [String]
    
    public init(name: String, permissions: Set<Permission>, inheritsFrom: [String] = []) {
        self.name = name
        self.permissions = permissions
        self.inheritsFrom = inheritsFrom
    }
}

public actor RoleManager {
    private var roles: [String: Role] = [:]
    private var userRoles: [String: Set<String>] = [:]
    
    public init() {
        Task {
            await initializeBuiltinRoles()
        }
    }
    
    private func initializeBuiltinRoles() {
        roles["admin"] = Role(
            name: "admin",
            permissions: [.all],
            inheritsFrom: []
        )
        
        roles["readwrite"] = Role(
            name: "readwrite",
            permissions: [.select, .insert, .update, .delete],
            inheritsFrom: []
        )
        
        roles["readonly"] = Role(
            name: "readonly",
            permissions: [.select],
            inheritsFrom: []
        )
    }
    
    public func createRole(_ role: Role) throws {
        guard roles[role.name] == nil else {
            throw DBError.duplicate
        }
        roles[role.name] = role
    }
    
    public func dropRole(name: String) throws {
        guard roles[name] != nil else {
            throw DBError.notFound
        }
        roles[name] = nil
    }
    
    public func grantRole(roleName: String, toUser username: String) throws {
        guard roles[roleName] != nil else {
            throw DBError.notFound
        }
        userRoles[username, default: []].insert(roleName)
    }
    
    public func revokeRole(roleName: String, fromUser username: String) {
        userRoles[username]?.remove(roleName)
    }
    
    public func getUserPermissions(username: String) -> Set<Permission> {
        var permissions: Set<Permission> = []
        
        guard let userRoleSet = userRoles[username] else {
            return permissions
        }
        
        for roleName in userRoleSet {
            if let role = roles[roleName] {
                permissions.formUnion(role.permissions)
                
                for inheritedRoleName in role.inheritsFrom {
                    if let inheritedRole = roles[inheritedRoleName] {
                        permissions.formUnion(inheritedRole.permissions)
                    }
                }
            }
        }
        
        return permissions
    }
    
    public func getUserRoles(username: String) -> Set<String> {
        return userRoles[username] ?? []
    }
    
    public func listRoles() -> [String] {
        return Array(roles.keys)
    }
}

