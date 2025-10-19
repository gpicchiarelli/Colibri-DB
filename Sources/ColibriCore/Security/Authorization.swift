//
//  Authorization.swift
//  Based on: spec/Authorization.tla
//

import Foundation

public enum Permission {
    case select, insert, update, delete
    case create, drop, alter
    case grant, revoke
    case all
}

public enum ResourceType {
    case table(String)
    case database(String)
    case system
}

public struct AccessControlEntry {
    public let principal: String
    public let resource: ResourceType
    public let permissions: Set<Permission>
    public let grantedBy: String
    public let grantedAt: Date
    
    public init(principal: String, resource: ResourceType, permissions: Set<Permission>, grantedBy: String) {
        self.principal = principal
        self.resource = resource
        self.permissions = permissions
        self.grantedBy = grantedBy
        self.grantedAt = Date()
    }
}

public actor AuthorizationManager {
    private var acl: [AccessControlEntry] = []
    private let superusers: Set<String> = ["admin"]
    
    public init() {}
    
    public func grant(principal: String, resource: ResourceType, permissions: Set<Permission>, grantedBy: String) {
        let entry = AccessControlEntry(
            principal: principal,
            resource: resource,
            permissions: permissions,
            grantedBy: grantedBy
        )
        acl.append(entry)
    }
    
    public func revoke(principal: String, resource: ResourceType, permissions: Set<Permission>) {
        acl.removeAll { entry in
            entry.principal == principal &&
            resourceMatches(entry.resource, resource) &&
            !entry.permissions.isDisjoint(with: permissions)
        }
    }
    
    public func checkPermission(principal: String, resource: ResourceType, permission: Permission) -> Bool {
        if superusers.contains(principal) {
            return true
        }
        
        for entry in acl {
            if entry.principal == principal &&
               resourceMatches(entry.resource, resource) &&
               (entry.permissions.contains(permission) || entry.permissions.contains(.all)) {
                return true
            }
        }
        
        return false
    }
    
    public func getPermissions(principal: String, resource: ResourceType) -> Set<Permission> {
        if superusers.contains(principal) {
            return [.all]
        }
        
        var permissions: Set<Permission> = []
        
        for entry in acl {
            if entry.principal == principal && resourceMatches(entry.resource, resource) {
                permissions.formUnion(entry.permissions)
            }
        }
        
        return permissions
    }
    
    private func resourceMatches(_ entryResource: ResourceType, _ requestedResource: ResourceType) -> Bool {
        switch (entryResource, requestedResource) {
        case (.system, _):
            return true
        case (.database(let db1), .database(let db2)):
            return db1 == db2
        case (.database(let db1), .table(let table)):
            return table.hasPrefix(db1 + ".")
        case (.table(let t1), .table(let t2)):
            return t1 == t2
        default:
            return false
        }
    }
}

