//
//  Locking.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrDB — BSD 3-Clause License

// Theme: Locking geometry defining resources, handles, and queues.

import Foundation

/// Identifies logical resources that can be locked by the transaction/lock manager.
public enum LockTarget: Hashable, CustomStringConvertible, Sendable {
    case table(String)
    case row(table: String, rid: RID)
    case index(table: String, name: String)
    case catalog(String)
    case ddl(String)
    case custom(String)

    public var description: String {
        switch self {
        case .table(let name): return "table:\(name)"
        case .row(let table, let rid): return "row:\(table)#\(rid.pageId):\(rid.slotId)"
        case .index(let table, let name): return "index:\(table).\(name)"
        case .catalog(let name): return "catalog:\(name)"
        case .ddl(let name): return "ddl:\(name)"
        case .custom(let name): return name
        }
    }
}

/// Opaque handle returned when acquiring a lock; required to release the lock explicitly.
public struct LockHandle: Hashable, Sendable {
    public let resource: LockTarget
    public let tid: UInt64
    public let mode: LockMode

    public init(resource: LockTarget, tid: UInt64, mode: LockMode) {
        self.resource = resource
        self.tid = tid
        self.mode = mode
    }
}

