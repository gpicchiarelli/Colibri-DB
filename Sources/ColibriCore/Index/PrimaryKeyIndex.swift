//
//  PrimaryKeyIndex.swift
//  ColibrìDB
//
//  Lightweight primary-key index powered by Value -> RID map.
//  Follows classic literature (e.g. System R) where the primary key lookup
//  is kept in-memory and updated atomically alongside heap mutations so
//  point reads can bypass full table scans.
//

import Foundation

/// Actor-backed primary key index for point lookups.
public actor PrimaryKeyIndex {
    private let column: String
    private var ridByValue: [Value: RID] = [:]
    
    public init(column: String) {
        self.column = column
    }
    
    public func upsert(value: Value, rid: RID) {
        ridByValue[value] = rid
    }
    
    public func remove(value: Value) {
        ridByValue.removeValue(forKey: value)
    }
    
    public func lookup(value: Value) -> RID? {
        return ridByValue[value]
    }
    
    public func trackedColumn() -> String {
        return column
    }
}

