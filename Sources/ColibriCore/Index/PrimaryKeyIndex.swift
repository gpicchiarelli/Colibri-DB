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
    // MARK: - Properties
    
    private let column: String
    private var ridByValue: [Value: RID] = [:]
    
    // MARK: - Initialization
    
    /// Initialize primary key index
    /// - Parameter column: Column name for the primary key
    public init(column: String) {
        self.column = column
    }
    
    // MARK: - Public Methods
    
    /// Upsert a value-RID mapping
    /// - Parameters:
    ///   - value: Primary key value
    ///   - rid: Record ID
    public func upsert(value: Value, rid: RID) {
        ridByValue[value] = rid
    }
    
    /// Remove a value-RID mapping
    /// - Parameter value: Primary key value to remove
    public func remove(value: Value) {
        ridByValue.removeValue(forKey: value)
    }
    
    /// Lookup RID for a value
    /// - Parameter value: Primary key value to lookup
    /// - Returns: Record ID if found, nil otherwise
    public func lookup(value: Value) -> RID? {
        return ridByValue[value]
    }
    
    /// Get the tracked column name
    /// - Returns: Column name
    public func trackedColumn() -> String {
        return column
    }
}

