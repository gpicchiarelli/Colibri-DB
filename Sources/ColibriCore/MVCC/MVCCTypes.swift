//
//  MVCCTypes.swift
//  ColibrìDB MVCC Types
//
//  Based on: spec/MVCC.tla
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//

import Foundation

// MARK: - Version Structure

/// Version structure with full MVCC metadata
/// Corresponds to TLA+: Version
/// Based on: "A Critique of ANSI SQL Isolation Levels" (Berenson et al., 1995)
public struct Version: Codable, Sendable {
    /// The actual data value
    public let value: Value
    
    /// Transaction that created this version
    public let beginTx: TxID
    
    /// Transaction that deleted/updated this version (0 = active)
    public var endTx: TxID
    
    /// Commit timestamp when version became visible
    public var beginTS: Timestamp
    
    /// Commit timestamp when version became invisible (0 = still visible)
    public var endTS: Timestamp
    
    /// Original creator transaction (for conflict detection)
    public let createdBy: TxID
    
    /// Deleter/updater transaction (0 = not deleted)
    public var deletedBy: TxID
    
    public init(
        value: Value,
        beginTx: TxID,
        endTx: TxID = 0,
        beginTS: Timestamp = 0,
        endTS: Timestamp = 0,
        createdBy: TxID,
        deletedBy: TxID = 0
    ) {
        self.value = value
        self.beginTx = beginTx
        self.endTx = endTx
        self.beginTS = beginTS
        self.endTS = endTS
        self.createdBy = createdBy
        self.deletedBy = deletedBy
    }
}

// MARK: - Snapshot Structure

/// Snapshot for transaction isolation
/// Corresponds to TLA+: Snapshot
/// Implements Snapshot Isolation (SI)
public struct Snapshot: Codable, Sendable {
    /// Transaction ID owning this snapshot
    public let txID: TxID
    
    /// Transaction start timestamp
    public let startTS: Timestamp
    
    /// Oldest transaction that was active at start
    public let xmin: Timestamp
    
    /// Next transaction ID at snapshot time
    public let xmax: Timestamp
    
    /// Set of transactions active when snapshot was taken
    public let activeTxAtStart: Set<TxID>
    
    public init(
        txID: TxID,
        startTS: Timestamp,
        xmin: Timestamp,
        xmax: Timestamp,
        activeTxAtStart: Set<TxID>
    ) {
        self.txID = txID
        self.startTS = startTS
        self.xmin = xmin
        self.xmax = xmax
        self.activeTxAtStart = activeTxAtStart
    }
}

// MARK: - Version Chain

/// Version chain for a key
/// Maintains all versions of a value, ordered by creation time
public struct VersionChain: Sendable {
    private var versions: [Version]
    
    public init() {
        self.versions = []
    }
    
    public mutating func append(_ version: Version) {
        versions.append(version)
    }
    
    public func getVersions() -> [Version] {
        return versions
    }
    
    public func isEmpty() -> Bool {
        return versions.isEmpty
    }
    
    public func count() -> Int {
        return versions.count
    }
    
    public subscript(index: Int) -> Version {
        get { versions[index] }
        set { versions[index] = newValue }
    }
}

// MARK: - Transaction Metadata

/// Metadata for an active transaction
public struct TransactionMetadata: Sendable {
    public let txID: TxID
    public let isolationLevel: IsolationLevel
    public var status: TransactionStatus
    public var snapshot: Snapshot?
    public var readSet: Set<String>
    public var writeSet: Set<String>
    public var startTime: Date
    
    public init(
        txID: TxID,
        isolationLevel: IsolationLevel,
        status: TransactionStatus = .active
    ) {
        self.txID = txID
        self.isolationLevel = isolationLevel
        self.status = status
        self.snapshot = nil
        self.readSet = []
        self.writeSet = []
        self.startTime = Date()
    }
}

