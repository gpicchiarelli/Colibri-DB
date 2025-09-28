//
//  Protocols.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Protocol compass defining shared storage and index contracts.

import Foundation
/// Core protocols defining pluggable components (indexes, storage, WAL, buffers),
/// as well as policy and optimization interfaces used by ColibrDB.

// MARK: - Index

/// Generic index protocol supporting insert, equality and range queries.
public protocol IndexProtocol {
    associatedtype Key: Hashable & Comparable
    associatedtype Ref
    mutating func insert(_ key: Key, _ ref: Ref) throws
    func searchEquals(_ key: Key) throws -> [Ref]
    func range(_ lo: Key?, _ hi: Key?) throws -> [Ref]
    mutating func remove(_ key: Key, _ ref: Ref) throws
}

// MARK: - Table Storage

/// Abstract heap/table storage interface.
public protocol TableStorageProtocol {
    @discardableResult
    mutating func insert(_ row: Row) throws -> RID
    func scan() throws -> AnySequence<(RID, Row)>
    func read(_ rid: RID) throws -> Row
    mutating func update(_ rid: RID, _ newRow: Row) throws
    mutating func remove(_ rid: RID) throws
}

// MARK: - Storage Engine

/// Storage engine abstraction that manages tables and paging.
public protocol StorageEngineProtocol {
    var pageSize: Int { get }
    mutating func open(dataDir: String) throws
    mutating func createTable(_ name: String) throws
    func table(_ name: String) throws -> TableStorageProtocol
}

// MARK: - WAL

/// Write‑ahead logging abstraction; returns LSNs for appended records.
public protocol WALProtocol {
    mutating func append(record: Data) throws -> UInt64 // returns LSN
    func flush(upTo lsn: UInt64) throws
}

// MARK: - Buffer Pool

/// Buffer pool abstraction for paging in/out fixed‑size pages.
public protocol BufferPoolProtocol {
    var sizeBytes: UInt64 { get }
    func getPage(_ id: PageID) throws -> Data
    func putPage(_ id: PageID, data: Data, dirty: Bool) throws
}

// MARK: - Transactions & Locks

/// Transaction manager operations for begin/commit/rollback.
public protocol TransactionManagerProtocol {
    func begin() throws -> UInt64
    func commit(_ tid: UInt64) throws
    func rollback(_ tid: UInt64) throws
}

public enum LockMode { case shared, exclusive }

/// Lock manager abstraction with shared/exclusive modes.
public protocol LockManagerProtocol {
    @discardableResult
    func lock(_ resource: LockTarget, mode: LockMode, tid: UInt64, timeout: TimeInterval?) throws -> LockHandle
    func unlock(_ handle: LockHandle)
    func unlockAll(for tid: UInt64)
}

// MARK: - Policy & Optimization (Clustering)

public enum PolicyKind: String, Codable { case timeWindow, loadThreshold, usageBased, fragmentation }

/// Optimization/maintenance policy definition.
public struct Policy: Codable, Identifiable {
    public var id: UUID = UUID()
    public var kind: PolicyKind
    public var table: String
    public var columns: [String]
    public var params: [String: String]
    public init(kind: PolicyKind, table: String, columns: [String] = [], params: [String: String] = [:]) {
        self.kind = kind
        self.table = table
        self.columns = columns
        self.params = params
    }
}

public protocol PolicyStoreProtocol {
    func list() -> [Policy]
    mutating func add(_ policy: Policy)
    mutating func remove(id: UUID) -> Bool
}

/// Estimate returned by the optimization simulator.
public struct OptimizationEstimate: CustomStringConvertible {
    public let estimatedSeconds: Double
    public let tempSpaceBytes: UInt64
    public let expectedBenefit: Double // 0..1
    public var description: String {
        let sec = String(format: "%.1f", estimatedSeconds)
        return "time=\(sec)s temp=\(tempSpaceBytes)B benefit=\(Int(expectedBenefit * 100))%"
    }
}

/// Optimization simulator abstraction for estimating index/cluster plans.
public protocol OptimizationSimulatorProtocol {
    func estimate(table: String, columns: [String], tableStats: TableStatistics?) -> OptimizationEstimate
}

