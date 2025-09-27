//
//  HeapTable.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: In-memory heap caretaker for lightweight table experiments.

import Foundation
/// In-memory heap table for testing and in-memory storage engine.

public struct HeapTable: TableStorageProtocol {
    private var rows: [RID: Row] = [:]
    private var nextPage: UInt64 = 1
    private var nextSlot: UInt16 = 1

    public init() {}

    private mutating func nextRID() -> RID {
        // Naive RID allocation (no paging). For MVP/testing only.
        let rid = RID(pageId: nextPage, slotId: nextSlot)
        if nextSlot == UInt16.max { nextSlot = 1; nextPage += 1 } else { nextSlot &+= 1 }
        return rid
    }

    /// Inserts a row and returns its RID.
    @discardableResult
    public mutating func insert(_ row: Row) throws -> RID {
        let rid = nextRID()
        rows[rid] = row
        return rid
    }

    /// Returns a sequence of all (RID, Row) pairs.
    public func scan() throws -> AnySequence<(RID, Row)> {
        AnySequence(rows.map { ($0.key, $0.value) })
    }

    /// Reads a row by RID.
    public func read(_ rid: RID) throws -> Row {
        guard let r = rows[rid] else { throw DBError.notFound("RID \(rid)") }
        return r
    }

    /// Updates a row by RID.
    public mutating func update(_ rid: RID, _ newRow: Row) throws {
        guard rows[rid] != nil else { throw DBError.notFound("RID \(rid)") }
        rows[rid] = newRow
    }

    /// Removes a row by RID.
    public mutating func remove(_ rid: RID) throws {
        rows.removeValue(forKey: rid)
    }

    /// Restores a previously removed row into its original RID (used during rollback).
    public mutating func restore(_ rid: RID, row: Row) {
        rows[rid] = row
    }
}

