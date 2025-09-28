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
    private struct Entry { var row: Row; var isTombstone: Bool }
    private var rows: [RID: Entry] = [:]
    private var nextPage: UInt64 = 1

    public init() {}

    @discardableResult
    public mutating func insert(_ row: Row) throws -> RID {
        let rid = RID(pageId: nextPage, slotId: 1)
        rows[rid] = Entry(row: row, isTombstone: false)
        nextPage += 1
        return rid
    }

    public func scan() throws -> AnySequence<(RID, Row)> {
        let iterator = rows.makeIterator()
        var currentIterator = iterator
        return AnySequence(AnyIterator {
            while let next = currentIterator.next() {
                let (rid, entry) = next
                guard !entry.isTombstone else { continue }
                return (rid, entry.row)
            }
            return nil
        })
    }

    public func scan(includeTombstones: Bool) throws -> AnySequence<(RID, Row)> {
        let iterator = rows.makeIterator()
        var currentIterator = iterator
        return AnySequence(AnyIterator {
            while let next = currentIterator.next() {
                let (rid, entry) = next
                if !includeTombstones && entry.isTombstone { continue }
                return (rid, entry.row)
            }
            return nil
        })
    }

    public func read(_ rid: RID) throws -> Row {
        guard let entry = rows[rid], !entry.isTombstone else { throw DBError.notFound("RID \(rid)") }
        return entry.row
    }

    public mutating func update(_ rid: RID, _ newRow: Row) throws {
        guard var entry = rows[rid], !entry.isTombstone else { throw DBError.notFound("RID \(rid)") }
        entry.row = newRow
        rows[rid] = entry
    }

    public mutating func remove(_ rid: RID) {
        rows[rid]?.isTombstone = true
    }
    
    public mutating func restore(_ rid: RID, row: Row) {
        rows[rid] = Entry(row: row, isTombstone: false)
    }

    public mutating func clearTombstone(_ rid: RID) {
        rows[rid]?.isTombstone = false
    }

    public mutating func register(row: Row, rid: RID, isTombstone: Bool = false) {
        rows[rid] = Entry(row: row, isTombstone: isTombstone)
    }
}

