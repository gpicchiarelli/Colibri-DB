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

    public func scan(includeTombstones: Bool = false) throws -> AnySequence<(RID, Row?, Bool)> {
        let keys = rows.keys.sorted { lhs, rhs in
            if lhs.pageId == rhs.pageId { return lhs.slotId < rhs.slotId }
            return lhs.pageId < rhs.pageId
        }
        var index = 0
        let iterator = AnyIterator<(RID, Row?, Bool)> {
            while index < keys.count {
                let rid = keys[index]
                index += 1
                guard let entry = rows[rid] else { continue }
                if !includeTombstones && entry.isTombstone { continue }
                return (rid, entry.isTombstone ? nil : entry.row, entry.isTombstone)
            }
            return nil
        }
        return AnySequence(iterator)
    }

    public func scan() throws -> AnySequence<(RID, Row)> {
        var iterator = try scan(includeTombstones: false).makeIterator()
        return AnySequence(AnyIterator {
            while let next = iterator.next() {
                let (rid, row, _) = next
                if let row = row { return (rid, row) }
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

    public mutating func remove(_ rid: RID) throws {
        guard var entry = rows[rid] else { throw DBError.notFound("RID \(rid)") }
        entry.isTombstone = true
        rows[rid] = entry
    }

    public mutating func restore(_ rid: RID, row: Row) {
        rows[rid] = Entry(row: row, isTombstone: false)
    }
}

