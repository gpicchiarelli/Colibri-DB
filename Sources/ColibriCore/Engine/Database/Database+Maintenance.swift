//
//  Database+Maintenance.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Maintenance lounge scheduling vacuum and compaction routines.

import Foundation
// MARK: - Maintenance

extension Database {
    /// Compacts heap storage: either a specific page or the entire table.
    public func compactTable(table: String, pageId: UInt64?) throws -> String {
        if let ft = tablesFile[table] {
            if let pid = pageId {
                let g = try ft.compactPage(pid)
                return "compacted page=\(pid) gained=\(g)B"
            } else {
                let (pages, gained) = try ft.compactAllPages()
                return "compacted pages=\(pages) gained=\(gained)B"
            }
        }
        return "(table not persisted or not found)"
    }

    /// Flushes a table's buffer pool to disk.
    public func flushTable(_ table: String, fullSync: Bool = false) throws {
        Signpost.event(.flush, name: "DBFlushTable", message: "\(table) full=\(fullSync ? 1 : 0)")
        if let ft = tablesFile[table] { try ft.flush(fullSync: fullSync) }
    }

    /// Flushes all table and index buffers to disk.
    public func flushAll(fullSync: Bool = false) {
        let span = Signpost.begin(.flush, name: "DBFlushAll", message: fullSync ? "fullsync" : "fsync")
        var flushedTables = 0
        var flushedIndexes = 0
        defer {
            Signpost.end(span, message: "tables=\(flushedTables) indexes=\(flushedIndexes)")
        }
        for (_, ft) in tablesFile {
            try? ft.flush(fullSync: fullSync)
            flushedTables &+= 1
        }
        for (_, tableMap) in indexes {
            for (_, def) in tableMap {
                if case .persistentBTree(let f) = def.backend {
                    try? f.flushBuffers(fullSync: fullSync)
                    flushedIndexes &+= 1
                }
            }
        }
    }
}
