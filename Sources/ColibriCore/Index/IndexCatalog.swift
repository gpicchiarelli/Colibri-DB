//
//  IndexCatalog.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Index registry cataloging logical and physical descriptors.

import Foundation
/// Persistent catalog of logical index definitions per table.

public struct IndexDef: Codable, Equatable {
    public let name: String
    public let table: String
    public let column: String? // legacy single-column
    public let columns: [String]? // preferred multi-column
    public let kind: String // Hash | ART | BTree
}

public final class IndexCatalog {
    private let path: String
    private var defs: [IndexDef] = []

    /// Opens/creates an index catalog stored under the provided directory.
    public init(dir: String) throws {
        self.path = URL(fileURLWithPath: dir).appendingPathComponent("indexes.json").path
        try load()
    }

    /// Lists all index definitions.
    public func list() -> [IndexDef] { defs }

    /// Adds an index definition if not present and persists the catalog.
    public func add(_ def: IndexDef) throws {
        if !defs.contains(def) {
            defs.append(def)
            try save()
        }
    }

    public func remove(name: String, table: String) throws {
        if let idx = defs.firstIndex(where: { $0.name == name && $0.table == table }) {
            defs.remove(at: idx)
            try save()
        }
    }

    private func load() throws {
        let fm = FileManager.default
        guard fm.fileExists(atPath: path) else { return }
        let data = try Data(contentsOf: URL(fileURLWithPath: path))
        defs = (try? JSONDecoder().decode([IndexDef].self, from: data)) ?? []
    }

    private func save() throws {
        let data = try JSONEncoder().encode(defs)
        try data.write(to: URL(fileURLWithPath: path), options: .atomic)
    }
}

