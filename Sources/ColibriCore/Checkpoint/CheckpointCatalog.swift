//
//  CheckpointCatalog.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Checkpoint ledger tracking consistent snapshots.

import Foundation
/// Serializable checkpoint catalog capturing DB state at a checkpoint.

public struct CheckpointCatalog: Codable {
    /// Transaction entry recorded at checkpoint time.
    public struct TxEntry: Codable { public var tid: UInt64; public var lastLSN: UInt64; public var status: String }
    public var lastDBLSN: UInt64
    public var when: Date
    public var dpt: [[UInt64]]? // [ [pageId, recLSN] ]
    public var tx: [TxEntry]?   // active transactions at checkpoint
    public init(lastDBLSN: UInt64, when: Date, dpt: [[UInt64]]? = nil, tx: [TxEntry]? = nil) {
        self.lastDBLSN = lastDBLSN
        self.when = when
        self.dpt = dpt
        self.tx = tx
    }
}

/// File I/O helpers for checkpoint catalog.
public enum CheckpointIO {
    /// Returns the checkpoint catalog path inside the data directory.
    public static func path(in dataDir: String) -> String {
        let dir = URL(fileURLWithPath: dataDir).appendingPathComponent("checkpoints")
        try? FileManager.default.createDirectory(at: dir, withIntermediateDirectories: true)
        return dir.appendingPathComponent("catalog.json").path
    }

    /// Loads a checkpoint catalog from disk, if present.
    public static func load(from dataDir: String) -> CheckpointCatalog? {
        let p = path(in: dataDir)
        guard FileManager.default.fileExists(atPath: p) else { return nil }
        guard let data = try? Data(contentsOf: URL(fileURLWithPath: p)) else { return nil }
        return try? JSONDecoder().decode(CheckpointCatalog.self, from: data)
    }

    /// Atomically saves a checkpoint catalog to disk.
    public static func save(_ ckpt: CheckpointCatalog, in dataDir: String) throws {
        let p = path(in: dataDir)
        let data = try JSONEncoder().encode(ckpt)
        try data.write(to: URL(fileURLWithPath: p), options: .atomic)
    }
}

