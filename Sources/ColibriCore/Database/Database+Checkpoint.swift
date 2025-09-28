//
//  Database+Checkpoint.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Checkpoint captain snapshotting dirty page state.

import Foundation
// MARK: - Checkpoint

extension Database {
    public func checkpoint() throws {
        // Flush and sync global WAL  
        if let w = globalWAL {
            try w.groupCommitSync()
        }
        // Flush heap tables buffer pools
        for (_, ft) in tablesFile { try? ft.flush() }
        // Ask indexes to checkpoint and truncate their WAL
        for (_, tableMap) in indexes {
            for (_, def) in tableMap {
                switch def.backend {
                case .anyString:
                    continue
                case .persistentBTree(let idx):
                    try? idx.checkpointIndex()
                }
            }
        }
        // Persist checkpoint catalog with DPT and active transactions
        let dptArr = dpt.map { [$0.key, $0.value] }
        let txArr: [CheckpointCatalog.TxEntry] = activeTIDs.map { tid in
            CheckpointCatalog.TxEntry(tid: tid, lastLSN: txLastLSN[tid] ?? 0, status: "active")
        }
        let ckpt = CheckpointCatalog(lastDBLSN: lastDBLSN, when: Date(), dpt: dptArr, tx: txArr)
        try CheckpointIO.save(ckpt, in: config.dataDir)
    }
}

