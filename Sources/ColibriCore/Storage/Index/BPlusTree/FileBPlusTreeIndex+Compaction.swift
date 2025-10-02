//
//  FileBPlusTreeIndex+Compaction.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrDB — BSD 3-Clause License

// Theme: B+Tree janitor compacting leaves and pruning drift.

import Foundation

extension FileBPlusTreeIndex {
    // MARK: - Physical Compaction

    public func compactPhysical() throws {
        guard hdr.root != 0 else { return }
        var keys: [Data] = []
        var lists: [[RID]] = []
        var pid = hdr.root
        while true {
            let page = try readPage(pid)
            if page.type == 1 {
                let intr = try parseInternal(page.data)
                pid = intr.children.first ?? pid
            } else { break }
        }
        var cur = pid
        while cur != 0 {
            let page = try readPage(cur)
            guard page.type == 2 else { break }
            let leaf = try parseLeaf(page.data)
            keys.append(contentsOf: leaf.keys)
            lists.append(contentsOf: leaf.ridLists)
            cur = leaf.nextLeaf
        }
        try bulkBuildEncoded(keys: keys, ridLists: lists)
    }
}

