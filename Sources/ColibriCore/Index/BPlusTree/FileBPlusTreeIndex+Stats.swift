//
//  FileBPlusTreeIndex+Stats.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrìDB — BSD 3-Clause License

// Theme: B+Tree observatory computing metrics and health.

import Foundation

extension FileBPlusTreeIndex {
    // MARK: - Comparing helpers

    func upperBound(keys: [Data], key: Data) -> Int {
        var l = 0, r = keys.count
        while l < r {
            let m = (l + r) >> 1
            if keys[m].lexicographicallyPrecedes(key) || keys[m] == key { l = m + 1 } else { r = m }
        }
        return l
    }

    func lowerBound(keys: [Data], key: Data) -> Int {
        var l = 0, r = keys.count
        while l < r {
            let m = (l + r) >> 1
            if keys[m].lexicographicallyPrecedes(key) { l = m + 1 } else { r = m }
        }
        return l
    }

    func binarySearch(keys: [Data], key: Data) -> Int? {
        if keys.isEmpty { return nil }
        var l = 0, r = keys.count - 1
        while l <= r {
            let m = (l + r) >> 1
            if keys[m] == key { return m }
            if keys[m].lexicographicallyPrecedes(key) { l = m + 1 } else { r = m - 1 }
        }
        return nil
    }

    // MARK: - Stats & Fragmentation

    public func estimateLeafOccupancy(sampleLeaves: Int = 8) throws -> Double {
        guard hdr.root != 0 else { return 1.0 }
        var pid = hdr.root
        while true {
            let page = try readPage(pid)
            if page.type == 1 {
                pid = (try parseInternal(page.data)).children.first ?? pid
            } else {
                break
            }
        }
        var cur = pid
        var leaves = 0
        var usedTotal = 0
        while cur != 0 && leaves < sampleLeaves {
            let page = try readPage(cur)
            guard page.type == 2 else { break }
            usedTotal += estimateLeafUsedBytes(page.data)
            leaves += 1
            let leaf = try parseLeaf(page.data)
            cur = leaf.nextLeaf
        }
        if leaves == 0 { return 1.0 }
        let avg = Double(usedTotal) / Double(leaves)
        return min(1.0, max(0.0, avg / Double(pageSize)))
    }

    func estimateLeafUsedBytes(_ d: Data) -> Int {
        d.reduce(0) { $1 == 0 ? $0 : $0 + 1 }
    }
}

