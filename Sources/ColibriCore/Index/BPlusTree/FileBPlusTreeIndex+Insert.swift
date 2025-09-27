//
//  FileBPlusTreeIndex+Insert.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrìDB — BSD 3-Clause License

// Theme: B+Tree nursery inserting keys while keeping balance.

import Foundation

extension FileBPlusTreeIndex {
    // MARK: - Insert recursion

    func insertRecursive(pageId: UInt64, key: Data, rid: RID, lsn: UInt64 = 0) throws -> (Data?, UInt64?) {
        let page = try readPage(pageId)
        if page.type == 1 {
            var intr = try parseInternal(page.data)
            let idx = upperBound(keys: intr.keys, key: key)
            let (promoKey, promoRight) = try insertRecursive(pageId: intr.children[idx], key: key, rid: rid, lsn: lsn)
            if let pk = promoKey, let right = promoRight {
                intr.keys.insert(pk, at: idx)
                intr.children.insert(right, at: idx + 1)
                let size = serializedInternalSize(keys: intr.keys, children: intr.children)
                if size > pageSize {
                    // Optimized split: use 60/40 ratio to reduce future splits
                    let splitPoint = Int(Double(intr.keys.count) * 0.6)
                    let promoted = intr.keys[splitPoint]
                    let leftKeys = Array(intr.keys[..<splitPoint])
                    let rightKeys = Array(intr.keys[(splitPoint+1)...])
                    let leftChildren = Array(intr.children[..<(splitPoint+1)])
                    let rightChildren = Array(intr.children[(splitPoint+1)...])
                    try writeInternal(pageId: pageId, keys: leftKeys, children: leftChildren, pageLSN: lsn)
                    let rightPage = try allocPage()
                    try writeInternal(pageId: rightPage, keys: rightKeys, children: rightChildren, pageLSN: lsn)
                    return (promoted, rightPage)
                } else {
                    try writeInternal(pageId: pageId, keys: intr.keys, children: intr.children, pageLSN: lsn)
                }
            }
            return (nil, nil)
        } else {
            var leaf = try parseLeaf(page.data)
            if let i = binarySearch(keys: leaf.keys, key: key) {
                var set = Set(leaf.ridLists[i])
                if leaf.tombstones[i].remove(rid) != nil {
                    // revived tombstone
                }
                set.insert(rid)
                leaf.ridLists[i] = Array(set)
            } else {
                let pos = lowerBound(keys: leaf.keys, key: key)
                leaf.keys.insert(key, at: pos)
                leaf.ridLists.insert([rid], at: pos)
                leaf.tombstones.insert([], at: pos)
            }
            let size = serializedLeafSize(keys: leaf.keys, ridLists: leaf.ridLists)
            if size > pageSize {
                // Optimized split: use 60/40 ratio to reduce future splits
                let splitPoint = Int(Double(leaf.keys.count) * 0.6)
                let rightKeys = Array(leaf.keys[splitPoint...])
                let rightRids = Array(leaf.ridLists[splitPoint...])
                let leftKeys = Array(leaf.keys[..<splitPoint])
                let leftRids = Array(leaf.ridLists[..<splitPoint])
                let rightPage = try allocPage()
                try writeLeaf(pageId: rightPage, keys: rightKeys, ridLists: rightRids, nextLeaf: leaf.nextLeaf, pageLSN: lsn)
                try writeLeaf(pageId: pageId, keys: leftKeys, ridLists: leftRids, nextLeaf: rightPage, pageLSN: lsn)
                let promoted = rightKeys.first!
                return (promoted, rightPage)
            } else {
                try writeLeaf(pageId: pageId, keys: leaf.keys, ridLists: leaf.ridLists, nextLeaf: leaf.nextLeaf, pageLSN: lsn)
                return (nil, nil)
            }
        }
    }

    func serializedInternalSize(keys: [Data], children: [UInt64]) -> Int {
        var size = 16
        size += 8
        for k in keys {
            size += VarInt.encode(UInt64(k.count)).count
            size += k.count
            size += 8
        }
        return size
    }

    func serializedLeafSize(keys: [Data], ridLists: [[RID]]) -> Int {
        var size = 24
        for (i, k) in keys.enumerated() {
            size += VarInt.encode(UInt64(k.count)).count
            size += k.count
            let r = ridLists[i]
            size += VarInt.encode(UInt64(r.count)).count
            size += r.count * (8 + 2)
        }
        return size
    }
}

