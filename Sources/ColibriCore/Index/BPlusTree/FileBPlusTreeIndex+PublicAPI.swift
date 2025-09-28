//
//  FileBPlusTreeIndex+PublicAPI.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrìDB — BSD 3-Clause License

// Theme: B+Tree front desk exposing query entry points.

import Foundation

extension FileBPlusTreeIndex {
    // MARK: - Public API

    public func insert(key: Value, rid: RID, sync: Bool = true) throws {
        let k = KeyBytes.fromValue(key).bytes
        let lsn: UInt64
        if false { // WAL disabled
            // lsn = try walAppendInsert(key: k, rid: rid) // Removed
            lsn = 0
        } else {
            lsn = 0
        }
        if hdr.root == 0 { // create first leaf root
            let leafId = try allocPage()
            try writeLeaf(pageId: leafId, keys: [k], ridLists: [[rid]], nextLeaf: 0, pageLSN: lsn)
            hdr.root = leafId
            try writeHeader()
            if sync { try fh.synchronize() }
            // WAL functionality disabled
            return
        }
        let (promoKey, promoRight) = try insertRecursive(pageId: hdr.root, key: k, rid: rid, lsn: lsn)
        if let pk = promoKey, let right = promoRight {
            let newRoot = try allocPage()
            try writeInternal(pageId: newRoot, keys: [pk], children: [hdr.root, right], pageLSN: lsn)
            hdr.root = newRoot
            try writeHeader()
        }
        if sync { try fh.synchronize() }
        // WAL functionality disabled
    }

    // Global WAL variant: caller provides pageLSN (single WAL for heap+index)
    public func insert(key: Value, rid: RID, pageLSN: UInt64, sync: Bool = true) throws {
        let k = KeyBytes.fromValue(key).bytes
        if hdr.root == 0 {
            let leafId = try allocPage()
            try writeLeaf(pageId: leafId, keys: [k], ridLists: [[rid]], nextLeaf: 0, pageLSN: pageLSN)
            hdr.root = leafId
            try writeHeader()
            if sync { try fh.synchronize() }
            return
        }
        let (promoKey, promoRight) = try insertRecursive(pageId: hdr.root, key: k, rid: rid, lsn: pageLSN)
        if let pk = promoKey, let right = promoRight {
            let newRoot = try allocPage()
            try writeInternal(pageId: newRoot, keys: [pk], children: [hdr.root, right], pageLSN: pageLSN)
            hdr.root = newRoot
            try writeHeader()
        }
        if sync { try fh.synchronize() }
    }

    public func insert(composite: [Value], rid: RID) throws {
        let k = KeyBytes.fromValues(composite).bytes
        let lsn: UInt64
        if false { // WAL disabled
            // lsn = try walAppendInsert(key: k, rid: rid) // Removed
            lsn = 0
        } else { 
            lsn = 0 
        }
        if hdr.root == 0 {
            let leafId = try allocPage()
            try writeLeaf(pageId: leafId, keys: [k], ridLists: [[rid]], nextLeaf: 0, pageLSN: lsn)
            hdr.root = leafId
            try writeHeader(); try fh.synchronize(); return
        }
        let (pk, right) = try insertRecursive(pageId: hdr.root, key: k, rid: rid, lsn: lsn)
        if let pk = pk, let r: UInt64 = right {
            let newRoot = try allocPage(); try writeInternal(pageId: newRoot, keys: [pk], children: [hdr.root, r], pageLSN: lsn); hdr.root = newRoot; try writeHeader()
        }
        try fh.synchronize()
        // WAL functionality disabled
    }

    /// Batch insert optimization for better performance
    /// - Parameters:
    ///   - entries: Array of (key, rid) pairs to insert
    ///   - pageLSN: Page LSN for WAL consistency
    /// - Throws: Database errors
    public func insertBatch(entries: [(Value, RID)], pageLSN: UInt64 = 0) throws {
        guard !entries.isEmpty else { return }
        
        // Sort entries by key for better cache locality and reduced splits
        let sortedEntries = entries.sorted { 
            let key1 = KeyBytes.fromValue($0.0).bytes
            let key2 = KeyBytes.fromValue($1.0).bytes
            return compareBytes(key1, key2) < 0
        }
        
        for (key, rid) in sortedEntries {
            let k = KeyBytes.fromValue(key).bytes
            if hdr.root == 0 {
                let leafId = try allocPage()
                try writeLeaf(pageId: leafId, keys: [k], ridLists: [[rid]], nextLeaf: 0, pageLSN: pageLSN)
                hdr.root = leafId
                try writeHeader()
            } else {
                let (promoKey, promoRight) = try insertRecursive(pageId: hdr.root, key: k, rid: rid, lsn: pageLSN)
                if let pk = promoKey, let right = promoRight {
                    let newRoot = try allocPage()
                    try writeInternal(pageId: newRoot, keys: [pk], children: [hdr.root, right], pageLSN: pageLSN)
                    hdr.root = newRoot
                    try writeHeader()
                }
            }
        }
        
        // Single synchronize at the end instead of per-insert
        try fh.synchronize()
    }

    public func insert(composite: [Value], rid: RID, pageLSN: UInt64) throws {
        let k = KeyBytes.fromValues(composite).bytes
        if hdr.root == 0 {
            let leafId = try allocPage()
            try writeLeaf(pageId: leafId, keys: [k], ridLists: [[rid]], nextLeaf: 0, pageLSN: pageLSN)
            hdr.root = leafId
            try writeHeader(); try fh.synchronize(); return
        }
        let (pk, right) = try insertRecursive(pageId: hdr.root, key: k, rid: rid, lsn: pageLSN)
        if let pk = pk, let r: UInt64 = right {
            let newRoot = try allocPage(); try writeInternal(pageId: newRoot, keys: [pk], children: [hdr.root, r], pageLSN: pageLSN); hdr.root = newRoot; try writeHeader()
        }
        try fh.synchronize()
    }

    public func searchEquals(_ key: Value) throws -> [RID] {
        let k = KeyBytes.fromValue(key).bytes
        guard hdr.root != 0 else { return [] }
        var pid = hdr.root
        while true {
            let page = try readPage(pid)
            if page.type == 1 {
                let inpg = try parseInternal(page.data)
                let idx = upperBound(keys: inpg.keys, key: k)
                pid = inpg.children[idx]
            } else {
                let leaf = try parseLeaf(page.data)
                if let i = binarySearch(keys: leaf.keys, key: k) {
                    return leaf.ridLists[i]
                }
                return []
            }
        }
    }
    
    /// Optimized search that avoids KeyBytes allocation in hot path
    public func searchEqualsOptimized(_ key: Value) throws -> [RID] {
        guard hdr.root != 0 else { return [] }
        var pid = hdr.root
        while true {
            let page = try readPage(pid)
            if page.type == 1 {
                let inpg = try parseInternal(page.data)
                let idx = upperBoundOptimized(keys: inpg.keys, key: key)
                pid = inpg.children[idx]
            } else {
                let leaf = try parseLeaf(page.data)
                if let i = binarySearchOptimized(keys: leaf.keys, key: key) {
                    return leaf.ridLists[i]
                }
                return []
            }
        }
    }

    public func searchEquals(composite: [Value]) throws -> [RID] {
        let k = KeyBytes.fromValues(composite).bytes
        guard hdr.root != 0 else { return [] }
        var pid = hdr.root
        while true {
            let page = try readPage(pid)
            if page.type == 1 {
                let inpg = try parseInternal(page.data)
                let idx = upperBound(keys: inpg.keys, key: k)
                pid = inpg.children[idx]
            } else {
                let leaf = try parseLeaf(page.data)
                if let i = binarySearch(keys: leaf.keys, key: k) { return leaf.ridLists[i] }
                return []
            }
        }
    }

    public func range(_ lo: Value?, _ hi: Value?) throws -> [RID] {
        guard hdr.root != 0 else { return [] }
        let loK = lo.map { KeyBytes.fromValue($0).bytes }
        let hiK = hi.map { KeyBytes.fromValue($0).bytes }
        var res: [RID] = []
        var pid = hdr.root
        while true {
            guard let page = try? readPage(pid) else { return res }
            if page.type == 1 {
                let inpg = try parseInternal(page.data)
                let idx = loK.map { upperBound(keys: inpg.keys, key: $0) } ?? 0
                pid = inpg.children[idx]
            } else {
                var leaf = try! parseLeaf(page.data)
                var i = loK.flatMap { lowerBound(keys: leaf.keys, key: $0) } ?? 0
                while true {
                    while i < leaf.keys.count {
                        let k = leaf.keys[i]
                        if let hiK = hiK, compareBytes(k, hiK) > 0 { return res }
                        res.append(contentsOf: leaf.ridLists[i])
                        i += 1
                    }
                    if leaf.nextLeaf == 0 { return res }
                    guard let nextPage = try? readPage(leaf.nextLeaf) else { return res }
                    leaf = try! parseLeaf(nextPage.data)
                    i = 0
                }
            }
        }
    }

    public func range(compositeLo lo: [Value]?, compositeHi hi: [Value]?) throws -> [RID] {
        guard hdr.root != 0 else { return [] }
        let loK = lo.map { KeyBytes.fromValues($0).bytes }
        let hiK = hi.map { KeyBytes.fromValues($0).bytes }
        var res: [RID] = []
        var pid = hdr.root
        while true {
            guard let page = try? readPage(pid) else { return res }
            if page.type == 1 {
                let inpg = try parseInternal(page.data)
                let idx = loK.map { upperBound(keys: inpg.keys, key: $0) } ?? 0
                pid = inpg.children[idx]
            } else {
                var leaf = try! parseLeaf(page.data)
                var i = loK.flatMap { lowerBound(keys: leaf.keys, key: $0) } ?? 0
                while true {
                    while i < leaf.keys.count {
                        let k = leaf.keys[i]
                        if let hiK = hiK, compareBytes(k, hiK) > 0 { return res }
                        res.append(contentsOf: leaf.ridLists[i])
                        i += 1
                    }
                    if leaf.nextLeaf == 0 { return res }
                    guard let nextPage = try? readPage(leaf.nextLeaf) else { return res }
                    leaf = try! parseLeaf(nextPage.data)
                    i = 0
                }
            }
        }
    }

    public func rangePrefixedBy(_ prefix: [Value]) throws -> [RID] {
        guard hdr.root != 0 else { return [] }
        let lo = KeyBytes.fromValues(prefix).bytes
        var hi = lo; hi.append(0xFF)
        return try rangeEncoded(loKey: lo, hiKey: hi)
    }

    func rangeEncoded(loKey: Data, hiKey: Data) throws -> [RID] {
        var res: [RID] = []
        var pid = hdr.root
        while true {
            guard let page = try? readPage(pid) else { return res }
            if page.type == 1 {
                let inpg = try parseInternal(page.data)
                let idx = upperBound(keys: inpg.keys, key: loKey)
                pid = inpg.children[idx]
            } else {
                var leaf = try! parseLeaf(page.data)
                var i = lowerBound(keys: leaf.keys, key: loKey)
                while true {
                    while i < leaf.keys.count {
                        let k = leaf.keys[i]
                        if compareBytes(k, hiKey) > 0 { return res }
                        res.append(contentsOf: leaf.ridLists[i])
                        i += 1
                    }
                    if leaf.nextLeaf == 0 { return res }
                    guard let nextPage = try? readPage(leaf.nextLeaf) else { return res }
                    leaf = try! parseLeaf(nextPage.data)
                    i = 0
                }
            }
        }
    }
}

