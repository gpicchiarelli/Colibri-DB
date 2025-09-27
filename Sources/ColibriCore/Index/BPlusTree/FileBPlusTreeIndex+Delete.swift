//
//  FileBPlusTreeIndex+Delete.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrìDB — BSD 3-Clause License

// Theme: B+Tree surgeon deleting keys with borrow and merge tactics.

import Foundation

extension FileBPlusTreeIndex {
    // MARK: - Delete (with basic merge for underflow)

    public func remove(key: Value, rid: RID) throws {
        let k = KeyBytes.fromValue(key).bytes
        let lsn = try walAppendDelete(key: k, rid: rid)
        try removeBytesKey(k, rid: rid, lsn: lsn)
    }

    public func remove(composite: [Value], rid: RID) throws {
        let k = KeyBytes.fromValues(composite).bytes
        let lsn = try walAppendDelete(key: k, rid: rid)
        try removeBytesKey(k, rid: rid, lsn: lsn)
    }

    @discardableResult
    public func removeAll(key: Value) throws -> Int {
        let k = KeyBytes.fromValue(key).bytes
        return try removeAllBytesKey(k)
    }

    @discardableResult
    public func removeAll(composite: [Value]) throws -> Int {
        let k = KeyBytes.fromValues(composite).bytes
        return try removeAllBytesKey(k)
    }

    func removeBytesKey(_ key: Data, rid: RID, lsn: UInt64) throws {
        guard hdr.root != 0 else { return }
        var frames: [(pageId: UInt64, childIndex: Int)] = []
        var pid = hdr.root
        while true {
            let page = try readPage(pid)
            if page.type == 1 {
                let intr = try parseInternal(page.data)
                let idx = upperBound(keys: intr.keys, key: key)
                frames.append((pid, idx))
                pid = intr.children[idx]
            } else {
                break
            }
        }
        var leaf = try parseLeaf(readPage(pid).data)
        guard let i = binarySearch(keys: leaf.keys, key: key) else { return }
        var set = Set(leaf.ridLists[i])
        set.remove(rid)
        if set.isEmpty {
            leaf.keys.remove(at: i)
            leaf.ridLists.remove(at: i)
        } else {
            leaf.ridLists[i] = Array(set)
        }
        try writeLeaf(pageId: pid, keys: leaf.keys, ridLists: leaf.ridLists, nextLeaf: leaf.nextLeaf)
        if pid != hdr.root {
            let size = serializedLeafSize(keys: leaf.keys, ridLists: leaf.ridLists)
            // TODO: restore leaf borrow/merge once underflow rebalancing is fixed.
            if false && size < pageSize / 2 {
                if let parentFrame = frames.last {
                    var parent = try parseInternal(readPage(parentFrame.pageId).data)
                    if parentFrame.childIndex > 0 {
                        let leftPid = parent.children[parentFrame.childIndex - 1]
                        var left = try parseLeaf(readPage(leftPid).data)
                        if !left.keys.isEmpty {
                            let lk = left.keys.removeLast()
                            let lr = left.ridLists.removeLast()
                            leaf.keys.insert(lk, at: 0)
                            leaf.ridLists.insert(lr, at: 0)
                            try writeLeaf(pageId: leftPid, keys: left.keys, ridLists: left.ridLists, nextLeaf: left.nextLeaf, pageLSN: lsn)
                            try writeLeaf(pageId: pid, keys: leaf.keys, ridLists: leaf.ridLists, nextLeaf: leaf.nextLeaf, pageLSN: lsn)
                            parent.keys[parentFrame.childIndex - 1] = leaf.keys.first!
                            try writeInternal(pageId: parentFrame.pageId, keys: parent.keys, children: parent.children, pageLSN: lsn)
                            try fh.synchronize()
                            var up = frames
                            try rebalanceInternal(&up, lsn: lsn)
                            return
                        }
                    }
                    if parentFrame.childIndex < parent.children.count - 1 {
                        let rightPid = parent.children[parentFrame.childIndex + 1]
                        var right = try parseLeaf(readPage(rightPid).data)
                        if !right.keys.isEmpty {
                            let rk = right.keys.removeFirst()
                            let rr = right.ridLists.removeFirst()
                            leaf.keys.append(rk)
                            leaf.ridLists.append(rr)
                            try writeLeaf(pageId: rightPid, keys: right.keys, ridLists: right.ridLists, nextLeaf: right.nextLeaf, pageLSN: lsn)
                            try writeLeaf(pageId: pid, keys: leaf.keys, ridLists: leaf.ridLists, nextLeaf: leaf.nextLeaf, pageLSN: lsn)
                            if !right.keys.isEmpty {
                                parent.keys[parentFrame.childIndex] = right.keys.first!
                            } else {
                                parent.keys.remove(at: parentFrame.childIndex)
                                parent.children.remove(at: parentFrame.childIndex + 1)
                            }
                            try writeInternal(pageId: parentFrame.pageId, keys: parent.keys, children: parent.children, pageLSN: lsn)
                            try fh.synchronize()
                            var up = frames
                            try rebalanceInternal(&up, lsn: lsn)
                            return
                        }
                    }
                    var merged = false
                    if parentFrame.childIndex < parent.children.count - 1 {
                        let rightPid = parent.children[parentFrame.childIndex + 1]
                        let right = try parseLeaf(readPage(rightPid).data)
                        let mergedKeys = leaf.keys + right.keys
                        let mergedRids = leaf.ridLists + right.ridLists
                        if serializedLeafSize(keys: mergedKeys, ridLists: mergedRids) <= pageSize {
                            leaf.keys = mergedKeys
                            leaf.ridLists = mergedRids
                            leaf.nextLeaf = right.nextLeaf
                            try writeLeaf(pageId: pid, keys: leaf.keys, ridLists: leaf.ridLists, nextLeaf: leaf.nextLeaf, pageLSN: lsn)
                            parent.keys.remove(at: parentFrame.childIndex)
                            parent.children.remove(at: parentFrame.childIndex + 1)
                            try writeInternal(pageId: parentFrame.pageId, keys: parent.keys, children: parent.children, pageLSN: lsn)
                            merged = true
                        }
                    }
                    if !merged && parentFrame.childIndex > 0 {
                        let leftPid = parent.children[parentFrame.childIndex - 1]
                        let left = try parseLeaf(readPage(leftPid).data)
                        let mergedKeys = left.keys + leaf.keys
                        let mergedRids = left.ridLists + leaf.ridLists
                        if serializedLeafSize(keys: mergedKeys, ridLists: mergedRids) <= pageSize {
                            try writeLeaf(pageId: leftPid, keys: mergedKeys, ridLists: mergedRids, nextLeaf: leaf.nextLeaf, pageLSN: lsn)
                            parent.keys.remove(at: parentFrame.childIndex - 1)
                            parent.children.remove(at: parentFrame.childIndex)
                            try writeInternal(pageId: parentFrame.pageId, keys: parent.keys, children: parent.children, pageLSN: lsn)
                            frames[frames.count - 1].pageId = leftPid
                            merged = true
                        }
                    }
                    if merged {
                        frames.removeLast()
                        var up = frames
                        try rebalanceInternal(&up, lsn: lsn)
                    }
                }
            }
        } else {
            if leaf.keys.isEmpty {
                hdr.root = 0
                hdr.nextPage = 1
                try writeHeader()
            }
        }
    }

    func removeAllBytesKey(_ key: Data) throws -> Int {
        guard hdr.root != 0 else { return 0 }
        var pid = hdr.root
        while true {
            let page = try readPage(pid)
            if page.type == 1 {
                let intr = try parseInternal(page.data)
                let idx = upperBound(keys: intr.keys, key: key)
                pid = intr.children[idx]
            } else { break }
        }
        var leaf = try parseLeaf(readPage(pid).data)
        guard let i = binarySearch(keys: leaf.keys, key: key) else { return 0 }
        let removed = leaf.ridLists[i].count
        leaf.keys.remove(at: i)
        leaf.ridLists.remove(at: i)
        try writeLeaf(pageId: pid, keys: leaf.keys, ridLists: leaf.ridLists, nextLeaf: leaf.nextLeaf)
        return removed
    }

    func rebalanceInternal(_ frames: inout [(pageId: UInt64, childIndex: Int)], lsn: UInt64) throws {
        while let frame = frames.popLast() {
            let parentPid = frame.pageId
            var parent = try parseInternal(readPage(parentPid).data)
            if parentPid == hdr.root {
                if parent.keys.isEmpty {
                    hdr.root = parent.children.first ?? 0
                    try writeHeader()
                }
                return
            }
            guard let grandFrame = frames.popLast() else { break }
            var grand = try parseInternal(readPage(grandFrame.pageId).data)
            let pIndex = grandFrame.childIndex
            if serializedInternalSize(keys: parent.keys, children: parent.children) >= pageSize / 2 {
                frames.append(grandFrame)
                continue
            }
            if pIndex > 0 {
                let leftPid = grand.children[pIndex - 1]
                var left = try parseInternal(readPage(leftPid).data)
                if !left.keys.isEmpty {
                    let sep = grand.keys[pIndex - 1]
                    let moveKey = left.keys.removeLast()
                    let moveChild = left.children.removeLast()
                    parent.keys.insert(sep, at: 0)
                    parent.children.insert(moveChild, at: 0)
                    grand.keys[pIndex - 1] = moveKey
                    try writeInternal(pageId: leftPid, keys: left.keys, children: left.children, pageLSN: lsn)
                    try writeInternal(pageId: parentPid, keys: parent.keys, children: parent.children, pageLSN: lsn)
                    try writeInternal(pageId: grandFrame.pageId, keys: grand.keys, children: grand.children, pageLSN: lsn)
                    frames.append(grandFrame)
                    continue
                }
            }
            if pIndex < grand.children.count - 1 {
                let rightPid = grand.children[pIndex + 1]
                var right = try parseInternal(readPage(rightPid).data)
                if !right.keys.isEmpty {
                    let sep = grand.keys[pIndex]
                    let moveKey = right.keys.removeFirst()
                    let moveChild = right.children.removeFirst()
                    parent.keys.append(sep)
                    parent.children.append(moveChild)
                    grand.keys[pIndex] = moveKey
                    try writeInternal(pageId: rightPid, keys: right.keys, children: right.children, pageLSN: lsn)
                    try writeInternal(pageId: parentPid, keys: parent.keys, children: parent.children, pageLSN: lsn)
                    try writeInternal(pageId: grandFrame.pageId, keys: grand.keys, children: grand.children, pageLSN: lsn)
                    frames.append(grandFrame)
                    continue
                }
            }
            var mergedUp = false
            if pIndex < grand.children.count - 1 {
                let rightPid = grand.children[pIndex + 1]
                let right = try parseInternal(readPage(rightPid).data)
                let mergedKeys = parent.keys + [grand.keys[pIndex]] + right.keys
                let mergedChildren = parent.children + right.children
                if serializedInternalSize(keys: mergedKeys, children: mergedChildren) <= pageSize {
                    try writeInternal(pageId: parentPid, keys: mergedKeys, children: mergedChildren, pageLSN: lsn)
                    grand.keys.remove(at: pIndex)
                    grand.children.remove(at: pIndex + 1)
                    try writeInternal(pageId: grandFrame.pageId, keys: grand.keys, children: grand.children, pageLSN: lsn)
                    mergedUp = true
                }
            }
            if !mergedUp && pIndex > 0 {
                let leftPid = grand.children[pIndex - 1]
                let left = try parseInternal(readPage(leftPid).data)
                let mergedKeys = left.keys + [grand.keys[pIndex - 1]] + parent.keys
                let mergedChildren = left.children + parent.children
                if serializedInternalSize(keys: mergedKeys, children: mergedChildren) <= pageSize {
                    try writeInternal(pageId: leftPid, keys: mergedKeys, children: mergedChildren, pageLSN: lsn)
                    grand.keys.remove(at: pIndex - 1)
                    grand.children.remove(at: pIndex)
                    try writeInternal(pageId: grandFrame.pageId, keys: grand.keys, children: grand.children, pageLSN: lsn)
                    frames.append((pageId: leftPid, childIndex: pIndex - 1))
                    continue
                }
            }
            frames.append(grandFrame)
        }
    }
}

