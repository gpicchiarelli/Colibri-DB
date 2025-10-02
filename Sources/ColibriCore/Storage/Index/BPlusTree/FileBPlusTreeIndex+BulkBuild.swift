//
//  FileBPlusTreeIndex+BulkBuild.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrDB — BSD 3-Clause License

// Theme: B+Tree foundry crafting bulk builds bottom-up.

import Foundation

extension FileBPlusTreeIndex {
    // MARK: - Bulk Build (bottom-up)

    public func bulkBuildEncoded(keys: [Data], ridLists: [[RID]]) throws {
        try fh.truncate(atOffset: 0)
        hdr = .init(pageSize: pageSize, root: 0, nextPage: 1, checkpointLSN: 0)
        try writeHeader()

        var leafIds: [UInt64] = []
        var leafFirst: [Data] = []
        var i = 0
        while i < keys.count {
            var pageKeys: [Data] = []
            var pageRids: [[RID]] = []
            var _ = serializedLeafSize(keys: pageKeys, ridLists: pageRids)
            while i < keys.count {
                let k = keys[i]
                let r = ridLists[i]
                let add = serializedLeafSize(keys: pageKeys + [k], ridLists: pageRids + [r])
                if add > pageSize && !pageKeys.isEmpty { break }
                pageKeys.append(k); pageRids.append(r)
                _ = add
                i += 1
            }
            let pid = try allocPage()
            try writeLeaf(pageId: pid, keys: pageKeys, ridLists: pageRids, nextLeaf: 0, pageLSN: 0)
            if let prev = leafIds.last {
                let prevLeaf = try parseLeaf(readPage(prev).data)
                try writeLeaf(pageId: prev, keys: prevLeaf.keys, ridLists: prevLeaf.ridLists, nextLeaf: pid, pageLSN: 0)
            }
            leafIds.append(pid)
            if let first = pageKeys.first { leafFirst.append(first) } else { leafFirst.append(Data()) }
        }

        var childIds = leafIds
        var childFirstKeys = leafFirst
        while childIds.count > 1 {
            var newIds: [UInt64] = []
            var newFirst: [Data] = []
            var idx = 0
            while idx < childIds.count {
                var keysPage: [Data] = []
                var childrenPage: [UInt64] = []
                childrenPage.append(childIds[idx])
                var _ = serializedInternalSize(keys: keysPage, children: childrenPage)
                var j = idx + 1
                while j < childIds.count {
                    let ksep = childFirstKeys[j]
                    let addSize = serializedInternalSize(keys: keysPage + [ksep], children: childrenPage + [childIds[j]])
                    if addSize > pageSize && !keysPage.isEmpty { break }
                    keysPage.append(ksep)
                    childrenPage.append(childIds[j])
                    _ = addSize
                    j += 1
                }
                let pid = try allocPage()
                try writeInternal(pageId: pid, keys: keysPage, children: childrenPage, pageLSN: 0)
                newIds.append(pid)
                newFirst.append(childFirstKeys[idx])
                idx = j
            }
            childIds = newIds
            childFirstKeys = newFirst
        }

        hdr.root = childIds.first ?? 0
        try writeHeader()
        // WAL cleared - using global WAL now
    }
}

