//
//  FileBPlusTreeIndex+Validation.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrìDB — BSD 3-Clause License

// Theme: B+Tree inspection bay validating structural invariants.

import Foundation

extension FileBPlusTreeIndex {
    // MARK: - Deep validation (consistency checks)

    public struct DeepReport: CustomStringConvertible {
        public let ok: Bool
        public let leaves: Int
        public let internalNodes: Int
        public let keys: Int
        public let zeroLSNPages: Int
        public let badLeafLinks: Int
        public let olderThanCheckpointPages: Int
        public let messages: [String]
        public var description: String {
            "ok=\(ok) leaves=\(leaves) internal=\(internalNodes) keys=\(keys) zeroLSN=\(zeroLSNPages) oldLSN=\(olderThanCheckpointPages) badLeafLinks=\(badLeafLinks) messages=\(messages.joined(separator: "; "))"
        }
    }

    public func validateDeep() throws -> DeepReport {
        guard hdr.root != 0 else {
            return DeepReport(ok: true, leaves: 0, internalNodes: 0, keys: 0, zeroLSNPages: 0, badLeafLinks: 0, olderThanCheckpointPages: 0, messages: ["empty-root"])
        }
        var messages: [String] = []
        var internalCount = 0
        var totalKeys = 0
        var zeroLSN = 0
        var badLeafLinks = 0
        var olderLSN = 0
        var boundaryViolations = 0
        var firstLeafDepth: Int? = nil
        var depthMismatch = 0

        func dfsBounds(_ pid: UInt64, _ lower: Data?, _ upper: Data?, _ depth: Int) -> Bool {
            let page = try readPage(pid)
            if page.type == 1 {
                internalCount += 1
                let intr = try parseInternal(page.data)
                let lsn = page.data.subdata(in: 8..<(8+8)).withUnsafeBytes { $0.load(as: UInt64.self) }.bigEndian
                if lsn == 0 && !intr.keys.isEmpty { zeroLSN += 1 }
                if lsn != 0 && lsn < hdr.checkpointLSN { olderLSN += 1 }
                if !dfsBounds(intr.children.first ?? 0, lower, intr.keys.first, depth + 1) { return false }
                for i in 1..<intr.children.count - 1 {
                    let low = intr.keys[i - 1]
                    let up = intr.keys[i]
                    if !dfsBounds(intr.children[i], low, up, depth + 1) { return false }
                }
                if let lastChild = intr.children.last {
                    if !dfsBounds(lastChild, intr.keys.last, upper, depth + 1) { return false }
                }
                return true
            } else if page.type == 2 {
                let leaf = try parseLeaf(page.data)
                let lsn = page.data.subdata(in: 8..<(8+8)).withUnsafeBytes { $0.load(as: UInt64.self) }.bigEndian
                if lsn == 0 && !leaf.keys.isEmpty { zeroLSN += 1 }
                if lsn != 0 && lsn < hdr.checkpointLSN { olderLSN += 1 }
                if let d0 = firstLeafDepth { if d0 != depth { depthMismatch += 1 } } else { firstLeafDepth = depth }
                for k in leaf.keys {
                    if let lb = lower, compareBytes(lb, k) > 0 { boundaryViolations += 1 }
                    if let ub = upper, compareBytes(k, ub) > 0 { boundaryViolations += 1 }
                    totalKeys += 1
                }
                return true
            } else {
                messages.append("unknown-page-type@\(pid)")
                return false
            }
        }
        let okBounds = dfsBounds(hdr.root, nil, nil, 0)

        var leafCount = 0
        var prevKey: Data? = nil
        var pid = hdr.root
        while true {
            let page = try readPage(pid)
            if page.type == 1 {
                let intr = try parseInternal(page.data)
                pid = intr.children.first ?? pid
            } else { break }
        }
        var curPid = pid
        while curPid != 0 {
            let page = try readPage(curPid)
            if page.type != 2 { messages.append("leaf-type-mismatch@\(curPid)"); badLeafLinks += 1; break }
            let leaf = try parseLeaf(page.data)
            let lsn = page.data.subdata(in: 8..<(8+8)).withUnsafeBytes { $0.load(as: UInt64.self) }.bigEndian
            if lsn == 0 && !leaf.keys.isEmpty { zeroLSN += 1 }
            if lsn != 0 && lsn < hdr.checkpointLSN { olderLSN += 1 }
            leafCount += 1
            for k in leaf.keys {
                if let pk = prevKey {
                    if compareBytes(pk, k) > 0 {
                        messages.append("leaf-order@\(curPid)")
                        return DeepReport(ok: false, leaves: leafCount, internalNodes: internalCount, keys: totalKeys, zeroLSNPages: zeroLSN, badLeafLinks: badLeafLinks, olderThanCheckpointPages: olderLSN, messages: messages)
                    }
                }
                prevKey = k
                totalKeys += 1
            }
            if leaf.nextLeaf == 0 { break }
            let np = try readPage(leaf.nextLeaf)
            if np.type != 2 { badLeafLinks += 1; messages.append("leaf-next-not-leaf@\(curPid)->\(leaf.nextLeaf)"); break }
            curPid = leaf.nextLeaf
        }
        let ok = okBounds && messages.isEmpty && badLeafLinks == 0 && boundaryViolations == 0 && depthMismatch == 0
        if boundaryViolations > 0 { messages.append("bound-violations=\(boundaryViolations)") }
        if depthMismatch > 0 { messages.append("leaf-depth-mismatch=\(depthMismatch)") }
        return DeepReport(ok: ok, leaves: leafCount, internalNodes: internalCount, keys: totalKeys, zeroLSNPages: zeroLSN, badLeafLinks: badLeafLinks, olderThanCheckpointPages: olderLSN, messages: messages)
    }

    public func dumpHeader(pageId: UInt64?) -> String {
        if let pid = pageId, pid > 0 {
            let page = try readPage(pid)
            if page.type == 1 {
                let keyCount = Int(page.data.subdata(in: 1..<3).withUnsafeBytes { $0.load(as: UInt16.self) }.bigEndian)
                let childCount = Int(page.data.subdata(in: 3..<5).withUnsafeBytes { $0.load(as: UInt16.self) }.bigEndian)
                let lsn = page.data.subdata(in: 8..<(8+8)).withUnsafeBytes { $0.load(as: UInt64.self) }.bigEndian
                return "page=\(pid) type=internal keys=\(keyCount) children=\(childCount) pageLSN=\(lsn)"
            } else if page.type == 2 {
                let keyCount = Int(page.data.subdata(in: 1..<3).withUnsafeBytes { $0.load(as: UInt16.self) }.bigEndian)
                let lsn = page.data.subdata(in: 8..<(8+8)).withUnsafeBytes { $0.load(as: UInt64.self) }.bigEndian
                let nextLeaf = page.data.subdata(in: 16..<(16+8)).withUnsafeBytes { $0.load(as: UInt64.self) }.bigEndian
                return "page=\(pid) type=leaf keys=\(keyCount) pageLSN=\(lsn) nextLeaf=\(nextLeaf)"
            } else {
                return "page=\(pid) type=unknown(\(page.type))"
            }
        } else {
            let stats = buf?.statsString() ?? "nobuf"
            return "fileHeader: pageSize=\(pageSize) root=\(hdr.root) nextPage=\(hdr.nextPage) checkpointLSN=\(hdr.checkpointLSN) pool=\(stats)"
        }
    }

    public func poolMetrics() -> LRUBufferPool.Metrics? { buf?.metrics() }

    public func dumpFirstLeaves(count: Int) -> [String] {
        var results: [String] = []
        guard hdr.root != 0, count > 0 else { return results }
        var pid = hdr.root
        while true {
            let page = try readPage(pid)
            if page.type == 1 {
                let intr = try parseInternal(page.data)
                if let c0 = intr.children.first {
                    pid = c0
                } else {
                    break
                }
            } else {
                break
            }
        }
        var current = pid
        var left = count
        while current != 0 && left > 0 {
            let page = try readPage(current)
            if page.type != 2 { results.append("page=\(current) type=\(page.type) unexpected"); break }
            let keyCount = Int(page.data.subdata(in: 1..<3).withUnsafeBytes { $0.load(as: UInt16.self) }.bigEndian)
            let lsn = page.data.subdata(in: 8..<(8+8)).withUnsafeBytes { $0.load(as: UInt64.self) }.bigEndian
            let nextLeaf = page.data.subdata(in: 16..<(16+8)).withUnsafeBytes { $0.load(as: UInt64.self) }.bigEndian
            results.append("page=\(current) type=leaf keys=\(keyCount) pageLSN=\(lsn) nextLeaf=\(nextLeaf)")
            current = nextLeaf
            left -= 1
        }
        return results
    }
}

