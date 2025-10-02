//
//  FileBPlusTreeIndex+Stats.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrDB — BSD 3-Clause License

// Theme: B+Tree observatory computing metrics and health.

import Foundation

extension FileBPlusTreeIndex {
    // MARK: - Comparing helpers

    @inline(__always) func upperBound(keys: [Data], key: Data) -> Int {
        var l = 0, r = keys.count
        while l < r {
            let m = (l + r) >> 1
            // Optimized byte-wise comparison
            let le = compareBytes(keys[m], key) <= 0
            l = le ? (m + 1) : l
            r = le ? r : m
        }
        return l
    }

    @inline(__always) func lowerBound(keys: [Data], key: Data) -> Int {
        var l = 0, r = keys.count
        while l < r {
            let m = (l + r) >> 1
            let lt = compareBytes(keys[m], key) < 0
            l = lt ? (m + 1) : l
            r = lt ? r : m
        }
        return l
    }

    @inline(__always) func binarySearch(keys: [Data], key: Data) -> Int? {
        if keys.isEmpty { return nil }
        var l = 0, r = keys.count - 1
        while l <= r {
            let m = (l + r) >> 1
            let cmp = compareBytes(keys[m], key)
            if cmp == 0 { return m }
            if cmp < 0 { l = m + 1 } else { r = m - 1 }
        }
        return nil
    }
    
    /// 🚀 OPTIMIZATION: Branchless binary search for better CPU pipeline performance
    @inline(__always) func binarySearchBranchless(keys: [Data], key: Data) -> Int? {
        if keys.isEmpty { return nil }
        
        let count = keys.count
        var base = 0
        var n = count
        
        // Branchless binary search using bit manipulation
        while n > 1 {
            let half = n >> 1
            let mid = base + half
            let cmp = compareBytes(keys[mid], key)
            
            // Branchless update: if cmp < 0, move base forward
            base = cmp < 0 ? mid : base
            n = cmp < 0 ? (n - half) : half
        }
        
        // Final check
        if base < count && compareBytes(keys[base], key) == 0 {
            return base
        }
        
        return nil
    }

    /// Optimized byte-wise comparison using withUnsafeBytes + memcmp
    /// Returns: -1 if a < b, 0 if a == b, 1 if a > b
    @inline(__always) func compareBytes(_ a: Data, _ b: Data) -> Int {
        let aCount = a.count
        let bCount = b.count
        
        // Quick length comparison first
        if aCount != bCount {
            return aCount < bCount ? -1 : 1
        }
        
        // Zero-length case
        if aCount == 0 {
            return 0
        }
        
        // Use withUnsafeBytes for zero-copy comparison
        return a.withUnsafeBytes { aBytes in
            b.withUnsafeBytes { bBytes in
                let result = memcmp(aBytes.baseAddress, bBytes.baseAddress, aCount)
                if result < 0 { return -1 }
                if result > 0 { return 1 }
                return 0
            }
        }
    }

    /// Optimized binary search that compares Value directly without KeyBytes allocation
    @inline(__always) func binarySearchOptimized(keys: [Data], key: Value) -> Int? {
        if keys.isEmpty { return nil }
        var l = 0, r = keys.count - 1
        while l <= r {
            let m = (l + r) >> 1
            let cmp = compareValueToKey(key, keys[m])
            if cmp == 0 { return m }
            if cmp < 0 { l = m + 1 } else { r = m - 1 }
        }
        return nil
    }
    
    /// Optimized upper bound that compares Value directly without KeyBytes allocation
    @inline(__always) func upperBoundOptimized(keys: [Data], key: Value) -> Int {
        var l = 0, r = keys.count
        while l < r {
            let m = (l + r) >> 1
            let le = compareValueToKey(key, keys[m]) >= 0
            l = le ? (m + 1) : l
            r = le ? r : m
        }
        return l
    }
    
    /// Direct comparison between Value and Data key without allocation
    @inline(__always) func compareValueToKey(_ value: Value, _ keyData: Data) -> Int {
        // Quick type check first
        guard !keyData.isEmpty else { return 0 }
        let keyType = keyData[0]
        
        switch value {
        case .null:
            return keyType == 0x00 ? 0 : (keyType < 0x00 ? 1 : -1)
        case .bool(let b):
            if keyType != 0x01 { return keyType < 0x01 ? 1 : -1 }
            if keyData.count < 2 { return 0 }
            let keyBool = keyData[1] != 0
            return b == keyBool ? 0 : (b ? 1 : -1)
        case .int(let i):
            if keyType != 0x02 { return keyType < 0x02 ? 1 : -1 }
            if keyData.count < 9 { return 0 }
            let u = UInt64(bitPattern: i &+ Int64(bitPattern: 0x8000_0000_0000_0000))
            let keyU = keyData.subdata(in: 1..<9).withUnsafeBytes { $0.load(as: UInt64.self) }.bigEndian
            return u == keyU ? 0 : (u < keyU ? -1 : 1)
        case .double(let d):
            if keyType != 0x03 { return keyType < 0x03 ? 1 : -1 }
            if keyData.count < 9 { return 0 }
            var bits = d.bitPattern
            if (bits & (1 << 63)) != 0 { bits = ~bits } else { bits ^= (1 << 63) }
            let keyBits = keyData.subdata(in: 1..<9).withUnsafeBytes { $0.load(as: UInt64.self) }.bigEndian
            return bits == keyBits ? 0 : (bits < keyBits ? -1 : 1)
        case .string(let s):
            if keyType != 0x04 { return keyType < 0x04 ? 1 : -1 }
            let keyString = String(data: keyData.dropFirst(), encoding: .utf8) ?? ""
            return s == keyString ? 0 : (s < keyString ? -1 : 1)
        case .decimal(let d):
            let doubleValue = Double(truncating: d as NSNumber)
            return compareValueToKey(.double(doubleValue), keyData)
        case .date(let d):
            let timestamp = d.timeIntervalSince1970
            return compareValueToKey(.double(timestamp), keyData)
        }
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

