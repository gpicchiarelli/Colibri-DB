//
//  FileBPlusTreeIndex+IO.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrDB — BSD 3-Clause License

// Theme: B+Tree IO chants translating nodes to pages and back.

import Foundation

extension FileBPlusTreeIndex {
    // MARK: - Low-level IO

    static func readHeader(handle: FileHandle, pageSize: Int) throws -> Header {
        try handle.seek(toOffset: 0)
        let d = try handle.read(upToCount: pageSize) ?? Data()
        let magic = String(data: d.subdata(in: 0..<4), encoding: .utf8)
        guard magic == "CBPT" else { throw DBError.io("Invalid index header magic") }
        var off = 4
        _ = d.subdata(in: off..<(off+2)).withUnsafeBytes { $0.load(as: UInt16.self) }.bigEndian; off += 2
        let ps = d.subdata(in: off..<(off+4)).withUnsafeBytes { $0.load(as: UInt32.self) }.bigEndian; off += 4
        let root = d.subdata(in: off..<(off+8)).withUnsafeBytes { $0.load(as: UInt64.self) }.bigEndian; off += 8
        let next = d.subdata(in: off..<(off+8)).withUnsafeBytes { $0.load(as: UInt64.self) }.bigEndian; off += 8
        let chk: UInt64 = d.count >= off + 8 ? d.subdata(in: off..<(off+8)).withUnsafeBytes { $0.load(as: UInt64.self) }.bigEndian : 0
        return Header(pageSize: Int(ps), root: root, nextPage: next, checkpointLSN: chk)
    }

    func writeHeader() throws {
        var d = Data()
        d.append(Data("CBPT".utf8))
        var ver: UInt16 = 1
        var ps = UInt32(pageSize).bigEndian
        var root = hdr.root.bigEndian
        var next = hdr.nextPage.bigEndian
        var chk = hdr.checkpointLSN.bigEndian
        d.append(Data(bytes: &ver, count: 2))
        d.append(Data(bytes: &ps, count: 4))
        d.append(Data(bytes: &root, count: 8))
        d.append(Data(bytes: &next, count: 8))
        d.append(Data(bytes: &chk, count: 8))
        if d.count < pageSize { d.append(Data(repeating: 0, count: pageSize - d.count)) }
        try fh.seek(toOffset: 0)
        try fh.write(contentsOf: d)
    }

    func allocPage() throws -> UInt64 {
        let id = hdr.nextPage
        hdr.nextPage += 1
        try writeHeader()
        return id
    }

    func readPage(_ pageId: UInt64) throws -> (type: UInt8, data: Data) {
        let off = UInt64(pageSize) * pageId
        if let b = buf { 
            let data = try b.getPage(pageId)
            return (type: data[0], data: data)
        }
        try fh.seek(toOffset: off)
        guard let d = try fh.read(upToCount: pageSize), d.count == pageSize else { throw DBError.io("Short read page \(pageId)") }
        let type = d[0]
        return (type, d)
    }

    func writeInternal(pageId: UInt64, keys: [Data], children: [UInt64], pageLSN: UInt64 = 0) throws {
        precondition(children.count == keys.count + 1, "Internal node children mismatch")
        var d = Data(count: pageSize)
        d[0] = 1
        var keyCountBE = UInt16(keys.count).bigEndian
        d.replaceSubrange(1..<3, with: withUnsafeBytes(of: &keyCountBE) { Data($0) })
        var rawChildCount = UInt16(children.count)
        let usePrefix = !keys.isEmpty
        if usePrefix { rawChildCount |= InternalFlag.prefixCompressed }
        var childCountBE = rawChildCount.bigEndian
        d.replaceSubrange(3..<5, with: withUnsafeBytes(of: &childCountBE) { Data($0) })
        var lsnBE = pageLSN.bigEndian
        d.replaceSubrange(8..<(8+8), with: withUnsafeBytes(of: &lsnBE) { Data($0) })
        var cursor = 16
        var firstChild = children[0].bigEndian
        d.replaceSubrange(cursor..<(cursor+8), with: withUnsafeBytes(of: &firstChild) { Data($0) }); cursor += 8
        var base = Data()
        var prevSuffix = Data()
        if usePrefix {
            base = commonPrefixAll(keys)
            VarInt.write(UInt64(base.count), into: &d, cursor: &cursor)
            if !base.isEmpty {
                d.replaceSubrange(cursor..<(cursor+base.count), with: base)
                cursor += base.count
            }
        }
        for i in 0..<keys.count {
            let k = keys[i]
            if usePrefix {
                try writeCompressedKey(k, base: base, prevSuffix: &prevSuffix, into: &d, cursor: &cursor)
            } else {
                VarInt.write(UInt64(k.count), into: &d, cursor: &cursor)
                d.replaceSubrange(cursor..<(cursor+k.count), with: k)
                cursor += k.count
            }
            var child = children[i+1].bigEndian
            d.replaceSubrange(cursor..<(cursor+8), with: withUnsafeBytes(of: &child) { Data($0) }); cursor += 8
        }
        if cursor > pageSize { throw DBError.io("Internal page overflow") }
        if let b = buf {
            try b.putPage(pageId, data: d, dirty: true)
        } else {
            try fh.seek(toOffset: UInt64(pageSize) * pageId)
            try fh.write(contentsOf: d)
        }
    }

    func writeLeaf(pageId: UInt64, keys: [Data], ridLists: [[RID]], nextLeaf: UInt64, pageLSN: UInt64 = 0) throws {
        precondition(keys.count == ridLists.count, "Leaf key/rid mismatch")
        let data = try serializeLeaf(keys: keys, ridLists: ridLists, nextLeaf: nextLeaf, pageLSN: pageLSN, compressed: false)
        try writeLeafPage(pageId: pageId, data: data)
    }

    private func writeLeafPage(pageId: UInt64, data: Data) throws {
        if let b = buf {
            try b.putPage(pageId, data: data, dirty: true)
        } else {
            try fh.seek(toOffset: UInt64(pageSize) * pageId)
            try fh.write(contentsOf: data)
        }
    }

    private func serializeLeaf(keys: [Data], ridLists: [[RID]], nextLeaf: UInt64, pageLSN: UInt64, compressed: Bool) throws -> Data {
        var d = Data(count: pageSize)
        d[0] = 2
        var keyCountBE = UInt16(keys.count).bigEndian
        d.replaceSubrange(1..<3, with: withUnsafeBytes(of: &keyCountBE) { Data($0) })
        var lsnBE = pageLSN.bigEndian
        d.replaceSubrange(8..<(8+8), with: withUnsafeBytes(of: &lsnBE) { Data($0) })
        var nextBE = nextLeaf.bigEndian
        d.replaceSubrange(16..<(16+8), with: withUnsafeBytes(of: &nextBE) { Data($0) })
        var cursor = 24
        var flags: UInt8 = 0

        func writeVarIntChecked(_ value: UInt64) throws {
            let bytes = VarInt.encode(value)
            if cursor + bytes.count > pageSize { throw DBError.io("Leaf serialization overflow") }
            d.replaceSubrange(cursor..<(cursor+bytes.count), with: bytes)
            cursor += bytes.count
        }

        func writeBytes(_ bytes: Data) throws {
            if bytes.isEmpty { return }
            if cursor + bytes.count > pageSize { throw DBError.io("Leaf serialization overflow") }
            d.replaceSubrange(cursor..<(cursor+bytes.count), with: bytes)
            cursor += bytes.count
        }

        if compressed && !keys.isEmpty {
            flags = LeafFlag.prefixCompressed | LeafFlag.prefixCompressedV2 | LeafFlag.ridDeltaEncoded
            let base = commonPrefixAll(keys)
            try writeVarIntChecked(UInt64(base.count))
            try writeBytes(base)
            var prevSuffix = Data()
            for i in 0..<keys.count {
                let key = keys[i]
                try writeCompressedKey(key, base: base, prevSuffix: &prevSuffix, into: &d, cursor: &cursor)
                try writeRIDList(ridLists[i], into: &d, cursor: &cursor, deltaEncoded: true)
            }
        } else {
            flags = 0
            for i in 0..<keys.count {
                let key = keys[i]
                try writeVarIntChecked(UInt64(key.count))
                try writeBytes(key)
                try writeRIDList(ridLists[i], into: &d, cursor: &cursor, deltaEncoded: false)
            }
        }

        d[3] = flags
        if cursor > pageSize { throw DBError.io("Leaf serialization overflow") }
        return d
    }

    func parseInternal(_ d: Data) throws -> (keys: [Data], children: [UInt64]) {
        let keyCount = Int(d.subdata(in: 1..<3).withUnsafeBytes { $0.load(as: UInt16.self) }.bigEndian)
        let rawChild = d.subdata(in: 3..<5).withUnsafeBytes { $0.load(as: UInt16.self) }.bigEndian
        let prefixEnabled = (rawChild & InternalFlag.prefixCompressed) != 0
        let childCount = Int(rawChild & InternalFlag.countMask)
        guard childCount == keyCount + 1 else { throw DBError.io("Internal page child count mismatch") }
        var cursor = 16
        var children: [UInt64] = []
        var keys: [Data] = []
        let firstChild = d.subdata(in: cursor..<(cursor+8)).withUnsafeBytes { $0.load(as: UInt64.self) }.bigEndian; cursor += 8
        children.append(firstChild)
        if prefixEnabled {
            let baseLen = Int(VarInt.decode(d, offset: &cursor))
            let base: Data
            if baseLen > 0 {
                base = d.subdata(in: cursor..<(cursor+baseLen))
                cursor += baseLen
            } else {
                base = Data()
            }
            var prevSuffix = Data()
            for _ in 0..<keyCount {
                let cp = Int(VarInt.decode(d, offset: &cursor))
                let suffixLen = Int(VarInt.decode(d, offset: &cursor))
                var suffix = Data()
                if cp > 0 { suffix.append(prevSuffix.prefix(cp)) }
                if suffixLen > 0 {
                    suffix.append(d.subdata(in: cursor..<(cursor+suffixLen)))
                    cursor += suffixLen
                }
                var full = Data()
                full.append(base)
                full.append(suffix)
                keys.append(full)
                prevSuffix = suffix
                let child = d.subdata(in: cursor..<(cursor+8)).withUnsafeBytes { $0.load(as: UInt64.self) }.bigEndian; cursor += 8
                children.append(child)
            }
        } else {
            for _ in 0..<keyCount {
                let len = Int(VarInt.decode(d, offset: &cursor))
                let key = d.subdata(in: cursor..<(cursor+len)); cursor += len
                let child = d.subdata(in: cursor..<(cursor+8)).withUnsafeBytes { $0.load(as: UInt64.self) }.bigEndian; cursor += 8
                keys.append(key)
                children.append(child)
            }
        }
        return (keys, children)
    }

    func parseLeaf(_ d: Data) throws -> (keys: [Data], ridLists: [[RID]], nextLeaf: UInt64) {
        let keyCount = Int(d.subdata(in: 1..<3).withUnsafeBytes { $0.load(as: UInt16.self) }.bigEndian)
        let flags = d[3]
        let nextLeaf = d.subdata(in: 16..<(16+8)).withUnsafeBytes { $0.load(as: UInt64.self) }.bigEndian
        var cursor = 24
        var keys: [Data] = []
        var rlists: [[RID]] = []
        if (flags & LeafFlag.prefixCompressedV2) != 0 {
            let baseLen = Int(VarInt.decode(d, offset: &cursor))
            let base: Data
            if baseLen > 0 {
                guard cursor + baseLen <= d.count else { throw DBError.io("Leaf decode base overflow") }
                base = d.subdata(in: cursor..<(cursor+baseLen))
                cursor += baseLen
            } else {
                base = Data()
            }
            var prevSuffix = Data()
            for _ in 0..<keyCount {
                let cp = Int(VarInt.decode(d, offset: &cursor))
                let suffixLen = Int(VarInt.decode(d, offset: &cursor))
                guard cp >= 0 && suffixLen >= 0 else { throw DBError.io("Leaf decode negative lengths") }
                var suffix = Data()
                if cp > 0 { suffix.append(prevSuffix.prefix(cp)) }
                if suffixLen > 0 {
                    guard cursor + suffixLen <= d.count else { throw DBError.io("Leaf decode suffix overflow") }
                    suffix.append(d.subdata(in: cursor..<(cursor+suffixLen)))
                    cursor += suffixLen
                }
                var full = Data()
                full.append(base)
                full.append(suffix)
                keys.append(full)
                prevSuffix = suffix
                let rids = try decodeRIDList(d, cursor: &cursor, deltaEncoded: true)
                rlists.append(rids)
            }
        } else if (flags & LeafFlag.prefixCompressed) != 0 {
            var prev = Data()
            for _ in 0..<keyCount {
                let cp = Int(VarInt.decode(d, offset: &cursor))
                let sl = Int(VarInt.decode(d, offset: &cursor))
                guard cp >= 0 && sl >= 0 else { throw DBError.io("Leaf decode negative lengths") }
                guard cursor + sl <= d.count else { throw DBError.io("Leaf decode prefix overflow") }
                let suffix = d.subdata(in: cursor..<(cursor+sl)); cursor += sl
                var full = Data()
                if cp > 0 { full.append(prev.prefix(cp)) }
                full.append(suffix)
                let rids = try decodeRIDList(d, cursor: &cursor, deltaEncoded: false)
                keys.append(full)
                rlists.append(rids)
                prev = full
            }
        } else {
            for _ in 0..<keyCount {
                let len = Int(VarInt.decode(d, offset: &cursor))
                guard len >= 0 && cursor + len <= d.count else { throw DBError.io("Leaf decode plain overflow") }
                let k = d.subdata(in: cursor..<(cursor+len)); cursor += len
                let rids = try decodeRIDList(d, cursor: &cursor, deltaEncoded: false)
                keys.append(k)
                rlists.append(rids)
            }
        }
        return (keys, rlists, nextLeaf)
    }

    func commonPrefix(_ a: Data, _ b: Data) -> Int {
        SIMDOptimizations.commonPrefixLength(a, b)
    }

    func commonPrefixAll(_ keys: [Data]) -> Data {
        guard var prefix = keys.first else { return Data() }
        for key in keys.dropFirst() {
            let len = commonPrefix(prefix, key)
            if len == 0 { return Data() }
            prefix = prefix.subdata(in: 0..<len)
        }
        return prefix
    }

    func writeCompressedKey(_ key: Data, base: Data, prevSuffix: inout Data, into data: inout Data, cursor: inout Int) throws {
        let baseLen = base.count
        let suffix: Data
        if baseLen < key.count {
            suffix = key.subdata(in: baseLen..<key.count)
        } else {
            suffix = Data()
        }
        let cp = commonPrefix(prevSuffix, suffix)
        let cpBytes = VarInt.encode(UInt64(cp))
        if cursor + cpBytes.count > pageSize { throw DBError.io("Leaf serialization overflow") }
        data.replaceSubrange(cursor..<(cursor+cpBytes.count), with: cpBytes)
        cursor += cpBytes.count
        let suffixTailLen = suffix.count - cp
        let suffixBytes = VarInt.encode(UInt64(suffixTailLen))
        if cursor + suffixBytes.count > pageSize { throw DBError.io("Leaf serialization overflow") }
        data.replaceSubrange(cursor..<(cursor+suffixBytes.count), with: suffixBytes)
        cursor += suffixBytes.count
        if suffixTailLen > 0 {
            let tail = suffix.subdata(in: cp..<suffix.count)
            if cursor + tail.count > pageSize { throw DBError.io("Leaf serialization overflow") }
            data.replaceSubrange(cursor..<(cursor+tail.count), with: tail)
            cursor += tail.count
        }
        prevSuffix = suffix
    }

    func writeRIDList(_ rids: [RID], into data: inout Data, cursor: inout Int, deltaEncoded: Bool) throws {
        if !deltaEncoded {
            let countBytes = VarInt.encode(UInt64(rids.count))
            if cursor + countBytes.count > pageSize { throw DBError.io("Leaf serialization overflow") }
            data.replaceSubrange(cursor..<(cursor+countBytes.count), with: countBytes)
            cursor += countBytes.count
            for rid in rids {
                var pid = rid.pageId.bigEndian
                var sid = rid.slotId.bigEndian
                if cursor + 8 > pageSize { throw DBError.io("Leaf serialization overflow") }
                data.replaceSubrange(cursor..<(cursor+8), with: withUnsafeBytes(of: &pid) { Data($0) }); cursor += 8
                if cursor + 2 > pageSize { throw DBError.io("Leaf serialization overflow") }
                data.replaceSubrange(cursor..<(cursor+2), with: withUnsafeBytes(of: &sid) { Data($0) }); cursor += 2
            }
            return
        }
        let sorted = rids.sorted { lhs, rhs in
            if lhs.pageId == rhs.pageId { return lhs.slotId < rhs.slotId }
            return lhs.pageId < rhs.pageId
        }
        let countBytes = VarInt.encode(UInt64(sorted.count))
        if cursor + countBytes.count > pageSize { throw DBError.io("Leaf serialization overflow") }
        data.replaceSubrange(cursor..<(cursor+countBytes.count), with: countBytes)
        cursor += countBytes.count
        guard let first = sorted.first else { return }
        let firstPageBytes = VarInt.encode(first.pageId)
        if cursor + firstPageBytes.count > pageSize { throw DBError.io("Leaf serialization overflow") }
        data.replaceSubrange(cursor..<(cursor+firstPageBytes.count), with: firstPageBytes)
        cursor += firstPageBytes.count
        let firstSlotBytes = VarInt.encode(UInt64(first.slotId))
        if cursor + firstSlotBytes.count > pageSize { throw DBError.io("Leaf serialization overflow") }
        data.replaceSubrange(cursor..<(cursor+firstSlotBytes.count), with: firstSlotBytes)
        cursor += firstSlotBytes.count
        var prev = first
        for rid in sorted.dropFirst() {
            let pageDelta = rid.pageId &- prev.pageId
            let pageBytes = VarInt.encode(pageDelta)
            if cursor + pageBytes.count > pageSize { throw DBError.io("Leaf serialization overflow") }
            data.replaceSubrange(cursor..<(cursor+pageBytes.count), with: pageBytes)
            cursor += pageBytes.count
            let slotDelta: UInt64 = (pageDelta == 0) ? UInt64(rid.slotId &- prev.slotId) : UInt64(rid.slotId)
            let slotBytes = VarInt.encode(slotDelta)
            if cursor + slotBytes.count > pageSize { throw DBError.io("Leaf serialization overflow") }
            data.replaceSubrange(cursor..<(cursor+slotBytes.count), with: slotBytes)
            cursor += slotBytes.count
            prev = rid
        }
    }

    func decodeRIDList(_ data: Data, cursor: inout Int, deltaEncoded: Bool) throws -> [RID] {
        let rc = Int(VarInt.decode(data, offset: &cursor))
        guard rc >= 0 else { throw DBError.io("Negative RID count") }
        if rc == 0 { return [] }
        if !deltaEncoded {
            var rids: [RID] = []
            rids.reserveCapacity(rc)
            for _ in 0..<rc {
                guard cursor + 10 <= data.count else { throw DBError.io("RID decode overflow") }
                let pid = data.subdata(in: cursor..<(cursor+8)).withUnsafeBytes { $0.load(as: UInt64.self) }.bigEndian; cursor += 8
                let sid = data.subdata(in: cursor..<(cursor+2)).withUnsafeBytes { $0.load(as: UInt16.self) }.bigEndian; cursor += 2
                rids.append(RID(pageId: pid, slotId: sid))
            }
            return rids
        }
        var rids: [RID] = []
        rids.reserveCapacity(rc)
        let firstPage = VarInt.decode(data, offset: &cursor)
        let firstSlot = VarInt.decode(data, offset: &cursor)
        guard firstSlot <= UInt64(UInt16.max) else { throw DBError.io("RID slot overflow") }
        var prev = RID(pageId: firstPage, slotId: UInt16(firstSlot))
        rids.append(prev)
        if rc == 1 { return rids }
        for _ in 1..<rc {
            let pageDelta = VarInt.decode(data, offset: &cursor)
            let slotDelta = VarInt.decode(data, offset: &cursor)
            let pageId = prev.pageId &+ pageDelta
            let slotValue: UInt64
            if pageDelta == 0 {
                slotValue = UInt64(prev.slotId) &+ slotDelta
            } else {
                slotValue = slotDelta
            }
            guard slotValue <= UInt64(UInt16.max) else { throw DBError.io("RID slot overflow") }
            let rid = RID(pageId: pageId, slotId: UInt16(slotValue))
            rids.append(rid)
            prev = rid
        }
        return rids
    }
}
