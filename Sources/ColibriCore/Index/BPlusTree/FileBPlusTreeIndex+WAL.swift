//
//  FileBPlusTreeIndex+WAL.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrìDB — BSD 3-Clause License

// Theme: B+Tree WAL hymns recording structural mutations.

import Foundation

extension FileBPlusTreeIndex {
    // MARK: - WAL support

    static func ensureWALHeader(handle: FileHandle) throws {
        if try handle.seekToEnd() == 0 {
            var d = Data()
            d.append(Data("CBWL".utf8))
            var ver: UInt16 = 1
            var res: UInt16 = 0
            d.append(Data(bytes: &ver, count: 2))
            d.append(Data(bytes: &res, count: 2))
            try handle.write(contentsOf: d)
            try handle.synchronize()
        }
    }

    func walAppendInsert(key: Data, rid: RID) throws -> UInt64 {
        try walAppendRecord(type: 1, payload: walPayload(key: key, rid: rid))
    }

    func walAppendDelete(key: Data, rid: RID) throws -> UInt64 {
        try walAppendRecord(type: 2, payload: walPayload(key: key, rid: rid))
    }

    func walAppendCheckpoint() throws {
        let lsn = try walAppendRecord(type: 3, payload: Data())
        hdr.checkpointLSN = lsn
        try writeHeader()
    }

    public func checkpointIndex() throws {
        try buf?.flushAll()
        try walAppendCheckpoint()
        try clearWAL()
    }

    public func flushBuffers(fullSync: Bool = false) throws {
        let span = Signpost.begin(.flush, name: "IndexFlush", message: URL(fileURLWithPath: path).lastPathComponent)
        defer { Signpost.end(span, message: fullSync ? "fullsync" : "fsync") }
        try buf?.flushAll()
        try IOHints.synchronize(handle: fh, full: fullSync)
    }

    func walPayload(key: Data, rid: RID) -> Data {
        var p = Data()
        p.append(VarInt.encode(UInt64(key.count)))
        p.append(key)
        var pid = rid.pageId.bigEndian
        var sid = rid.slotId.bigEndian
        p.append(Data(bytes: &pid, count: 8))
        p.append(Data(bytes: &sid, count: 2))
        return p
    }

    func walAppendRecord(type: UInt8, payload: Data) throws -> UInt64 {
        try FileBPlusTreeIndex.ensureWALHeader(handle: walFH)
        try walFH.seekToEnd()
        var rec = Data([type])
        let lsn = nextLSN
        var lsnBE = lsn.bigEndian
        rec.append(Data(bytes: &lsnBE, count: 8))
        rec.append(payload)
        let crc = CRC32.compute(rec)
        var crcBE = crc.bigEndian
        var out = Data()
        out.append(Data(bytes: &crcBE, count: 4))
        out.append(rec)
        try walFH.write(contentsOf: out)
        try syncWAL()
        nextLSN &+= 1
        opsSinceCheckpoint += 1
        if opsSinceCheckpoint >= checkpointEvery {
            try walAppendCheckpoint()
            opsSinceCheckpoint = 0
        }
        return lsn
    }

    func clearWAL() throws {
        try walFH.truncate(atOffset: 0)
        try walFH.seek(toOffset: 0)
        try FileBPlusTreeIndex.ensureWALHeader(handle: walFH)
        try syncWAL()
    }

    func replayWAL() throws {
        if ioHintsEnabled {
            let length = try walFH.seekToEnd()
            if length > 0 {
                IOHints.prepareSequentialRead(handle: walFH, length: UInt64(length))
            }
        }
        try walFH.seek(toOffset: 0)
        let data = try walFH.readToEnd() ?? Data()
        var off = 0
        if data.count >= 8, String(data: data.subdata(in: 0..<4), encoding: .utf8) == "CBWL" {
            off = 8
            var lastLSN: UInt64 = 0
            while off + 4 <= data.count {
                let crcStored = data.subdata(in: off..<(off+4)).withUnsafeBytes { $0.load(as: UInt32.self) }.bigEndian
                off += 4
                if off >= data.count { break }
                let type = data[off]; off += 1
                if off + 8 > data.count { break }
                let lsn = data.subdata(in: off..<(off+8)).withUnsafeBytes { $0.load(as: UInt64.self) }.bigEndian
                off += 8
                switch type {
                case 1, 2:
                    let startPayload = off
                    let keyLen = Int(VarInt.decode(data, offset: &off))
                    if off + keyLen + 10 > data.count { off = data.count; break }
                    let key = data.subdata(in: off..<(off+keyLen)); off += keyLen
                    let pid = data.subdata(in: off..<(off+8)).withUnsafeBytes { $0.load(as: UInt64.self) }.bigEndian; off += 8
                    let sid = data.subdata(in: off..<(off+2)).withUnsafeBytes { $0.load(as: UInt16.self) }.bigEndian; off += 2
                    var rec = Data([type])
                    var lsnBE = lsn.bigEndian
                    rec.append(Data(bytes: &lsnBE, count: 8))
                    rec.append(data.subdata(in: startPayload..<off))
                    let crcCalc = CRC32.compute(rec)
                    if crcCalc != crcStored { break }
                    if hdr.root == 0 {
                        let leaf = try allocPage()
                        try writeLeaf(pageId: leaf, keys: [], ridLists: [], nextLeaf: 0, pageLSN: lsn)
                        hdr.root = leaf
                        try writeHeader()
                    }
                    if type == 1 {
                        _ = try? insertRecursive(pageId: hdr.root, key: key, rid: RID(pageId: pid, slotId: sid), lsn: lsn)
                    } else {
                        try? removeBytesKey(key, rid: RID(pageId: pid, slotId: sid), lsn: lsn)
                    }
                    lastLSN = max(lastLSN, lsn)
                case 3:
                    lastLSN = max(lastLSN, lsn)
                default:
                    off = data.count
                }
            }
            nextLSN = lastLSN &+ 1
        } else {
            off = 0
            while off < data.count {
                let op = data[off]; off += 1
                if op == 1 {
                    let len = Int(VarInt.decode(data, offset: &off))
                    if off + len + 10 > data.count { break }
                    let key = data.subdata(in: off..<(off+len)); off += len
                    let pid = data.subdata(in: off..<(off+8)).withUnsafeBytes { $0.load(as: UInt64.self) }.bigEndian; off += 8
                    let sid = data.subdata(in: off..<(off+2)).withUnsafeBytes { $0.load(as: UInt16.self) }.bigEndian; off += 2
                    if hdr.root == 0 {
                        let leaf = try allocPage()
                        try writeLeaf(pageId: leaf, keys: [], ridLists: [], nextLeaf: 0, pageLSN: 0)
                        hdr.root = leaf
                        try writeHeader()
                    }
                    _ = try? insertRecursive(pageId: hdr.root, key: key, rid: RID(pageId: pid, slotId: sid), lsn: 0)
                } else { break }
            }
        }
        if data.count > 8 { try clearWAL() }
    }

    private func syncWAL() throws {
        try IOHints.synchronize(handle: walFH, full: walFullSyncEnabled)
    }
}
