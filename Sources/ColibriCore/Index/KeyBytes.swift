//
//  KeyBytes.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Key encoding toolkit shaping bytes for ordered indexes.

import Foundation
/// Encodes typed values into lexicographically comparable bytes for B+Tree keys.

// Encodes Value into lexicographically comparable bytes with a type tag
// Order: null < bool(false) < bool(true) < int < double < string
// Int: map signed Int64 to big-endian unsigned by adding 2^63
// Double: IEEE 754 big-endian; flip sign bit for positive, invert all bits for negative

public struct KeyBytes: Hashable, Comparable {
    public let bytes: Data

    public init(_ bytes: Data) { self.bytes = bytes }

    public func hash(into hasher: inout Hasher) {
        hasher.combine(SIMDOptimizations.hashBytes(bytes))
    }

    /// Encodes a single Value into key bytes with a leading type tag.
    public static func fromValue(_ v: Value) -> KeyBytes {
        switch v {
        case .null:
            return KeyBytes(Data([0x00]))
        case .bool(let b):
            return KeyBytes(Data([0x01, b ? 0x01 : 0x00]))
        case .int(let i):
            let u = UInt64(bitPattern: i &+ Int64(bitPattern: 0x8000_0000_0000_0000))
            var be = withUnsafeBytes(of: u.bigEndian) { Data($0) }
            be.insert(0x02, at: 0)
            return KeyBytes(be)
        case .double(let d):
            var bits = d.bitPattern
            // Transform to lex-order-preserving
            if (bits & (1 << 63)) != 0 { // negative
                bits = ~bits
            } else {
                bits ^= (1 << 63)
            }
            var be = withUnsafeBytes(of: bits.bigEndian) { Data($0) }
            be.insert(0x03, at: 0)
            return KeyBytes(be)
        case .string(let s):
            var d = Data([0x04])
            d.append(s.data(using: .utf8) ?? Data())
            return KeyBytes(d)
        case .decimal(let d):
            // Convert decimal to double for lexicographic ordering
            let doubleValue = Double(truncating: d as NSNumber)
            return fromValue(.double(doubleValue))
        case .date(let d):
            // Use timestamp for lexicographic ordering  
            let timestamp = d.timeIntervalSince1970
            return fromValue(.double(timestamp))
        }
    }

    /// Encodes a composite of Values into key bytes with length prefixes.
    public static func fromValues(_ values: [Value]) -> KeyBytes {
        var out = Data()
        out.append(0xFE) // composite tag
        for v in values {
            let kb = fromValue(v).bytes
            out.append(VarInt.encode(UInt64(kb.count)))
            out.append(kb)
        }
        out.append(0xFF) // end marker
        return KeyBytes(out)
    }

    public static func < (lhs: KeyBytes, rhs: KeyBytes) -> Bool {
        return lhs.bytes.lexicographicallyPrecedes(rhs.bytes)
    }
}

// Simple ULEB128 for lengths
/// Minimal ULEB128 codec for length prefixes used in key encoding.
enum VarInt {
    static func encode(_ v: UInt64) -> Data {
        var n = v
        var out = Data()
        while true {
            var b = UInt8(n & 0x7F)
            n >>= 7
            if n != 0 { b |= 0x80 }
            out.append(b)
            if n == 0 { break }
        }
        return out
    }
    static func decode(_ data: Data, offset: inout Int) -> UInt64 {
        var result: UInt64 = 0
        var shift: UInt64 = 0
        while offset < data.count {
            let b = data[offset]; offset += 1
            result |= UInt64(b & 0x7F) << shift
            if (b & 0x80) == 0 { break }
            shift += 7
        }
        return result
    }

    /// Returns the number of bytes required to encode `v`.
    static func encodedSize(_ v: UInt64) -> Int {
        var n = v
        var bytes = 1
        while n >= 0x80 {
            bytes &+= 1
            n >>= 7
        }
        return bytes
    }

    /// Encodes `v` directly into `data` starting at `cursor`, advancing it.
    static func write(_ v: UInt64, into data: inout Data, cursor: inout Int) {
        var n = v
        repeat {
            var byte = UInt8(n & 0x7F)
            n >>= 7
            if n != 0 { byte |= 0x80 }
            data[cursor] = byte
            cursor &+= 1
        } while n != 0
    }
}

// MARK: - Decoders (best-effort)
extension KeyBytes {
    public static func toSingleValue(_ data: Data) -> Value? {
        guard !data.isEmpty else { return nil }
        let t = data[0]
        let payload = data.dropFirst()
        switch t {
        case 0x00:
            return .null
        case 0x01:
            if let b = payload.first { return .bool(b != 0) }
        case 0x02:
            if payload.count >= 8 {
                let u = payload.withUnsafeBytes { $0.load(as: UInt64.self) }.bigEndian
                let i = Int64(bitPattern: u) &- Int64(bitPattern: 0x8000_0000_0000_0000)
                return .int(i)
            }
        case 0x03:
            if payload.count >= 8 {
                var bits = payload.withUnsafeBytes { $0.load(as: UInt64.self) }.bigEndian
                // invert transform
                if (bits & (1 << 63)) != 0 { bits ^= (1 << 63) } else { bits = ~bits }
                let d = Double(bitPattern: bits)
                return .double(d)
            }
        case 0x04:
            return .string(String(data: payload, encoding: .utf8) ?? "")
        case 0xFE:
            // composite marker; unsupported in single
            return nil
        default:
            return nil
        }
        return nil
    }

    public static func toValues(_ data: Data, count: Int) -> [Value]? {
        var vals: [Value] = []
        if data.first == 0xFE {
            var off = 1
            while off < data.count && data[off] != 0xFF && vals.count < count {
                let len = Int(VarInt.decode(data, offset: &off))
                if off + len > data.count { return nil }
                let slice = data.subdata(in: off..<(off+len)); off += len
                if let v = toSingleValue(slice) { vals.append(v) } else { return nil }
            }
            return vals.count == count ? vals : nil
        }
        // Fallback: try decode as count singles concatenated
        var off = 0
        while off < data.count && vals.count < count {
            let t = data[off]; off += 1
            switch t {
            case 0x00:
                vals.append(.null)
            case 0x01:
                if off < data.count { vals.append(.bool(data[off] != 0)); off += 1 } else { return nil }
            case 0x02:
                if off + 8 <= data.count {
                    let u = data.subdata(in: off..<(off+8)).withUnsafeBytes { $0.load(as: UInt64.self) }.bigEndian
                    let i = Int64(bitPattern: u) &- Int64(bitPattern: 0x8000_0000_0000_0000)
                    vals.append(.int(i)); off += 8
                } else { return nil }
            case 0x03:
                if off + 8 <= data.count {
                    var bits = data.subdata(in: off..<(off+8)).withUnsafeBytes { $0.load(as: UInt64.self) }.bigEndian
                    if (bits & (1 << 63)) != 0 { bits ^= (1 << 63) } else { bits = ~bits }
                    vals.append(.double(Double(bitPattern: bits))); off += 8
                } else { return nil }
            case 0x04:
                let rest = data.suffix(from: off)
                vals.append(.string(String(data: rest, encoding: .utf8) ?? ""))
                off = data.count
            default:
                return nil
            }
        }
        return vals.count == count ? vals : nil
    }
}
