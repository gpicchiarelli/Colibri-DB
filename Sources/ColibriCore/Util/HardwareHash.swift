//
//  HardwareHash.swift
//  Deterministic, hardware-accelerated hashing on Apple Silicon using CryptoKit
//

import Foundation
import CryptoKit

public enum HardwareHash {
    /// Hash arbitrary `Value` into a 64-bit integer using SHA256 (hardware-accelerated on Apple Silicon).
    /// The result is deterministic across runs and platforms for the same serialized value and seed.
    public static func hash64(_ value: Value, seed: UInt64 = 0) -> UInt64 {
        // SHA256 is chosen for robustness and availability of HW acceleration via CryptoKit on Apple Silicon.
        // We fold the digest down to 64 bits to fit typical index/bloom filter usage (fast and compact).
        var hasher = SHA256()
        // Incorporate a caller-provided seed to allow multiple independent hash families.
        // Use little-endian to keep a stable cross-platform byte order.
        var seedLE = seed.littleEndian
        withUnsafeBytes(of: &seedLE) { seedPtr in
            hasher.update(data: Data(seedPtr))
        }
        // Serialize the typed value into a stable byte representation and feed it to the hasher.
        hasher.update(data: serialize(value))
        let digest = hasher.finalize()
        // Reduce 256-bit digest to 64 bits: take the first 8 bytes.
        // Note: Using a different folding (e.g., XOR of 4 limbs) is also possible; prefix is fine here.
        let bytes = Array(digest.prefix(8))
        return bytes.withUnsafeBytes { ptr in
            // Load as UInt64 (host endianness). Callers should normalize endianness if needed for I/O.
            return ptr.load(as: UInt64.self)
        }
    }
    
    /// Return two independent 64-bit hashes derived from a single SHA256 digest.
    /// Useful for Bloom filter double hashing: h(i) = h1 + i*h2
    public static func hash64x2(_ value: Value, seed: UInt64 = 0) -> (UInt64, UInt64) {
        // Single digest → two 64-bit lanes to avoid computing two separate hashes.
        var hasher = SHA256()
        var seedLE = seed.littleEndian
        withUnsafeBytes(of: &seedLE) { seedPtr in
            hasher.update(data: Data(seedPtr))
        }
        hasher.update(data: serialize(value))
        let digest = hasher.finalize()
        let bytes = Array(digest.prefix(16))
        let h1: UInt64 = bytes[0..<8].withUnsafeBytes { $0.load(as: UInt64.self) }
        var h2: UInt64 = bytes[8..<16].withUnsafeBytes { $0.load(as: UInt64.self) }
        // Ensure h2 is odd to improve cycle coverage when used with modulo (avoids even-step cycles).
        if h2 % 2 == 0 { h2 &+= 1 }
        return (h1, h2)
    }
    
    private static func serialize(_ value: Value) -> Data {
        // Stable, explicit serialization per variant to guarantee cross-platform determinism.
        switch value {
        case .int(let v):
            var x = v.littleEndian
            return withUnsafeBytes(of: &x) { Data($0) }
        case .double(let v):
            var x = v.bitPattern.littleEndian
            return withUnsafeBytes(of: &x) { Data($0) }
        case .string(let v):
            return Data(v.utf8)
        case .bool(let v):
            return Data([v ? 1 : 0])
        case .date(let v):
            var t = v.timeIntervalSince1970.bitPattern.littleEndian
            return withUnsafeBytes(of: &t) { Data($0) }
        case .null:
            // Sentinel byte for null to disambiguate from other zero-length encodings.
            return Data([0xFF])
        case .decimal(let v):
            // Use string representation for determinism
            return Data(v.description.utf8)
        case .bytes(let v):
            return v
        }
    }
}


