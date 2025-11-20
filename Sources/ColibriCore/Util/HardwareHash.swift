//
//  HardwareHash.swift
//  Deterministic, hardware-accelerated hashing on Apple Silicon using CryptoKit
//

import Foundation
import CryptoKit

public enum HardwareHash {
    public enum Backend: Sendable {
        case sha256
        case xxhash64
    }
    
    /// Default backend used when not specified explicitly.
    /// - For compatibility, we keep SHA-256 as default.
    public static let defaultBackend: Backend = .sha256
    
    /// Hash arbitrary `Value` into a 64-bit integer using SHA256 (hardware-accelerated on Apple Silicon).
    /// The result is deterministic across runs and platforms for the same serialized value and seed.
    public static func hash64(_ value: Value, seed: UInt64 = 0) -> UInt64 {
        // SHA256 is chosen for robustness and availability of HW acceleration via CryptoKit on Apple Silicon.
        // We fold the digest down to 64 bits to fit typical index/bloom filter usage (fast and compact).
        // NOTE: This overload preserves previous behavior (SHA-256 based).
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
        // Reduce 256-bit digest to 64 bits: take the first 8 bytes without allocating.
        let result: UInt64 = digest.withUnsafeBytes { rawPtr in
            precondition(rawPtr.count >= 8)
            // Load unaligned first 8 bytes
            let v = rawPtr.loadUnaligned(as: UInt64.self)
            return v
        }
        // Normalize to little-endian for portability across hosts.
        return result.littleEndian
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
        // Read two 64-bit lanes directly from the digest without intermediate arrays.
        let (rawH1, rawH2): (UInt64, UInt64) = digest.withUnsafeBytes { rawPtr in
            precondition(rawPtr.count >= 16)
            let h1 = rawPtr.loadUnaligned(fromByteOffset: 0, as: UInt64.self)
            let h2 = rawPtr.loadUnaligned(fromByteOffset: 8, as: UInt64.self)
            return (h1, h2)
        }
        var h1 = rawH1.littleEndian
        var h2 = rawH2.littleEndian
        // Ensure h2 is odd to improve cycle coverage when used with modulo (avoids even-step cycles).
        if h2 == 0 { h2 = 1 } else { h2 |= 1 }
        return (h1, h2)
    }
    
    /// Hash with selectable backend (default: `defaultBackend`).
    public static func hash64(_ value: Value, seed: UInt64 = 0, backend: Backend) -> UInt64 {
        switch backend {
        case .sha256:
            return hash64(value, seed: seed)
        case .xxhash64:
            return XXHash64.hash64(serialize(value), seed: seed)
        }
    }
    
    /// Two 64-bit hashes with selectable backend (default: `defaultBackend`).
    public static func hash64x2(_ value: Value, seed: UInt64 = 0, backend: Backend) -> (UInt64, UInt64) {
        switch backend {
        case .sha256:
            return hash64x2(value, seed: seed)
        case .xxhash64:
            return XXHash64.hash64x2(serialize(value), seed: seed)
        }
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

// MARK: - Unaligned load helpers
private extension UnsafeRawBufferPointer {
    func loadUnaligned<T>(as: T.Type) -> T {
        return self.bindMemory(to: T.self).baseAddress!.pointee
    }
    func loadUnaligned<T>(fromByteOffset offset: Int, as _: T.Type) -> T {
        return self.baseAddress!.advanced(by: offset).assumingMemoryBound(to: T.self).pointee
    }
}

// MARK: - XXHash64 (pure Swift)
private enum XXHash64 {
    // Constants as per xxHash64 specification
    private static let prime1: UInt64 = 11400714785074694791
    private static let prime2: UInt64 = 14029467366897019727
    private static let prime3: UInt64 = 1609587929392839161
    private static let prime4: UInt64 = 9650029242287828579
    private static let prime5: UInt64 = 2870177450012600261
    
    static func hash64(_ data: Data, seed: UInt64) -> UInt64 {
        return data.withUnsafeBytes { buffer in
            return hash64(buffer, seed: seed)
        }
    }
    
    static func hash64x2(_ data: Data, seed: UInt64) -> (UInt64, UInt64) {
        // Derive two independent seeds from the provided seed via simple bijection.
        let seed1 = seed &* 0x9E3779B97F4A7C15 &+ 0xD2B74407B1CE6E93
        let seed2 = seed ^ 0x9E3779B97F4A7C15
        let h1 = hash64(data, seed: seed1)
        var h2 = hash64(data, seed: seed2)
        if h2 == 0 { h2 = 1 } else { h2 |= 1 } // ensure odd and non-zero
        return (h1, h2)
    }
    
    private static func hash64(_ buffer: UnsafeRawBufferPointer, seed: UInt64) -> UInt64 {
        let count = buffer.count
        var p = buffer.baseAddress!
        let end = p.advanced(by: count)
        
        var hash: UInt64
        
        if count >= 32 {
            var v1 = seed &+ prime1 &+ prime2
            var v2 = seed &+ prime2
            var v3 = seed
            var v4 = seed &- prime1
            
            while p <= end.advanced(by: -32) {
                v1 = round(v1, p.loadUnaligned(as: UInt64.self)); p = p.advanced(by: 8)
                v2 = round(v2, p.loadUnaligned(as: UInt64.self)); p = p.advanced(by: 8)
                v3 = round(v3, p.loadUnaligned(as: UInt64.self)); p = p.advanced(by: 8)
                v4 = round(v4, p.loadUnaligned(as: UInt64.self)); p = p.advanced(by: 8)
            }
            
            hash = rotateLeft(v1, 1) &+ rotateLeft(v2, 7) &+ rotateLeft(v3, 12) &+ rotateLeft(v4, 18)
            
            hash = mergeRound(hash, v1)
            hash = mergeRound(hash, v2)
            hash = mergeRound(hash, v3)
            hash = mergeRound(hash, v4)
        } else {
            hash = seed &+ prime5
        }
        
        hash = hash &+ UInt64(count)
        
        // Process remaining 8-byte chunks
        while p <= end.advanced(by: -8) {
            let k1 = round(0, p.loadUnaligned(as: UInt64.self))
            hash ^= k1
            hash = rotateLeft(hash, 27) &* prime1 &+ prime4
            p = p.advanced(by: 8)
        }
        
        // Process remaining 4-byte chunk
        if p <= end.advanced(by: -4) {
            let k1 = UInt64(p.loadUnaligned(as: UInt32.self))
            hash ^= k1 &* prime1
            hash = rotateLeft(hash, 23) &* prime2 &+ prime3
            p = p.advanced(by: 4)
        }
        
        // Process remaining bytes
        while p < end {
            let k1 = UInt64(p.loadUnaligned(as: UInt8.self))
            hash ^= k1 &* prime5
            hash = rotateLeft(hash, 11) &* prime1
            p = p.advanced(by: 1)
        }
        
        // Avalanche
        hash ^= hash >> 33
        hash &*= prime2
        hash ^= hash >> 29
        hash &*= prime3
        hash ^= hash >> 32
        
        return hash.littleEndian
    }
    
    @inline(__always)
    private static func round(_ acc: UInt64, _ input: UInt64) -> UInt64 {
        var acc = acc
        acc &+= input &* prime2
        acc = rotateLeft(acc, 31)
        acc &*= prime1
        return acc
    }
    
    @inline(__always)
    private static func mergeRound(_ hash: UInt64, _ val: UInt64) -> UInt64 {
        var h = hash
        var v = val
        v &*= prime2
        v = rotateLeft(v, 31)
        v &*= prime1
        h ^= v
        h = h &* prime1 &+ prime4
        return h
    }
    
    @inline(__always)
    private static func rotateLeft(_ x: UInt64, _ r: UInt64) -> UInt64 {
        return (x << r) | (x >> (64 - r))
    }
}


