import Foundation
import Darwin
#if canImport(Accelerate)
import Accelerate
#endif

/// Collection of SIMD-friendly helpers with Accelerate/NEON stubs.
enum SIMDOptimizations {
    /// Returns the length of the common prefix between two buffers.
    static func commonPrefixLength(_ lhs: Data, _ rhs: Data) -> Int {
#if canImport(Accelerate)
        return lhs.withUnsafeBytes { lBuf in
            rhs.withUnsafeBytes { rBuf in
                guard let lBase = lBuf.baseAddress, let rBase = rBuf.baseAddress else { return 0 }
                let count = min(lhs.count, rhs.count)
                let lPtr = lBase.assumingMemoryBound(to: UInt8.self)
                let rPtr = rBase.assumingMemoryBound(to: UInt8.self)
                var offset = 0
                let stride = 64
                while offset + stride <= count {
                    if memcmp(lPtr.advanced(by: offset), rPtr.advanced(by: offset), stride) != 0 {
                        break
                    }
                    offset += stride
                }
                while offset < count {
                    if lPtr[offset] != rPtr[offset] { break }
                    offset += 1
                }
                return offset
            }
        }
#else
        return fallbackCommonPrefix(lhs, rhs)
#endif
    }

    /// Hash helper using a simple FNV-1a fallback; kept pluggable for future SIMD paths.
    static func hashBytes(_ data: Data) -> UInt64 {
#if canImport(Accelerate)
        // Placeholder for Accelerate-backed hashing (e.g. vDSP_reduce).
        return fallbackHashBytes(data)
#else
        return fallbackHashBytes(data)
#endif
    }

    private static func fallbackCommonPrefix(_ lhs: Data, _ rhs: Data) -> Int {
        let limit = min(lhs.count, rhs.count)
        var i = 0
        while i < limit {
            if lhs[i] != rhs[i] { break }
            i += 1
        }
        return i
    }

    private static func fallbackHashBytes(_ data: Data) -> UInt64 {
        var hash: UInt64 = 1469598103934665603 // FNV offset basis
        for byte in data {
            hash ^= UInt64(byte)
            hash &*= 1099511628211
        }
        return hash
    }
}
