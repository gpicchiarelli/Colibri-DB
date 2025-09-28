//
//  IOHints.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-09-26.
//
// ColibrDB — BSD 3-Clause License
//
// Theme: Adaptive I/O hints wrapping platform syscalls for hot paths.

import Foundation
#if canImport(Darwin)
import Darwin
#elseif canImport(Glibc)
import Glibc
#endif

/// Utility namespace used to apply best-effort I/O tuning hints.
///
/// All helpers are no-ops when the underlying platform does not expose the
/// targeted syscall, allowing callers to unconditionally request hints without
/// sprinkling `#if os(...)` checks throughout the codebase.
enum IOHints {
    private static let prefetchChunkBytes: Int = 1 << 20 // 1 MiB
    private static let maxPrefetchChunks: Int = 4

    /// Applies sequential read hints on the specified file handle.
    /// - Parameters:
    ///   - handle: Open file handle.
    ///   - offset: Starting offset (defaults to 0).
    ///   - length: Planned read length in bytes.
    static func prepareSequentialRead(handle: FileHandle, offset: UInt64 = 0, length: UInt64) {
        guard length > 0 else { return }
        let fd = handle.fileDescriptor
#if canImport(Darwin)
        _ = fcntl(fd, F_RDAHEAD, 1)
        var advice = radvisory(ra_offset: off_t(truncatingIfNeeded: offset),
                               ra_count: Int32(clampingLength(length)))
        withUnsafeMutablePointer(to: &advice) { ptr in
            _ = fcntl(fd, F_RDADVISE, ptr)
        }
#elseif canImport(Glibc)
        _ = posix_fadvise(fd,
                           off_t(truncatingIfNeeded: offset),
                           off_t(clampingLength(length)),
                           POSIX_FADV_SEQUENTIAL)
        _ = posix_fadvise(fd,
                           off_t(truncatingIfNeeded: offset),
                           off_t(clampingLength(length)),
                           POSIX_FADV_WILLNEED)
#endif
        prefetch(handle: handle, offset: offset, length: length)
    }

    /// Applies a localized sequential hint for repeated page fetches.
    /// - Parameters:
    ///   - fd: File descriptor.
    ///   - offset: Byte offset.
    ///   - length: Suggested length.
    static func hintSequential(fd: Int32, offset: UInt64, length: Int) {
#if canImport(Darwin)
        _ = fcntl(fd, F_RDAHEAD, 1)
        var advice = radvisory(ra_offset: off_t(truncatingIfNeeded: offset),
                               ra_count: Int32(clampingLength(UInt64(max(0, length)))))
        withUnsafeMutablePointer(to: &advice) { ptr in
            _ = fcntl(fd, F_RDADVISE, ptr)
        }
#elseif canImport(Glibc)
        _ = posix_fadvise(fd,
                           off_t(truncatingIfNeeded: offset),
                           off_t(clampingLength(UInt64(max(0, length)))),
                           POSIX_FADV_WILLNEED)
#endif
    }

    /// Applies a stronger durability sync. Falls back to `fsync` when
    /// `F_FULLFSYNC` is unsupported or fails.
    /// - Parameters:
    ///   - handle: File handle to synchronize.
    ///   - full: Whether to try `F_FULLFSYNC`.
    static func synchronize(handle: FileHandle, full: Bool) throws {
#if canImport(Darwin)
        if full {
            let fd = handle.fileDescriptor
            if fcntl(fd, F_FULLFSYNC) == -1 {
                try handle.synchronize()
            }
            return
        }
        try handle.synchronize()
#else
        _ = full
        try handle.synchronize()
#endif
    }

    /// Attempts to disable OS cache for a file descriptor (Darwin: F_NOCACHE).
    static func setNoCache(fd: Int32, enabled: Bool) {
#if canImport(Darwin)
        _ = fcntl(fd, F_NOCACHE, enabled ? 1 : 0)
#else
        _ = (fd, enabled)
#endif
    }

    /// Clamps a 64-bit length to fit into `off_t`.
    private static func clampingLength(_ length: UInt64) -> Int64 {
        if length >= UInt64(Int64.max) { return Int64.max }
        return Int64(length)
    }

    /// Naively prefetches the first few chunks using `preadv2` (or `preadv`).
    private static func prefetch(handle: FileHandle, offset: UInt64, length: UInt64) {
#if canImport(Glibc)
        guard length > 0 else { return }
        let fd = handle.fileDescriptor
        let maxBytes = min(length, UInt64(prefetchChunkBytes * maxPrefetchChunks))
        let chunkSize = min(prefetchChunkBytes, Int(maxBytes))
        var buffer = [UInt8](repeating: 0, count: max(chunkSize, 1))
        var totalPrefetched: UInt64 = 0
        var currentOffset = off_t(truncatingIfNeeded: offset)
        while totalPrefetched < maxBytes {
            let toFetch = Int(min(UInt64(buffer.count), maxBytes - totalPrefetched))
            let result: ssize_t = buffer.withUnsafeMutableBytes { raw -> ssize_t in
                var iov = iovec(iov_base: raw.baseAddress, iov_len: toFetch)
                if let fn = preadv2Pointer {
                    return fn(fd, &iov, 1, currentOffset, rwfNowait)
                }
                return Glibc.preadv(fd, &iov, 1, currentOffset)
            }
            if result <= 0 { break }
            totalPrefetched += UInt64(result)
            currentOffset += off_t(result)
            if result < toFetch { break }
        }
#else
        _ = (handle, offset, length)
#endif
    }

#if canImport(Glibc)
    private static let rwfNowait: Int32 = {
#if os(Linux)
        return Int32(0x00000008) // RWF_NOWAIT, not exposed on all swift targets
#else
        return 0
#endif
    }()

    private static let preadv2Pointer: (@convention(c) (Int32, UnsafeMutablePointer<iovec>?, Int32, off_t, Int32) -> ssize_t)? = {
        guard let symbol = dlsym(nil, "preadv2") else { return nil }
        return unsafeBitCast(symbol,
                             to: (@convention(c) (Int32, UnsafeMutablePointer<iovec>?, Int32, off_t, Int32) -> ssize_t).self)
    }()
#endif
}
