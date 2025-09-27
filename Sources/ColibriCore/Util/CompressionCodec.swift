import Foundation
import Compression

public enum CompressionAlgorithm: String, Codable, Sendable {
    case none
    case lzfse
    case zlib

    var compressionID: compression_algorithm? {
        switch self {
        case .none:
            return nil
        case .lzfse:
            return COMPRESSION_LZFSE
        case .zlib:
            return COMPRESSION_ZLIB
        }
    }
}

/// Thin wrapper around Apple's Compression framework to support configurable algorithms.
public enum CompressionCodec {
    /// Attempts to compress `data` using the provided algorithm.
    /// Returns nil when compression is disabled or ineffective.
    static func compress(_ data: Data, algorithm: CompressionAlgorithm) -> Data? {
        guard let compressionID = algorithm.compressionID, !data.isEmpty else { return nil }
        let destinationCapacity = data.count + max(data.count / 16, 64)
        var output = Data(count: destinationCapacity)
        let compressedSize = data.withUnsafeBytes { src -> size_t in
            guard let srcBase = src.baseAddress else { return 0 }
            return output.withUnsafeMutableBytes { dst -> size_t in
                guard let dstBase = dst.baseAddress else { return 0 }
                return compression_encode_buffer(
                    dstBase.assumingMemoryBound(to: UInt8.self), destinationCapacity,
                    srcBase.assumingMemoryBound(to: UInt8.self), data.count,
                    nil,
                    compressionID
                )
            }
        }
        guard compressedSize > 0, compressedSize < data.count else { return nil }
        output.removeSubrange(compressedSize..<output.count)
        return output
    }

    /// Decompresses `data` using the provided algorithm into a buffer of `expectedSize` bytes.
    static func decompress(_ data: Data, algorithm: CompressionAlgorithm, expectedSize: Int) throws -> Data {
        guard let compressionID = algorithm.compressionID else {
            return data
        }
        var output = Data(count: expectedSize)
        let decoded = data.withUnsafeBytes { src -> size_t in
            guard let srcBase = src.baseAddress else { return 0 }
            return output.withUnsafeMutableBytes { dst -> size_t in
                guard let dstBase = dst.baseAddress else { return 0 }
                return compression_decode_buffer(
                    dstBase.assumingMemoryBound(to: UInt8.self), expectedSize,
                    srcBase.assumingMemoryBound(to: UInt8.self), data.count,
                    nil,
                    compressionID
                )
            }
        }
        guard decoded == expectedSize else {
            throw DBError.io("Failed to decode compressed WAL payload")
        }
        return output
    }
}
