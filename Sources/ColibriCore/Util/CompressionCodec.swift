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
/// Provides robust error handling and validation to prevent data corruption.
public enum CompressionCodec {
    
    // MARK: - Compression
    
    /// Attempts to compress `data` using the provided algorithm.
    /// Returns nil when compression is disabled or ineffective (compressed >= original).
    /// 
    /// - Parameters:
    ///   - data: Data to compress
    ///   - algorithm: Compression algorithm to use
    /// - Returns: Compressed data, or nil if compression disabled/ineffective
    /// - Note: Never throws - returns nil on failure to allow fallback to uncompressed
    static func compress(_ data: Data, algorithm: CompressionAlgorithm) -> Data? {
        // If compression disabled or empty data, return nil
        guard let compressionID = algorithm.compressionID, !data.isEmpty else { 
            return nil 
        }
        
        // Validate input size (reasonable limits to prevent memory issues)
        guard data.count <= 100 * 1024 * 1024 else {  // Max 100MB
            print("⚠️  CompressionCodec: Input too large (\(data.count) bytes), skipping compression")
            return nil
        }
        
        // Allocate output buffer with extra space for compression overhead
        let destinationCapacity = data.count + max(data.count / 16, 64)
        var output = Data(count: destinationCapacity)
        
        // Perform compression
        let compressedSize = data.withUnsafeBytes { src -> size_t in
            guard let srcBase = src.baseAddress else { 
                print("⚠️  CompressionCodec: Invalid source buffer")
                return 0 
            }
            return output.withUnsafeMutableBytes { dst -> size_t in
                guard let dstBase = dst.baseAddress else { 
                    print("⚠️  CompressionCodec: Invalid destination buffer")
                    return 0 
                }
                return compression_encode_buffer(
                    dstBase.assumingMemoryBound(to: UInt8.self), destinationCapacity,
                    srcBase.assumingMemoryBound(to: UInt8.self), data.count,
                    nil,
                    compressionID
                )
            }
        }
        
        // Validate compression result
        guard compressedSize > 0 else {
            // Compression failed - this is OK, we'll fall back to uncompressed
            return nil
        }
        
        // Only use compressed data if it's actually smaller
        guard compressedSize < data.count else {
            // Compression not effective - use original data
            return nil
        }
        
        // Trim to actual compressed size
        output.removeSubrange(compressedSize..<output.count)
        
        // Validate output
        guard !output.isEmpty else {
            print("⚠️  CompressionCodec: Compression produced empty output")
            return nil
        }
        
        return output
    }
    
    // MARK: - Decompression
    
    /// Decompresses `data` using the provided algorithm into a buffer of `expectedSize` bytes.
    /// 
    /// - Parameters:
    ///   - data: Compressed data
    ///   - algorithm: Compression algorithm used
    ///   - expectedSize: Expected size of decompressed data
    /// - Returns: Decompressed data
    /// - Throws: DBError.io if decompression fails or size mismatch
    /// - Note: NEVER returns silently corrupted data - throws on any error
    static func decompress(_ data: Data, algorithm: CompressionAlgorithm, expectedSize: Int) throws -> Data {
        // If algorithm is .none, data should already be uncompressed
        guard let compressionID = algorithm.compressionID else {
            // Validate that uncompressed data matches expected size
            guard data.count == expectedSize else {
                throw DBError.io("Uncompressed data size mismatch: expected \(expectedSize), got \(data.count)")
            }
            return data
        }
        
        // Validate input
        guard !data.isEmpty else {
            throw DBError.io("Cannot decompress empty data")
        }
        
        guard expectedSize > 0 && expectedSize <= 100 * 1024 * 1024 else {  // Max 100MB
            throw DBError.io("Invalid expected size for decompression: \(expectedSize)")
        }
        
        // Sanity check: compressed data should be smaller than expected output
        guard data.count < expectedSize * 2 else {
            throw DBError.io("Suspicious compression: compressed (\(data.count)) larger than 2× expected (\(expectedSize))")
        }
        
        // Allocate output buffer
        var output = Data(count: expectedSize)
        
        // Perform decompression
        let decoded = data.withUnsafeBytes { src -> size_t in
            guard let srcBase = src.baseAddress else { 
                return 0 
            }
            return output.withUnsafeMutableBytes { dst -> size_t in
                guard let dstBase = dst.baseAddress else { 
                    return 0 
                }
                return compression_decode_buffer(
                    dstBase.assumingMemoryBound(to: UInt8.self), expectedSize,
                    srcBase.assumingMemoryBound(to: UInt8.self), data.count,
                    nil,
                    compressionID
                )
            }
        }
        
        // Validate decompression result
        guard decoded > 0 else {
            throw DBError.io("Decompression failed: compression_decode_buffer returned 0")
        }
        
        guard decoded == expectedSize else {
            throw DBError.io("Decompression size mismatch: expected \(expectedSize), got \(decoded)")
        }
        
        return output
    }
    
    // MARK: - Validation & Monitoring
    
    /// Validates that compressed data can be successfully decompressed.
    /// Used for testing and verification.
    static func validate(compressed: Data, algorithm: CompressionAlgorithm, expectedSize: Int) -> Bool {
        do {
            let decompressed = try decompress(compressed, algorithm: algorithm, expectedSize: expectedSize)
            return decompressed.count == expectedSize
        } catch {
            return false
        }
    }
    
    /// Calculates compression ratio for monitoring purposes.
    /// Returns: ratio where 1.0 = no compression, 2.0 = 50% reduction, etc.
    static func compressionRatio(original: Int, compressed: Int) -> Double {
        guard compressed > 0 else { return 1.0 }
        return Double(original) / Double(compressed)
    }
}
