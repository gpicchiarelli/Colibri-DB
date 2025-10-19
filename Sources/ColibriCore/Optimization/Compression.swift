//
//  Compression.swift
//  ColibrìDB Data Compression
//
//  Based on: spec/Compression.tla
//  Implements: LZ4/Snappy-style compression
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//

import Foundation
import Compression

/// Compression algorithm
public enum CompressionAlgorithm {
    case none
    case lz4
    case zlib
    case lzma
}

/// Compression Manager
public struct CompressionManager {
    // MARK: - Compression
    
    /// Compress data
    public static func compress(_ data: Data, algorithm: CompressionAlgorithm = .lz4) throws -> Data {
        guard algorithm != .none else {
            return data
        }
        
        let compressionAlgo = algorithm.nativeAlgorithm
        
        let compressedData = data.withUnsafeBytes { (sourcePtr: UnsafeRawBufferPointer) -> Data? in
            guard let baseAddress = sourcePtr.baseAddress else {
                return nil
            }
            
            let destinationSize = data.count
            var destinationBuffer = Data(count: destinationSize)
            
            let compressedSize = destinationBuffer.withUnsafeMutableBytes { (destPtr: UnsafeMutableRawBufferPointer) -> Int in
                guard let destAddress = destPtr.baseAddress else {
                    return 0
                }
                
                return compression_encode_buffer(
                    destAddress,
                    destinationSize,
                    baseAddress,
                    data.count,
                    nil,
                    compressionAlgo
                )
            }
            
            if compressedSize > 0 {
                destinationBuffer.count = compressedSize
                return destinationBuffer
            }
            
            return nil
        }
        
        return compressedData ?? data
    }
    
    /// Decompress data
    public static func decompress(_ data: Data, algorithm: CompressionAlgorithm = .lz4, originalSize: Int) throws -> Data {
        guard algorithm != .none else {
            return data
        }
        
        let compressionAlgo = algorithm.nativeAlgorithm
        
        let decompressedData = data.withUnsafeBytes { (sourcePtr: UnsafeRawBufferPointer) -> Data? in
            guard let baseAddress = sourcePtr.baseAddress else {
                return nil
            }
            
            var destinationBuffer = Data(count: originalSize)
            
            let decompressedSize = destinationBuffer.withUnsafeMutableBytes { (destPtr: UnsafeMutableRawBufferPointer) -> Int in
                guard let destAddress = destPtr.baseAddress else {
                    return 0
                }
                
                return compression_decode_buffer(
                    destAddress,
                    originalSize,
                    baseAddress,
                    data.count,
                    nil,
                    compressionAlgo
                )
            }
            
            if decompressedSize > 0 {
                destinationBuffer.count = decompressedSize
                return destinationBuffer
            }
            
            return nil
        }
        
        return decompressedData ?? data
    }
}

// MARK: - Extension

extension CompressionAlgorithm {
    var nativeAlgorithm: compression_algorithm {
        switch self {
        case .none:
            return COMPRESSION_LZ4
        case .lz4:
            return COMPRESSION_LZ4
        case .zlib:
            return COMPRESSION_ZLIB
        case .lzma:
            return COMPRESSION_LZMA
        }
    }
}

