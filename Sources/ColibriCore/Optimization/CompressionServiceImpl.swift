//
//  CompressionServiceImpl.swift
//  ColibrìDB Compression Service Implementation
//
//  Concrete implementation of CompressionService protocol
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//

import Foundation

/// Concrete implementation of CompressionService protocol
public actor CompressionServiceImpl: CompressionService {
    // MARK: - Properties
    
    private let algorithm: CompressionAlgorithm
    
    // MARK: - Initialization
    
    /// Initialize compression service implementation
    /// - Parameter algorithm: Compression algorithm to use
    public init(algorithm: CompressionAlgorithm = .lz4) {
        self.algorithm = algorithm
    }
    
    // MARK: - Protocol Implementation
    
    /// Compress data
    /// - Parameter data: Data to compress
    /// - Returns: Compressed data
    public func compress(data: Data) async throws -> Data {
        return try CompressionManager.compress(data, algorithm: algorithm)
    }
    
    /// Decompress data
    /// - Parameter data: Compressed data to decompress
    /// - Returns: Decompressed data
    public func decompress(data: Data) async throws -> Data {
        // The protocol doesn't specify original size, so we try with a reasonable estimate
        // In practice, the original size should be stored with compressed data
        let estimatedSize = data.count * 4 // Conservative estimate
        return try CompressionManager.decompress(data, algorithm: algorithm, originalSize: estimatedSize)
    }
}

