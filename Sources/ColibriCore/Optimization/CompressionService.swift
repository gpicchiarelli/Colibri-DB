//
//  CompressionService.swift
//  ColibrìDB Compression Service
//
//  Implements: Data compression/decompression
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//

import Foundation

// MARK: - Protocol Definition

/// Compression service protocol (async, Sendable-safe)
public protocol CompressionService: Sendable {
    func compress(data: Data) async throws -> Data
    func decompress(data: Data) async throws -> Data
}

// MARK: - Protocol Implementation

/// Default compression service implementation (stateless helper)
public struct DefaultCompressionService: CompressionService {
    // MARK: - Properties
    
    private let algorithm: CompressionAlgorithm
    
    // MARK: - Initialization
    
    /// Initialize compression service
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
        // Without the original size, fall back to a reasonable estimate (4x)
        let estimatedSize = max(data.count * 4, 1)
        return try CompressionManager.decompress(data, algorithm: algorithm, originalSize: estimatedSize)
    }
}

