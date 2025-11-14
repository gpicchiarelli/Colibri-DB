//
//  CompressionService.swift
//  ColibrìDB Compression Service
//
//  Implements: Data compression/decompression
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//

import Foundation

/// Compression service protocol (async, Sendable-safe)
public protocol CompressionService: Sendable {
    func compress(data: Data) async throws -> Data
    func decompress(data: Data) async throws -> Data
}

/// Default compression service implementation (stateless helper)
public struct DefaultCompressionService: CompressionService {
    private let algorithm: CompressionAlgorithm
    
    public init(algorithm: CompressionAlgorithm = .lz4) {
        self.algorithm = algorithm
    }
    
    public func compress(data: Data) async throws -> Data {
        return try CompressionManager.compress(data, algorithm: algorithm)
    }
    
    public func decompress(data: Data) async throws -> Data {
        // Without the original size, fall back to a reasonable estimate (4x)
        let estimatedSize = max(data.count * 4, 1)
        return try CompressionManager.decompress(data, algorithm: algorithm, originalSize: estimatedSize)
    }
}

