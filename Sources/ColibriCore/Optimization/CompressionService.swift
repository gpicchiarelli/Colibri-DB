//
//  CompressionService.swift
//  ColibrìDB Compression Service
//
//  Implements: Data compression/decompression
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//

import Foundation

/// Compression service protocol
public protocol CompressionService: Sendable {
    func compress(_ data: Data) throws -> Data
    func decompress(_ data: Data, originalSize: Int) throws -> Data
}

/// Default compression service implementation
public struct DefaultCompressionService: CompressionService {
    private let algorithm: CompressionAlgorithm
    
    public init(algorithm: CompressionAlgorithm = .lz4) {
        self.algorithm = algorithm
    }
    
    public func compress(_ data: Data) throws -> Data {
        return try CompressionManager.compress(data, algorithm: algorithm)
    }
    
    public func decompress(_ data: Data, originalSize: Int) throws -> Data {
        return try CompressionManager.decompress(data, algorithm: algorithm, originalSize: originalSize)
    }
}

