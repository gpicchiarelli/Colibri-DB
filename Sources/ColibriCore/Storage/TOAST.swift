//
//  TOAST.swift
//  The Oversized-Attribute Storage Technique
//  Based on: spec/TOAST.tla
//

import Foundation

// MARK: - Types

/// TOAST pointer for oversized attributes
public struct TOASTPointer {
    public let chunkID: UUID
    public let size: Int
    public let compressionType: CompressionAlgorithm
    
    public init(chunkID: UUID, size: Int, compressionType: CompressionAlgorithm) {
        self.chunkID = chunkID
        self.size = size
        self.compressionType = compressionType
    }
}

// MARK: - TOAST Manager

/// Manager for TOAST (The Oversized-Attribute Storage Technique)
public actor TOASTManager {
    // MARK: - Properties
    
    private let threshold: Int = 2048
    private var chunks: [UUID: Data] = [:]
    
    // MARK: - Initialization
    
    /// Initialize TOAST manager
    public init() {}
    
    // MARK: - Public Methods
    
    /// Store data using TOAST
    /// - Parameter data: Data to store
    /// - Returns: TOAST pointer to stored data
    public func store(_ data: Data) async throws -> TOASTPointer {
        if data.count <= threshold {
            let chunkID = UUID()
            chunks[chunkID] = data
            return TOASTPointer(chunkID: chunkID, size: data.count, compressionType: .none)
        }
        
        let compressed = try CompressionManager.compress(data, algorithm: .lz4)
        let chunkID = UUID()
        chunks[chunkID] = compressed
        
        return TOASTPointer(chunkID: chunkID, size: data.count, compressionType: .lz4)
    }
    
    /// Retrieve data from TOAST
    /// - Parameter pointer: TOAST pointer
    /// - Returns: Retrieved data
    public func retrieve(_ pointer: TOASTPointer) async throws -> Data {
        guard let compressedData = chunks[pointer.chunkID] else {
            throw DBError.notFound
        }
        
        if pointer.compressionType == .none {
            return compressedData
        }
        
        return try CompressionManager.decompress(
            compressedData,
            algorithm: pointer.compressionType,
            originalSize: pointer.size
        )
    }
    
    /// Delete data from TOAST
    /// - Parameter pointer: TOAST pointer to delete
    public func delete(_ pointer: TOASTPointer) {
        chunks[pointer.chunkID] = nil
    }
}

