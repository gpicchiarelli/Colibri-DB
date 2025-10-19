//
//  TOAST.swift
//  The Oversized-Attribute Storage Technique
//  Based on: spec/TOAST.tla
//

import Foundation

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

public actor TOASTManager {
    private let threshold: Int = 2048
    private var chunks: [UUID: Data] = [:]
    
    public init() {}
    
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
    
    public func delete(_ pointer: TOASTPointer) {
        chunks[pointer.chunkID] = nil
    }
}

