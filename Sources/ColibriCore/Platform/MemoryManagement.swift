//
//  MemoryManagement.swift
//  Based on: spec/MemoryManagement.tla
//

import Foundation

// MARK: - Types

/// Memory pool for efficient memory allocation
public struct MemoryPool {
    private var blocks: [Data]
    private let blockSize: Int
    private var freeList: [Int]
    
    public init(blockCount: Int, blockSize: Int) {
        self.blockSize = blockSize
        self.blocks = Array(repeating: Data(count: blockSize), count: blockCount)
        self.freeList = Array(0..<blockCount)
    }
    
    public mutating func allocate() -> Int? {
        guard !freeList.isEmpty else {
            return nil
        }
        return freeList.removeFirst()
    }
    
    public mutating func deallocate(_ index: Int) {
        freeList.append(index)
    }
    
    public func read(_ index: Int) -> Data? {
        guard index < blocks.count else {
            return nil
        }
        return blocks[index]
    }
    
    public mutating func write(_ index: Int, data: Data) {
        guard index < blocks.count else {
            return
        }
        blocks[index] = data
    }
    
    public func getStatistics() -> MemoryPoolStatistics {
        return MemoryPoolStatistics(
            totalBlocks: blocks.count,
            freeBlocks: freeList.count,
            usedBlocks: blocks.count - freeList.count,
            blockSize: blockSize
        )
    }
}

/// Memory pool statistics
public struct MemoryPoolStatistics {
    public let totalBlocks: Int
    public let freeBlocks: Int
    public let usedBlocks: Int
    public let blockSize: Int
    
    public var utilizationPercent: Double {
        guard totalBlocks > 0 else { return 0 }
        return Double(usedBlocks) / Double(totalBlocks) * 100.0
    }
}

// MARK: - Arena Allocator

/// Arena allocator for efficient memory allocation
public actor ArenaAllocator {
    // MARK: - Properties
    
    private var arena: Data
    private var offset: Int = 0
    private let size: Int
    
    // MARK: - Initialization
    
    /// Initialize arena allocator
    /// - Parameter size: Size of the arena in bytes
    public init(size: Int) {
        self.size = size
        self.arena = Data(count: size)
    }
    
    // MARK: - Public Methods
    
    /// Allocate memory from arena
    /// - Parameter size: Size to allocate
    /// - Returns: Offset of allocated memory, or nil if insufficient space
    public func allocate(size: Int) -> Int? {
        guard offset + size <= self.size else {
            return nil
        }
        
        let allocatedOffset = offset
        offset += size
        
        return allocatedOffset
    }
    
    /// Reset arena to beginning
    public func reset() {
        offset = 0
    }
    
    /// Get current usage of arena
    /// - Returns: Number of bytes used
    public func getUsage() -> Int {
        return offset
    }
}

