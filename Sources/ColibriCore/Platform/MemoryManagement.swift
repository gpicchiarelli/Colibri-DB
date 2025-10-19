//
//  MemoryManagement.swift
//  Based on: spec/MemoryManagement.tla
//

import Foundation

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

public actor ArenaAllocator {
    private var arena: Data
    private var offset: Int = 0
    private let size: Int
    
    public init(size: Int) {
        self.size = size
        self.arena = Data(count: size)
    }
    
    public func allocate(size: Int) -> Int? {
        guard offset + size <= self.size else {
            return nil
        }
        
        let allocatedOffset = offset
        offset += size
        
        return allocatedOffset
    }
    
    public func reset() {
        offset = 0
    }
    
    public func getUsage() -> Int {
        return offset
    }
}

