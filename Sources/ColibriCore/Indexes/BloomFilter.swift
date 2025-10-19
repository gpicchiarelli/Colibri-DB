//
//  BloomFilter.swift
//  Based on: spec/BloomFilter.tla
//

import Foundation

public struct BloomFilter {
    private var bits: [Bool]
    private let size: Int
    private let hashCount: Int
    
    public init(size: Int = 10000, hashCount: Int = 3) {
        self.size = size
        self.hashCount = hashCount
        self.bits = Array(repeating: false, count: size)
    }
    
    private func hash(_ value: Value, seed: Int) -> Int {
        var hasher = Hasher()
        hasher.combine(seed)
        
        switch value {
        case .int(let v): hasher.combine(v)
        case .double(let v): hasher.combine(v)
        case .string(let v): hasher.combine(v)
        case .bool(let v): hasher.combine(v)
        case .date(let v): hasher.combine(v)
        case .null: hasher.combine(0)
        case .decimal(let v): hasher.combine(v)
        case .bytes(let v): hasher.combine(v)
        }
        
        return abs(hasher.finalize()) % size
    }
    
    public mutating func insert(_ value: Value) {
        for i in 0..<hashCount {
            let index = hash(value, seed: i)
            bits[index] = true
        }
    }
    
    public func contains(_ value: Value) -> Bool {
        for i in 0..<hashCount {
            let index = hash(value, seed: i)
            if !bits[index] {
                return false
            }
        }
        return true
    }
    
    public func falsePositiveRate(insertedCount: Int) -> Double {
        let m = Double(size)
        let k = Double(hashCount)
        let n = Double(insertedCount)
        return pow(1.0 - exp(-k * n / m), k)
    }
}

