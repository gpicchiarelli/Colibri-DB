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
        // Double hashing: h_i = (h1 + i * h2) % m
        let (h1, h2) = HardwareHash.hash64x2(value, seed: UInt64(seed), backend: .xxhash64)
        let combined = (h1 &+ UInt64(seed) &* h2) % UInt64(size)
        return Int(combined)
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

