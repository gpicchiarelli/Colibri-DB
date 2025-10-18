//
//  BloomFilter.swift
//  ColibrDB
//
//  Created by AI Assistant on 2025-10-18.
//
// ColibrDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// 🚀 FIX #52: Advanced Data Structures - Bloom Filter Implementation
// Theme: Probabilistic data structure for fast membership testing

import Foundation

/// A Bloom filter is a space-efficient probabilistic data structure that is used to test
/// whether an element is a member of a set. False positives are possible, but false negatives are not.
///
/// **Use Cases**:
/// - Index existence checking before expensive disk I/O
/// - Cache key existence testing
/// - Duplicate detection in large datasets
/// - Query optimization (check if table has matching rows)
///
/// **Characteristics**:
/// - Space: O(m) where m is the bit array size
/// - Insert: O(k) where k is the number of hash functions
/// - Query: O(k)
/// - False positive rate: (1 - e^(-kn/m))^k where n is number of elements
public final class BloomFilter: @unchecked Sendable {
    
    // MARK: - Properties
    
    /// Bit array for storing hash results
    private var bits: [UInt64]
    
    /// Number of bits in the filter (m)
    private let bitCount: Int
    
    /// Number of hash functions to use (k)
    private let hashFunctionCount: Int
    
    /// Number of elements inserted
    private var elementCount: Int = 0
    
    /// Lock for thread-safe operations
    private let lock = NSLock()
    
    // MARK: - Initialization
    
    /// Creates a Bloom filter optimized for expected number of elements and desired false positive rate
    ///
    /// - Parameters:
    ///   - expectedElements: Expected number of elements to insert (n)
    ///   - falsePositiveRate: Desired false positive probability (default 0.01 = 1%)
    public init(expectedElements: Int, falsePositiveRate: Double = 0.01) {
        // Calculate optimal bit array size: m = -(n * ln(p)) / (ln(2)^2)
        let optimalBitCount = Int(ceil(
            -Double(expectedElements) * log(falsePositiveRate) / pow(log(2.0), 2.0)
        ))
        
        // Calculate optimal number of hash functions: k = (m/n) * ln(2)
        let optimalHashCount = Int(ceil(
            Double(optimalBitCount) / Double(expectedElements) * log(2.0)
        ))
        
        self.bitCount = max(64, optimalBitCount) // Minimum 64 bits
        self.hashFunctionCount = max(1, min(10, optimalHashCount)) // Between 1-10 hash functions
        
        // Allocate bit array (using UInt64 chunks for efficiency)
        let chunkCount = (bitCount + 63) / 64
        self.bits = Array(repeating: 0, count: chunkCount)
        
        print("🌸 BloomFilter initialized: \(bitCount) bits, \(hashFunctionCount) hash functions, expected FP rate: \(String(format: "%.4f%%", falsePositiveRate * 100))")
    }
    
    /// Creates a Bloom filter with explicit bit count and hash function count
    ///
    /// - Parameters:
    ///   - bitCount: Number of bits in the filter
    ///   - hashFunctionCount: Number of hash functions to use
    public init(bitCount: Int, hashFunctionCount: Int) {
        self.bitCount = max(64, bitCount)
        self.hashFunctionCount = max(1, min(10, hashFunctionCount))
        
        let chunkCount = (self.bitCount + 63) / 64
        self.bits = Array(repeating: 0, count: chunkCount)
        
        print("🌸 BloomFilter initialized: \(self.bitCount) bits, \(self.hashFunctionCount) hash functions")
    }
    
    // MARK: - Public API
    
    /// Inserts an element into the Bloom filter
    ///
    /// - Parameter data: Data to insert
    public func insert(_ data: Data) {
        lock.lock()
        defer { lock.unlock() }
        
        for hashIndex in 0..<hashFunctionCount {
            let bitIndex = computeHash(data, hashIndex: hashIndex)
            setBit(at: bitIndex)
        }
        
        elementCount += 1
    }
    
    /// Inserts a string into the Bloom filter
    ///
    /// - Parameter string: String to insert
    public func insert(_ string: String) {
        guard let data = string.data(using: .utf8) else { return }
        insert(data)
    }
    
    /// Inserts an integer into the Bloom filter
    ///
    /// - Parameter value: Integer to insert
    public func insert(_ value: Int) {
        var val = value
        let data = Data(bytes: &val, count: MemoryLayout<Int>.size)
        insert(data)
    }
    
    /// Tests whether an element might be in the set
    ///
    /// - Parameter data: Data to test
    /// - Returns: `true` if element might be in set (with false positive rate),
    ///            `false` if element is definitely not in set
    public func mightContain(_ data: Data) -> Bool {
        lock.lock()
        defer { lock.unlock() }
        
        for hashIndex in 0..<hashFunctionCount {
            let bitIndex = computeHash(data, hashIndex: hashIndex)
            if !isBitSet(at: bitIndex) {
                return false // Definitely not in set
            }
        }
        
        return true // Might be in set
    }
    
    /// Tests whether a string might be in the set
    ///
    /// - Parameter string: String to test
    /// - Returns: `true` if element might be in set, `false` if definitely not
    public func mightContain(_ string: String) -> Bool {
        guard let data = string.data(using: .utf8) else { return false }
        return mightContain(data)
    }
    
    /// Tests whether an integer might be in the set
    ///
    /// - Parameter value: Integer to test
    /// - Returns: `true` if element might be in set, `false` if definitely not
    public func mightContain(_ value: Int) -> Bool {
        var val = value
        let data = Data(bytes: &val, count: MemoryLayout<Int>.size)
        return mightContain(data)
    }
    
    /// Clears all elements from the Bloom filter
    public func clear() {
        lock.lock()
        defer { lock.unlock() }
        
        for i in 0..<bits.count {
            bits[i] = 0
        }
        elementCount = 0
    }
    
    /// Returns the current false positive rate estimate based on inserted elements
    public func estimatedFalsePositiveRate() -> Double {
        lock.lock()
        defer { lock.unlock() }
        
        guard elementCount > 0 else { return 0.0 }
        
        // Formula: (1 - e^(-kn/m))^k
        let k = Double(hashFunctionCount)
        let n = Double(elementCount)
        let m = Double(bitCount)
        
        let exponent = -k * n / m
        return pow(1.0 - exp(exponent), k)
    }
    
    /// Returns statistics about the Bloom filter
    public func statistics() -> BloomFilterStatistics {
        lock.lock()
        defer { lock.unlock() }
        
        var bitsSet = 0
        for chunk in bits {
            bitsSet += chunk.nonzeroBitCount
        }
        
        return BloomFilterStatistics(
            bitCount: bitCount,
            hashFunctionCount: hashFunctionCount,
            elementCount: elementCount,
            bitsSet: bitsSet,
            fillRatio: Double(bitsSet) / Double(bitCount),
            estimatedFalsePositiveRate: estimatedFalsePositiveRate()
        )
    }
    
    // MARK: - Private Methods
    
    /// Computes a hash index for the given data and hash function index
    ///
    /// Uses double hashing: h(k,i) = (h1(k) + i*h2(k)) mod m
    ///
    /// - Parameters:
    ///   - data: Data to hash
    ///   - hashIndex: Index of the hash function (0 to k-1)
    /// - Returns: Bit index in range [0, bitCount)
    private func computeHash(_ data: Data, hashIndex: Int) -> Int {
        // Primary hash using FNV-1a
        let h1 = fnv1aHash(data)
        
        // Secondary hash using simple polynomial rolling hash
        let h2 = polynomialHash(data)
        
        // Double hashing: h(k,i) = (h1(k) + i*h2(k)) mod m
        let combined = h1 &+ (UInt64(hashIndex) &* h2)
        
        return Int(combined % UInt64(bitCount))
    }
    
    /// FNV-1a hash function
    private func fnv1aHash(_ data: Data) -> UInt64 {
        var hash: UInt64 = 14695981039346656037 // FNV offset basis
        let prime: UInt64 = 1099511628211 // FNV prime
        
        for byte in data {
            hash ^= UInt64(byte)
            hash = hash &* prime
        }
        
        return hash
    }
    
    /// Polynomial rolling hash function
    private func polynomialHash(_ data: Data) -> UInt64 {
        var hash: UInt64 = 0
        let base: UInt64 = 31
        
        for byte in data {
            hash = hash &* base &+ UInt64(byte)
        }
        
        return hash | 1 // Ensure odd number for double hashing
    }
    
    /// Sets a bit at the specified index
    private func setBit(at index: Int) {
        let chunkIndex = index / 64
        let bitOffset = index % 64
        bits[chunkIndex] |= (1 << bitOffset)
    }
    
    /// Checks if a bit is set at the specified index
    private func isBitSet(at index: Int) -> Bool {
        let chunkIndex = index / 64
        let bitOffset = index % 64
        return (bits[chunkIndex] & (1 << bitOffset)) != 0
    }
}

// MARK: - Statistics

/// Statistics about a Bloom filter's current state
public struct BloomFilterStatistics {
    /// Total number of bits in the filter
    public let bitCount: Int
    
    /// Number of hash functions used
    public let hashFunctionCount: Int
    
    /// Number of elements inserted
    public let elementCount: Int
    
    /// Number of bits currently set to 1
    public let bitsSet: Int
    
    /// Ratio of bits set (0.0 to 1.0)
    public let fillRatio: Double
    
    /// Estimated false positive rate
    public let estimatedFalsePositiveRate: Double
    
    public var description: String {
        """
        BloomFilter Statistics:
        - Bits: \(bitCount) (\(bitsSet) set, \(String(format: "%.2f%%", fillRatio * 100)) full)
        - Hash Functions: \(hashFunctionCount)
        - Elements: \(elementCount)
        - Estimated FP Rate: \(String(format: "%.4f%%", estimatedFalsePositiveRate * 100))
        """
    }
}

// MARK: - Database Integration

extension BloomFilter {
    
    /// Creates a Bloom filter optimized for table row existence checking
    ///
    /// - Parameter estimatedRowCount: Estimated number of rows in the table
    /// - Returns: Bloom filter with 0.1% false positive rate
    public static func forTableRows(estimatedRowCount: Int) -> BloomFilter {
        return BloomFilter(expectedElements: estimatedRowCount, falsePositiveRate: 0.001)
    }
    
    /// Creates a Bloom filter optimized for index key existence checking
    ///
    /// - Parameter estimatedKeyCount: Estimated number of unique keys
    /// - Returns: Bloom filter with 1% false positive rate
    public static func forIndexKeys(estimatedKeyCount: Int) -> BloomFilter {
        return BloomFilter(expectedElements: estimatedKeyCount, falsePositiveRate: 0.01)
    }
    
    /// Creates a Bloom filter optimized for cache key checking
    ///
    /// - Parameter estimatedCacheSize: Estimated number of cache entries
    /// - Returns: Bloom filter with 5% false positive rate (higher tolerance for cache)
    public static func forCacheKeys(estimatedCacheSize: Int) -> BloomFilter {
        return BloomFilter(expectedElements: estimatedCacheSize, falsePositiveRate: 0.05)
    }
}

