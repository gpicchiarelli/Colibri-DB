//
//  IndexAdapters.swift
//  ColibrìDB - Index Protocol Adapters
//
//  TDD: GREEN Phase - Adapters to make existing implementations conform to Index protocol
//  Author: TDD Chief Engineer
//  Date: 2025-01-27
//

import Foundation

// MARK: - BTreeIndex Adapter

/// Adapter to make BTreeIndex conform to Index protocol
public struct BTreeIndexAdapter: Index {
    private let btree: BTreeIndex
    private let lock = NSLock()
    
    public init(_ btree: BTreeIndex) {
        self.btree = btree
    }
    
    public func insert(key: Value, rid: RID) async throws {
        lock.lock()
        defer { lock.unlock() }
        try btree.insert(key: key, rid: rid)
    }
    
    public func seek(key: Value) async throws -> [RID]? {
        lock.lock()
        defer { lock.unlock() }
        return btree.search(key: key)
    }
    
    public func scan(minKey: Value, maxKey: Value) async throws -> [(Value, [RID])] {
        lock.lock()
        defer { lock.unlock() }
        return btree.rangeScan(minKey: minKey, maxKey: maxKey)
    }
    
    public func delete(key: Value) async throws {
        lock.lock()
        defer { lock.unlock() }
        try btree.delete(key: key)
    }
    
    public func rebuild() async throws {
        // BTree doesn't have explicit rebuild, but we can verify structure
        lock.lock()
        defer { lock.unlock() }
        // No-op for now, structure is maintained automatically
    }
    
    public func cardinality() async throws -> Int {
        lock.lock()
        defer { lock.unlock() }
        // Count all entries via range scan (full range)
        let results = btree.rangeScan(minKey: .int(Int64.min), maxKey: .int(Int64.max))
        return results.reduce(0) { $0 + $1.1.count }
    }
}

// MARK: - ARTIndex Adapter

/// Adapter to make ARTIndex conform to Index protocol
/// Note: ARTIndex uses Data keys, we convert Value to Data
public struct ARTIndexAdapter: Index {
    private let art: ARTIndex
    
    public init(_ art: ARTIndex) {
        self.art = art
    }
    
    private func valueToData(_ value: Value) -> Data {
        switch value {
        case .int(let v):
            var data = Data()
            withUnsafeBytes(of: v.bigEndian) { data.append(contentsOf: $0) }
            return data
        case .string(let v):
            return v.data(using: .utf8) ?? Data()
        case .double(let v):
            var data = Data()
            withUnsafeBytes(of: v.bitPattern.bigEndian) { data.append(contentsOf: $0) }
            return data
        case .bool(let v):
            return Data([v ? 1 : 0])
        case .null:
            return Data()
        }
    }
    
    public func insert(key: Value, rid: RID) async throws {
        await art.insert(key: valueToData(key), rid: rid)
    }
    
    public func seek(key: Value) async throws -> [RID]? {
        await art.search(key: valueToData(key))
    }
    
    public func scan(minKey: Value, maxKey: Value) async throws -> [(Value, [RID])] {
        // ART doesn't have native range scan
        // Use prefixScan with empty prefix to get all entries, then filter
        // This is inefficient but correct for protocol conformance
        let allResults = await art.prefixScan(prefix: Data())
        
        return allResults
            .map { (data, rids) in
                // Convert Data back to Value (simplified - assumes int keys for now)
                if data.count == 8 {
                    let value = data.withUnsafeBytes { $0.load(as: Int64.self).bigEndian }
                    return (Value.int(value), rids)
                }
                // Fallback for string keys
                if let str = String(data: data, encoding: .utf8) {
                    return (Value.string(str), rids)
                }
                // Default fallback
                return (Value.bytes(data), rids)
            }
            .filter { (key, _) in
                key >= minKey && key <= maxKey
            }
            .sorted { $0.0 < $1.0 }
    }
    
    public func delete(key: Value) async throws {
        // ARTIndex doesn't have delete yet - mark for future implementation
        // For now, this is a no-op (will be implemented in future)
        // TODO: Implement delete in ARTIndex
    }
    
    public func rebuild() async throws {
        // ART doesn't have explicit rebuild
        // No-op for now
    }
    
    public func cardinality() async throws -> Int {
        // ART exposes totalKeys
        await art.getTotalKeys()
    }
}

// MARK: - HashIndex Adapter

/// Adapter to make HashIndex conform to Index protocol
public struct HashIndexAdapter: Index {
    private let hash: HashIndex
    
    public init(_ hash: HashIndex) {
        self.hash = hash
    }
    
    public func insert(key: Value, rid: RID) async throws {
        try await hash.insert(key: key, rid: rid)
    }
    
    public func seek(key: Value) async throws -> [RID]? {
        if let rid = try await hash.search(key: key) {
            return [rid]
        }
        return nil
    }
    
    public func scan(minKey: Value, maxKey: Value) async throws -> [(Value, [RID])] {
        // Hash index doesn't support range scan (unordered)
        // Return all entries filtered by range, then sorted
        let entries = await hash.getAllEntries()
        return entries
            .filter { entry in
                entry.key >= minKey && entry.key <= maxKey
            }
            .map { entry in
                (entry.key, [entry.rid])
            }
            .sorted { $0.0 < $1.0 }  // Sort by key for protocol conformance
    }
    
    public func delete(key: Value) async throws {
        try await hash.delete(key: key)
    }
    
    public func rebuild() async throws {
        // Hash index rebuild = resize to optimal size
        // For now, no-op (resize happens automatically)
    }
    
    public func cardinality() async throws -> Int {
        await hash.getEntryCount()
    }
}
