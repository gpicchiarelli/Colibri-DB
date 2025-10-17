//
//  LRUBufferPoolTests.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//

// Theme: Buffer pool drills ensuring namespace quotas and eviction order.

import Foundation
@_spi(Experimental) import Testing
@testable import ColibriCore

@Suite(.serialized)
struct LRUBufferPoolTests {
    @Test func clockEvictsUnpinnedPagesBeforePinnedOnes() throws {
        let testGroup = "test-buffer-\(UUID().uuidString)"
        BufferNamespaceManager.shared.setQuota(group: testGroup, pages: 100)

        var store: [PageID: Data] = [
            1: Data(repeating: 1, count: 8),
            2: Data(repeating: 2, count: 8),
            3: Data(repeating: 3, count: 8)
        ]
        var fetchCount: [PageID: Int] = [:]

        let pool = LRUBufferPool(pageSize: 8,
                                  capacityPages: 2,
                                  fetch: { pid in
                                      fetchCount[pid, default: 0] += 1
                                      return store[pid] ?? Data(repeating: 0, count: 8)
                                  },
                                  flush: { pid, data in
                                      store[pid] = data
                                  },
                                  namespace: "\(testGroup):pool",
                                  deferredWrite: false,
                                  maxDirty: 2)
        defer { pool.unpinPage(1) }

        pool.setEvictionPolicy(.clock)
        try pool.putPage(1, data: Data(repeating: 1, count: 8), dirty: false)
        _ = try pool.pinPage(1)

        try pool.putPage(2, data: Data(repeating: 2, count: 8), dirty: false)
        try pool.putPage(3, data: Data(repeating: 3, count: 8), dirty: false)

        let metrics = pool.metrics()
        #expect(metrics.pages == 2)

        fetchCount.removeAll()
        _ = try pool.getPage(2)
        #expect(fetchCount[2] == 1)
    }
}
