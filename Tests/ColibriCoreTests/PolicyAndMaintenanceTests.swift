//
//  PolicyAndMaintenanceTests.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//

// Theme: Policy tests verifying retention workflow narratives.

import Foundation
@_spi(Experimental) import Testing
@testable import ColibriCore

@Suite(.serialized)
struct PolicyAndMaintenanceTests {
    @Test func databasePolicyRoundTrip() throws {
        let tempDir = FileManager.default.temporaryDirectory.appendingPathComponent(UUID().uuidString, isDirectory: true)
        try FileManager.default.createDirectory(at: tempDir, withIntermediateDirectories: true)
        defer { try? FileManager.default.removeItem(at: tempDir) }

        var config = DBConfig(dataDir: tempDir.path)
        config.autoCompactionEnabled = false
        config.lockTimeoutSeconds = 1.0

        let db = Database(config: config)
        let policy = Policy(kind: .timeWindow, table: "orders", columns: ["order_date"], params: ["window": "02:00-05:00"])
        db.addPolicy(policy)

        let items = db.listPolicies()
        #expect(items.count == 1)
        #expect(items.first?.kind == .timeWindow)
        #expect(items.first?.params["window"] == "02:00-05:00")

        #expect(db.removePolicy(id: policy.id) == true)
        #expect(db.listPolicies().isEmpty)
    }

    @Test func optimizationSimulatorUsesStatistics() {
        let simulator = SimpleOptimizationSimulator()
        let baseline = simulator.estimate(table: "orders", columns: ["region", "sku"], tableStats: nil)

        let fragmentation = HeapFragmentationStats(pageSize: 8192,
                                                   totalPages: 1024,
                                                   sampledPages: 512,
                                                   liveTupleCount: 600_000,
                                                   deadTupleCount: 400_000,
                                                   liveBytes: 120_000_000,
                                                   deadBytes: 80_000_000,
                                                   freeBytes: 32_000_000,
                                                   fragmentationRatio: 0.7)
        let stats = TableStatistics(table: "orders",
                                    rowCount: 1_000_000,
                                    deadRowCount: 400_000,
                                    avgRowSizeBytes: 256.0,
                                    fragmentation: fragmentation,
                                    columnCardinality: ["region": 24, "sku": 50_000],
                                    sampledRowCount: 100_000,
                                    updatedAt: Date())

        let informed = simulator.estimate(table: "orders", columns: ["region", "sku"], tableStats: stats)

        #expect(informed.estimatedSeconds < baseline.estimatedSeconds)
        #expect(informed.tempSpaceBytes < baseline.tempSpaceBytes)
        #expect(informed.expectedBenefit > baseline.expectedBenefit)
    }

    @Test func bufferNamespaceQuotaIsEnforced() throws {
        BufferNamespaceManager.shared.setQuota(group: "table", pages: 100)

        let pageSize = 64
        var storeA: [PageID: Data] = [:]
        var storeB: [PageID: Data] = [:]

        let poolA = LRUBufferPool(pageSize: pageSize,
                                  capacityPages: 8,
                                  fetch: { pid in storeA[pid] ?? Data(repeating: 0, count: pageSize) },
                                  flush: { pid, data in storeA[pid] = data },
                                  namespace: "table:alpha",
                                  deferredWrite: false,
                                  maxDirty: 4)
        let poolB = LRUBufferPool(pageSize: pageSize,
                                  capacityPages: 8,
                                  fetch: { pid in storeB[pid] ?? Data(repeating: 0, count: pageSize) },
                                  flush: { pid, data in storeB[pid] = data },
                                  namespace: "table:beta",
                                  deferredWrite: false,
                                  maxDirty: 4)

        for id in 1...2 {
            try poolA.putPage(PageID(id), data: Data(repeating: UInt8(id), count: pageSize), dirty: false)
        }
        for id in 3...4 {
            try poolB.putPage(PageID(id), data: Data(repeating: UInt8(id), count: pageSize), dirty: false)
        }

        BufferNamespaceManager.shared.setQuota(group: "table", pages: 3)
        BufferNamespaceManager.shared.enforceQuota(for: "table")

        let metricsA = poolA.metrics()
        let metricsB = poolB.metrics()
        let totalPages = metricsA.pages + metricsB.pages
        let totalEvictions = metricsA.evictions + metricsB.evictions

        #expect(totalPages <= 3)
        #expect(totalEvictions > 0)

        BufferNamespaceManager.shared.setQuota(group: "table", pages: 100)
    }
}

