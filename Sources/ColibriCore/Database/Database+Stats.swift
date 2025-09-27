//
//  Database+Stats.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Stats observatory collecting telemetry for optimizations.

import Foundation
// MARK: - Stats

extension Database {
    /// Returns aggregate metrics across all buffer pools as numeric values.
    public func bufferPoolAggregateNumbers() -> (hits: UInt64, misses: UInt64, evictions: UInt64, pages: Int, capacity: Int, pinned: Int, dirty: Int) {
        var totalHits: UInt64 = 0
        var totalMisses: UInt64 = 0
        var totalEv: UInt64 = 0
        var totalPages = 0
        var totalCap = 0
        var totalPinned = 0
        var totalDirty = 0
        for (_, ft) in tablesFile {
            if let m = ft.poolMetrics() {
                totalHits &+= m.hits; totalMisses &+= m.misses; totalEv &+= m.evictions
                totalPages += m.pages; totalCap += m.capacity; totalPinned += m.pinned; totalDirty += m.dirty
            }
        }
        for (_, imap) in indexes {
            for (_, pair) in imap {
                if case .persistentBTree(let f) = pair.backend, let m = f.poolMetrics() {
                    totalHits &+= m.hits; totalMisses &+= m.misses; totalEv &+= m.evictions
                    totalPages += m.pages; totalCap += m.capacity; totalPinned += m.pinned; totalDirty += m.dirty
                }
            }
        }
        return (totalHits, totalMisses, totalEv, totalPages, totalCap, totalPinned, totalDirty)
    }
    /// Returns a list of human-readable buffer pool stats for tables and indexes.
    public func bufferPoolStats() -> [String] {
        var lines: [String] = []
        for (t, ft) in tablesFile {
            lines.append("table=\(t) pool=\(ft.statsString())")
        }
        for (t, imap) in indexes {
            for (name, pair) in imap {
                switch pair.backend {
                case .anyString:
                    lines.append("index=\(t).\(name) pool=n/a")
                case .persistentBTree(let f):
                    lines.append("index=\(t).\(name) \(f.dumpHeader(pageId: nil))")
                }
            }
        }
        return lines
    }

    /// Returns an aggregate summary of buffer pool metrics across all pools.
    public func bufferPoolAggregateStats() -> String {
        var totalHits: UInt64 = 0
        var totalMisses: UInt64 = 0
        var totalEv: UInt64 = 0
        var totalPages = 0
        var totalCap = 0
        var totalPinned = 0
        var totalDirty = 0
        for (_, ft) in tablesFile {
            if let m = ft.poolMetrics() { totalHits &+= m.hits; totalMisses &+= m.misses; totalEv &+= m.evictions; totalPages += m.pages; totalCap += m.capacity; totalPinned += m.pinned; totalDirty += m.dirty }
        }
        for (_, imap) in indexes {
            for (_, pair) in imap {
                if case .persistentBTree(let f) = pair.backend { if let m = f.poolMetrics() { totalHits &+= m.hits; totalMisses &+= m.misses; totalEv &+= m.evictions; totalPages += m.pages; totalCap += m.capacity; totalPinned += m.pinned; totalDirty += m.dirty } }
            }
        }
        return "buffers total: hits=\(totalHits) misses=\(totalMisses) evictions=\(totalEv) pages=\(totalPages)/\(totalCap) pinned=\(totalPinned) dirty=\(totalDirty)"
    }

    /// Refreshes optimizer statistics for the provided tables (or all tables).
    public func refreshTableStatistics(tables: [String]? = nil, sampleRows: Int? = nil) {
        let target: [String]
        if let t = tables {
            target = t
        } else {
            target = Array(Set(tablesFile.keys).union(tablesMem.keys))
        }
        let limit = max(1, sampleRows ?? config.optimizerStatsSampleRows)
        for table in target {
            let sample = sampleTableRows(table: table, limit: limit)
            var fragmentation = cachedTableStats[table]
            if fragmentation == nil, let storage = tablesFile[table] {
                fragmentation = try? storage.fragmentationStats(samplePages: config.heapFragmentationSamplePages)
                if let frag = fragmentation { cachedTableStats[table] = frag }
            }
            let rowCountFromFrag = fragmentation?.liveTupleCount ?? 0
            let rowCount = sample.totalRows > 0 ? sample.totalRows : rowCountFromFrag
            let deadRows = fragmentation?.deadTupleCount ?? 0
            let avgRowSize: Double
            if let frag = fragmentation, frag.liveTupleCount > 0 {
                avgRowSize = Double(frag.liveBytes) / Double(frag.liveTupleCount)
            } else {
                avgRowSize = sample.avgRowSize
            }
            let stats = TableStatistics(table: table,
                                        rowCount: rowCount,
                                        deadRowCount: deadRows,
                                        avgRowSizeBytes: avgRowSize,
                                        fragmentation: fragmentation,
                                        columnCardinality: sample.columnCardinality,
                                        sampledRowCount: sample.sampledRows,
                                        updatedAt: Date())
            tableStatistics[table] = stats
            var tableStatsMap: [String: Double] = ["rowCount": Double(rowCount)]
            tableStatsMap["deadRowCount"] = Double(deadRows)
            tableStatsMap["avgRowSizeBytes"] = avgRowSize
            if let frag = fragmentation {
                tableStatsMap["fragmentationRatio"] = frag.fragmentationRatio
                tableStatsMap["freeBytes"] = Double(frag.freeBytes)
                tableStatsMap["deadBytes"] = Double(frag.deadBytes)
            }
            systemCatalog?.registerStatistic(table: table,
                                             column: nil,
                                             stats: tableStatsMap,
                                             metadata: ["sampledRows": String(sample.sampledRows)])
            for (column, distinct) in sample.columnCardinality {
                systemCatalog?.registerStatistic(table: table,
                                                 column: column,
                                                 stats: ["distinctCount": Double(distinct)],
                                                 metadata: ["sampledRows": String(sample.sampledRows)])
            }
        }
    }

    /// Returns cached statistics for a specific table, if available.
    public func tableStats(_ table: String) -> TableStatistics? { tableStatistics[table] }

    /// Returns optimizer statistics for all tracked tables.
    public func allTableStatistics() -> [TableStatistics] { Array(tableStatistics.values) }

    /// Returns cached fragmentation statistics for a table if available.
    public func tableFragmentation(_ table: String) -> HeapFragmentationStats? { cachedTableStats[table] }

    private func sampleTableRows(table: String, limit: Int) -> (totalRows: Int, sampledRows: Int, columnCardinality: [String: Int], avgRowSize: Double) {
        guard let sequence = try? scan(table) else {
            return (0, 0, [:], 0.0)
        }
        var totalRows = 0
        var sampledRows = 0
        var distinct: [String: Set<Value>] = [:]
        var totalSampleBytes = 0
        let encoder = JSONEncoder()
        for (_, row) in sequence {
            totalRows &+= 1
            if sampledRows < limit {
                sampledRows &+= 1
                for (col, value) in row {
                    var set = distinct[col] ?? Set<Value>()
                    if set.count < limit { set.insert(value) }
                    distinct[col] = set
                }
                if let data = try? encoder.encode(row) {
                    totalSampleBytes &+= data.count
                }
            }
        }
        let avg = sampledRows > 0 ? Double(totalSampleBytes) / Double(sampledRows) : 0.0
        let counts = distinct.mapValues { $0.count }
        return (totalRows, sampledRows, counts, avg)
    }
}

