//
//  Database+Vacuum.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Vacuum scheduler steering background compaction passes.

import Foundation
// MARK: - Vacuum

extension Database {
    // MARK: - Vacuum background job
    /// Starts the periodic vacuum task that compacts heap pages.
    public func startVacuum(intervalSeconds: TimeInterval? = nil, pagesPerRun: Int? = nil) {
        stopVacuum()
        let interval = max(0.5, intervalSeconds ?? config.autoCompactionIntervalSeconds)
        let pages = pagesPerRun ?? config.autoCompactionPagesPerRun
        vacuumPagesPerRun = max(1, pages)
        let t = DispatchSource.makeTimerSource(queue: vacuumQueue)
        t.schedule(deadline: .now() + interval, repeating: interval)
        t.setEventHandler { [weak self] in self?.vacuumTick() }
        t.resume()
        vacuumTimer = t
    }

    /// Stops the periodic vacuum task.
    public func stopVacuum() { vacuumTimer?.cancel(); vacuumTimer = nil }

    /// Executes a single vacuum pass over a sliding window of pages.
    func vacuumTick() {
        guard !tablesFile.isEmpty else { return }
        let threshold = max(0.0, min(1.0, config.heapFragmentationThreshold))
        let minPages = max(1, config.heapFragmentationMinPages)
        let samplePages = max(1, config.heapFragmentationSamplePages)
        let span = Signpost.begin(.vacuum, name: "VacuumTick", message: "budget=\(vacuumPagesPerRun)")
        var statsForOptimizer: [String: HeapFragmentationStats] = [:]
        var hotTables: [(String, HeapFragmentationStats)] = []
        for (name, storage) in tablesFile {
            if storage.pageCount == 0 { continue }
            let stats = (try? storage.fragmentationStats(samplePages: samplePages)) ?? HeapFragmentationStats.empty(pageSize: storage.pageSize)
            statsForOptimizer[name] = stats
            if stats.totalPages >= minPages && stats.fragmentationRatio >= threshold {
                hotTables.append((name, stats))
            }
        }
        hotTables.sort { $0.1.fragmentationRatio > $1.1.fragmentationRatio }
        var pagesCompacted = 0
        var bytesReclaimed = 0
        var budget = vacuumPagesPerRun
        defer { Signpost.end(span, message: "pages=\(pagesCompacted) bytes=\(bytesReclaimed)") }

        if !hotTables.isEmpty {
            let share = max(1, budget / hotTables.count)
            for (name, _) in hotTables {
                guard budget > 0, let table = tablesFile[name] else { continue }
                let res = compactTable(name: name, table: table, maxPages: min(share, budget))
                budget -= res.attempted
                pagesCompacted += res.compacted
                bytesReclaimed += res.bytes
                if budget <= 0 { break }
            }
        }

        if budget > 0 {
            for (name, table) in tablesFile {
                guard budget > 0 else { break }
                let res = compactTable(name: name, table: table, maxPages: budget)
                budget -= res.attempted
                pagesCompacted += res.compacted
                bytesReclaimed += res.bytes
            }
        }

        vacuumRuns &+= 1
        vacuumTotalPagesCompacted &+= pagesCompacted
        vacuumTotalBytesReclaimed &+= bytesReclaimed
        vacuumLastRun = Date()
        mvcc.vacuum(table: nil, cutoff: mvcc.minimumActiveTID())
        if !statsForOptimizer.isEmpty {
            cachedTableStats.merge(statsForOptimizer) { _, new in new }
        }
        runIndexCompaction(sampleLeaves: samplePages)
    }

    private func compactTable(name: String, table: FileHeapTable, maxPages: Int) -> (attempted: Int, compacted: Int, bytes: Int) {
        guard maxPages > 0 else { return (0, 0, 0) }
        let total = table.pageCount
        if total == 0 { return (0, 0, 0) }
        var pid = vacuumPositions[name] ?? 1
        var attempted = 0
        var compacted = 0
        var bytes = 0
        var remaining = maxPages
        let span = Signpost.begin(.vacuum, name: "VacuumTable", message: name)
        defer {
            Signpost.end(span, message: "attempted=\(attempted) compacted=\(compacted) bytes=\(bytes)")
        }
        while remaining > 0 {
            if pid == 0 || pid > total { pid = 1 }
            if let gained = try? table.compactPage(pid) {
                if gained > 0 { compacted &+= 1; bytes &+= gained }
                attempted &+= 1
            }
            pid &+= 1
            remaining &-= 1
        }
        vacuumPositions[name] = pid
        return (attempted, compacted, bytes)
    }

    private func runIndexCompaction(sampleLeaves: Int) {
        guard !indexes.isEmpty else { return }
        let threshold = max(0.0, min(1.0, config.indexLeafOccupancyThreshold))
        let cooldown = max(0.0, config.indexCompactionCooldownSeconds)
        let now = Date()
        for (table, imap) in indexes {
            for (name, def) in imap {
                guard case .persistentBTree(let index) = def.backend else { continue }
                guard let occupancy = try? index.estimateLeafOccupancy(sampleLeaves: max(4, sampleLeaves / 2)) else { continue }
                if occupancy >= threshold { continue }
                let key = "\(table).\(name)"
                if let last = lastIndexCompaction[key], now.timeIntervalSince(last) < cooldown { continue }
                Signpost.event(.vacuum, name: "VacuumIndexCompact", message: "\(table).\(name) occ=\(String(format: "%.2f", occupancy))")
                try? index.compactPhysical()
                lastIndexCompaction[key] = now
            }
        }
    }

    /// Returns a summary line with vacuum metrics and last run timestamp.
    public func vacuumStats() -> String {
        let last = vacuumLastRun.map { ISO8601DateFormatter().string(from: $0) } ?? "never"
        return "vacuum runs=\(vacuumRuns) pages=\(vacuumTotalPagesCompacted) bytes=\(vacuumTotalBytesReclaimed) last=\(last)"
    }
}
