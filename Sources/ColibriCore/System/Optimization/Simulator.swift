//
//  Simulator.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Simulation arena projecting maintenance and query impacts.

import Foundation
/// Toy optimization simulator that estimates clustering/indexing benefits.

public struct SimpleOptimizationSimulator: OptimizationSimulatorProtocol {
    public init() {}
    /// Estimates time, temp space, and benefit for optimizing a set of columns.
    public func estimate(table: String, columns: [String], tableStats: TableStatistics?) -> OptimizationEstimate {
        let cols = max(1, columns.count)
        var estimatedSeconds: Double = 30.0 * Double(cols)
        var tempSpace: UInt64 = 256 * 1024 * 1024
        var benefit: Double = min(0.8, 0.2 + Double(cols) * 0.2)
        if let stats = tableStats {
            let avgRowSize = max(64.0, stats.avgRowSizeBytes)
            let rowCount = max(1, stats.rowCount)
            let dataBytes = avgRowSize * Double(rowCount)
            let dataMB = dataBytes / (1024.0 * 1024.0)
            let fragmentation = stats.fragmentation?.fragmentationRatio ?? 0.0
            let fragmentationFactor = 1.0 + fragmentation * 2.0
            let throughputMBps = 80.0 // assumed disk throughput for clustering
            estimatedSeconds = max(0.5, (dataMB / throughputMBps) * Double(cols)) * fragmentationFactor
            let tempMultiplier = min(0.5, 0.10 + fragmentation * 0.4)
            tempSpace = UInt64(max(64.0, dataBytes * tempMultiplier))
            let deadFraction = rowCount == 0 ? 0.0 : Double(stats.deadRowCount) / Double(rowCount)
            benefit = min(0.95, 0.3 + fragmentation * 0.5 + deadFraction * 0.3)
        }
        return OptimizationEstimate(estimatedSeconds: estimatedSeconds, tempSpaceBytes: tempSpace, expectedBenefit: benefit)
    }
}

