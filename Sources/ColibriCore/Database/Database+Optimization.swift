//
//  Database+Optimization.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Optimizer simulation lab estimating plan benefits and costs.

import Foundation
// MARK: - Optimization

extension Database {
    /// Simulates optimization (e.g., clustering/indexing) for the given columns.
    public func simulateOptimize(table: String, columns: [String]) -> OptimizationEstimate {
        let stats = tableStatistics[table] ?? {
            refreshTableStatistics(tables: [table])
            return tableStatistics[table]
        }()
        return simulator.estimate(table: table, columns: columns, tableStats: stats)
    }
}

