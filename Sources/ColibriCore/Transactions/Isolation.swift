//
//  Isolation.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrìDB — BSD 3-Clause License

// Theme: Isolation handbook mapping SQL levels to engine rules.

import Foundation

/// Supported transaction isolation levels.
public enum IsolationLevel: String, Codable, Sendable {
    case readCommitted
    case repeatableRead
    case snapshotIsolation
    case serializable

    /// Returns whether the level requires a consistent snapshot across the whole transaction.
    public var usesStableSnapshot: Bool {
        switch self {
        case .readCommitted:
            return false
        case .repeatableRead, .snapshotIsolation, .serializable:
            return true
        }
    }
}

