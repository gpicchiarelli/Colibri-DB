//
//  Errors.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Error lexicon translating engine mishaps into signals.

import Foundation
/// Database error types used across ColibrìDB.
/// Cases cover configuration, IO, invalid arguments, conflicts and not found conditions.

public enum DBError: Error, CustomStringConvertible {
    case notImplemented(String)
    case io(String)
    case config(String)
    case invalidArgument(String)
    case notFound(String)
    case conflict(String)
    case deadlock(String)
    case lockTimeout(String)
    case constraintViolation(String)

    /// Human‑readable error description.
    public var description: String {
        switch self {
        case .notImplemented(let m): return "NotImplemented: \(m)"
        case .io(let m): return "IO: \(m)"
        case .config(let m): return "Config: \(m)"
        case .invalidArgument(let m): return "InvalidArgument: \(m)"
        case .notFound(let m): return "NotFound: \(m)"
        case .conflict(let m): return "Conflict: \(m)"
        case .deadlock(let m): return "Deadlock: \(m)"
        case .lockTimeout(let m): return "LockTimeout: \(m)"
        case .constraintViolation(let m): return "ConstraintViolation: \(m)"
        }
    }
}

/// Database-specific error types
public enum DatabaseError: Error {
    case connectionFailed
    case queryTimeout
    case invalidSchema
}

/// Index-specific error types  
public enum IndexError: Error {
    case corruptedIndex
    case duplicateKey
    case missingIndex
}
