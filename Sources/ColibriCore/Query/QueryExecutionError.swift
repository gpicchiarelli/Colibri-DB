//
//  QueryExecutionError.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-27.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

import Foundation

/// Query execution errors
public enum QueryExecutionError: Error, LocalizedError {
    case operatorNotOpen
    case invalidQuery(String)
    case executionFailed(String)
    case timeout
    case resourceExhausted
    case invalidParameter(String)
    case unsupportedOperation(String)
    case invalidPredicate
    
    public var errorDescription: String? {
        switch self {
        case .operatorNotOpen:
            return "Query operator is not open"
        case .invalidQuery(let message):
            return "Invalid query: \(message)"
        case .executionFailed(let message):
            return "Query execution failed: \(message)"
        case .timeout:
            return "Query execution timeout"
        case .resourceExhausted:
            return "Query execution resource exhausted"
        case .invalidParameter(let message):
            return "Invalid parameter: \(message)"
        case .unsupportedOperation(let message):
            return "Unsupported operation: \(message)"
        case .invalidPredicate:
            return "Invalid predicate"
        }
    }
}
