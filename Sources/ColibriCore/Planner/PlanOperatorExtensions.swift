//
//  PlanOperatorExtensions.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-01-27.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

import Foundation

// MARK: - Default implementations for PlanOperator

extension PlanOperator {
    /// Default implementation of next() without context parameter
    public func next() throws -> PlanRow? {
        // This is a placeholder - subclasses should override
        return nil
    }
    
    /// Default implementation of close() without context parameter
    public func close() throws {
        // This is a placeholder - subclasses should override
    }
    
    /// Default implementation of materialize() without context parameter
    public func materialize() throws -> [PlanRow] {
        // This is a placeholder - subclasses should override
        return []
    }
}

// MARK: - Helper functions for context handling

extension PlanOperator {
    /// Helper to get context from ExecutionContext
    internal func getContext(from context: ExecutionContext) -> ExecutionContext {
        return context
    }
}
