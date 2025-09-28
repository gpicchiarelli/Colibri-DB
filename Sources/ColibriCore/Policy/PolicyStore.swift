//
//  PolicyStore.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Rulebook preserving maintenance and retention policies.

import Foundation
/// In-memory policy store used by the optimizer and maintenance components.

public struct InMemoryPolicyStore: PolicyStoreProtocol {
    private var items: [Policy] = []
    public init() {}
    /// Returns all policies.
    public func list() -> [Policy] { items }
    /// Adds a policy.
    public mutating func add(_ policy: Policy) { items.append(policy) }
    /// Removes a policy by id; returns true if removed.
    public mutating func remove(id: UUID) -> Bool {
        if let idx = items.firstIndex(where: { $0.id == id }) {
            items.remove(at: idx)
            return true
        }
        return false
    }
}

