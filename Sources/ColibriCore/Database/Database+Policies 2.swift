//
//  Database+Policies.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrìDB — BSD 3-Clause License
// Copyright (c) 2025 Giacomo Picchiarelli
// Licensed under the BSD 3-Clause License. See LICENSE file.

// Theme: Policy office applying retention and scheduling rules.

import Foundation
// MARK: - Policies

extension Database {
    /// Adds an optimization/maintenance policy.
    public func addPolicy(_ p: Policy) {
        policyStore.add(p)
    }

    /// Returns all configured policies.
    public func listPolicies() -> [Policy] { policyStore.list() }

    /// Removes a policy by id; returns true if removed.
    public func removePolicy(id: UUID) -> Bool { policyStore.remove(id: id) }
}

