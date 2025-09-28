//
//  FaultInjector.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrDB — BSD 3-Clause License

// Theme: Fault injection control panel toggling chaos scenarios.

import Foundation

/// Simple fault injection utility for testing crash/failure scenarios.
/// Keys are arbitrary strings; when a counter reaches zero, an error should be thrown.
public final class FaultInjector: @unchecked Sendable {
    public static let shared = FaultInjector()
    private init() {}
    private var counters: [String: Int] = [:]
    private let lock = NSLock()

    public func set(key: String, remaining: Int) {
        lock.lock(); defer { lock.unlock() }
        counters[key] = max(0, remaining)
    }

    public func clear(key: String? = nil) {
        lock.lock(); defer { lock.unlock() }
        if let k = key { counters.removeValue(forKey: k) } else { counters.removeAll() }
    }

    public func shouldFail(key: String) -> Bool {
        lock.lock(); defer { lock.unlock() }
        guard let n = counters[key] else { return false }
        if n <= 0 { return false }
        counters[key] = n - 1
        return n - 1 == 0
    }
}

