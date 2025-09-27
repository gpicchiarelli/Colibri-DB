//
//  Clock.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrìDB — BSD 3-Clause License

// Theme: Hybrid logical clock choreographing timestamp orderings.

import Foundation

/// Simple monotonic logical clock used to timestamp transactions for Clock-SI style scheduling.
final class SerializableClock {
    private let lock = NSLock()
    private var current: UInt64 = 1

    func next() -> UInt64 {
        lock.lock(); defer { lock.unlock() }
        let ts = current
        current &+= 1
        return ts
    }
}

