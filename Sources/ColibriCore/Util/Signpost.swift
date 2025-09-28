//
//  Signpost.swift
//  ColibrDB
//
//  Created by Giacomo Picchiarelli on 2025-09-26.
//
// ColibrDB — BSD 3-Clause License
//
// Theme: Lightweight wrapper around os_signpost with graceful no-op fallback.

import Foundation
#if canImport(os)
import os
#endif

/// Thin convenience layer to scope signpost usage without littering `#if` in callers.
/// Signposts are generated only on platforms that expose the unified logging APIs.
enum Signpost {
    enum Category {
        case flush
        case vacuum
        case planner
    }

#if canImport(os)
    private static let subsystem = "dev.colibridb.core"
    private static let flushLog = OSLog(subsystem: subsystem, category: "flush")
    private static let vacuumLog = OSLog(subsystem: subsystem, category: "vacuum")
    private static let plannerLog = OSLog(subsystem: subsystem, category: "planner")

    private static func log(for category: Category) -> OSLog {
        switch category {
        case .flush: return flushLog
        case .vacuum: return vacuumLog
        case .planner: return plannerLog
        }
    }
#endif

    struct Span {
#if canImport(os)
        fileprivate let id: OSSignpostID
        fileprivate let log: OSLog
        fileprivate let name: StaticString
        fileprivate init(id: OSSignpostID, log: OSLog, name: StaticString) {
            self.id = id
            self.log = log
            self.name = name
        }
#else
        fileprivate init() {}
#endif
    }

    /// Starts a signposted interval.
    /// - Parameters:
    ///   - category: Logical channel (flush/vacuum/planner).
    ///   - name: Stable identifier rendered in Instruments.
    ///   - message: Optional metadata string (public visibility).
    /// - Returns: Token to be fed back into `end` once the interval finishes.
    @discardableResult
    static func begin(_ category: Category, name: StaticString, message: String? = nil) -> Span {
#if canImport(os)
        let log = log(for: category)
        let id = OSSignpostID(log: log)
        if let message {
            os_signpost(.begin, log: log, name: name, signpostID: id, "%{public}s", message)
        } else {
            os_signpost(.begin, log: log, name: name, signpostID: id)
        }
        return Span(id: id, log: log, name: name)
#else
        _ = (category, name, message)
        return Span()
#endif
    }

    /// Ends a previously started signpost span.
    /// - Parameters:
    ///   - span: Span returned by `begin`.
    ///   - message: Optional metadata string printed on closure.
    static func end(_ span: Span, message: String? = nil) {
#if canImport(os)
        if let message {
            os_signpost(.end, log: span.log, name: span.name, signpostID: span.id, "%{public}s", message)
        } else {
            os_signpost(.end, log: span.log, name: span.name, signpostID: span.id)
        }
#else
        _ = span
        _ = message
#endif
    }

    /// Emits a one-shot diagnostic event for quick inspection.
    /// - Parameters:
    ///   - category: Logical channel.
    ///   - name: Display name in Instruments.
    ///   - message: Payload string.
    static func event(_ category: Category, name: StaticString, message: String) {
#if canImport(os)
        os_signpost(.event, log: log(for: category), name: name, "%{public}s", message)
#else
        _ = (category, name, message)
#endif
    }
}
