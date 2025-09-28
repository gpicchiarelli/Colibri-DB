//
//  TombstoneSet.swift
//  ColibrìDB
//
//  Created by GPT-5 Codex on 2025-09-28.
//
// ColibrìDB — BSD 3-Clause License

import Foundation

/// Utility container that tracks live references together with tombstones so
/// that deletes remain logical until compaction/vacuum clears them.
struct TombstoneSet<Ref: Hashable> {
    private(set) var live: Set<Ref> = []
    private(set) var tombstones: Set<Ref> = []

    init(live: Set<Ref> = [], tombstones: Set<Ref> = []) {
        self.live = live
        self.tombstones = tombstones
    }

    mutating func insert(_ ref: Ref) {
        tombstones.remove(ref)
        live.insert(ref)
    }

    mutating func insert<S: Sequence>(_ refs: S) where S.Element == Ref {
        for ref in refs { insert(ref) }
    }

    mutating func remove(_ ref: Ref) {
        if live.remove(ref) != nil {
            tombstones.insert(ref)
        }
    }

    mutating func delete(_ ref: Ref) {
        remove(ref)
    }

    mutating func remove<S: Sequence>(_ refs: S) where S.Element == Ref {
        for ref in refs { remove(ref) }
    }

    mutating func clearTombstone(_ ref: Ref) {
        tombstones.remove(ref)
    }

    mutating func clearVisible() {
        live.removeAll()
    }

    mutating func clearAll() {
        live.removeAll()
        tombstones.removeAll()
    }

    mutating func merge(with other: TombstoneSet<Ref>) {
        live.formUnion(other.live)
        tombstones.formUnion(other.tombstones)
    }

    func visible() -> [Ref] { Array(live) }
    func visibleSet() -> Set<Ref> { live }

    var hasLive: Bool { !live.isEmpty }
    var hasTombstones: Bool { !tombstones.isEmpty }
    var isEmpty: Bool { live.isEmpty && tombstones.isEmpty }
    var isDead: Bool { isEmpty }
}


