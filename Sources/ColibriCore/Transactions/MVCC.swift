//
//  MVCC.swift
//  ColibrìDB
//
//  Created by Giacomo Picchiarelli on 2025-09-25.
//
// ColibrìDB — BSD 3-Clause License

// Theme: MVCC bureau supervising visibility timelines.

import Foundation

/// Multi-version concurrency control manager responsible for tracking row versions,
/// transaction visibility and garbage-collecting obsolete tuples once they become invisible
/// to every active transaction.
public final class MVCCManager {
    // MARK: - Nested types

    public enum Status: String, Codable { case inProgress, committed, aborted }
    public struct Version: Codable {
        var row: Row
        var beginTID: UInt64
        var beginStatus: Status
        var endTID: UInt64?
        var endStatus: Status?
        var createdAt: Date

        var isDeleted: Bool { endTID != nil && endStatus != .aborted }
    }

    public struct Snapshot {
        let tid: UInt64?
        let activeTIDs: Set<UInt64>
        let committedTIDs: Set<UInt64>
        /// Logical cutoff used to approximate snapshot visibility. Transactions with TID greater
        /// than this value are considered "future" relative to the snapshot and therefore invisible.
        let cutoffTID: UInt64
    }

    // MARK: - State

    private var tableVersions: [String: [RID: [Version]]] = [:]
    private(set) var activeTIDs: Set<UInt64> = []
    private(set) var committedTIDs: Set<UInt64> = [0]
    private(set) var abortedTIDs: Set<UInt64> = []
    private let lock = NSLock()

    // MARK: - Transaction lifecycle

    func begin(tid: UInt64) {
        lock.lock(); defer { lock.unlock() }
        activeTIDs.insert(tid)
    }

    func commit(tid: UInt64) {
        lock.lock(); defer { lock.unlock() }
        guard activeTIDs.remove(tid) != nil else { return }
        committedTIDs.insert(tid)
        updateVersions(for: tid, to: .committed)
    }

    func rollback(tid: UInt64) {
        lock.lock(); defer { lock.unlock() }
        guard activeTIDs.remove(tid) != nil else { return }
        abortedTIDs.insert(tid)
        updateVersions(for: tid, to: .aborted)
        purgeAbortedVersions(tid: tid)
    }

    // MARK: - Version registration

    func registerInsert(table: String, rid: RID, row: Row, tid: UInt64?) {
        lock.lock(); defer { lock.unlock() }
        var map = tableVersions[table] ?? [:]
        var chain = map[rid] ?? []
        let beginTid = tid ?? 0
        let beginStatus: Status = (tid == nil) ? .committed : .inProgress
        let newVersion = Version(row: row,
                                 beginTID: beginTid,
                                 beginStatus: beginStatus,
                                 endTID: nil,
                                 endStatus: nil,
                                 createdAt: Date())
        if let last = chain.last,
           last.endTID == nil,
           last.beginTID == beginTid,
           last.beginStatus == beginStatus,
           last.row == row {
            // idempotent insert (e.g. WAL replay)
            chain[chain.count - 1] = newVersion
        } else {
            chain.append(newVersion)
        }
        map[rid] = chain
        tableVersions[table] = map
        if beginStatus == .committed { committedTIDs.insert(beginTid) }
    }

    func registerDelete(table: String, rid: RID, row: Row, tid: UInt64?) {
        lock.lock(); defer { lock.unlock() }
        var map = tableVersions[table] ?? [:]
        var chain = map[rid] ?? []
        if chain.isEmpty {
            // Synthetic committed version for pre-existing tuple.
            chain.append(Version(row: row,
                                 beginTID: 0,
                                 beginStatus: .committed,
                                 endTID: nil,
                                 endStatus: nil,
                                 createdAt: Date()))
        }
        guard var last = chain.popLast() else {
            map[rid] = chain
            tableVersions[table] = map
            return
        }
        last.row = row
        last.endTID = tid ?? 0
        last.endStatus = (tid == nil) ? .committed : .inProgress
        chain.append(last)
        map[rid] = chain
        tableVersions[table] = map
    }

    func forceRemove(table: String, rid: RID) {
        lock.lock(); defer { lock.unlock() }
        tableVersions[table]?.removeValue(forKey: rid)
    }

    func undoInsert(table: String, rid: RID, tid: UInt64) {
        lock.lock(); defer { lock.unlock() }
        guard var map = tableVersions[table] else { return }
        guard var chain = map[rid] else { return }
        chain.removeAll { $0.beginTID == tid && $0.beginStatus != .committed }
        if chain.isEmpty {
            map.removeValue(forKey: rid)
        } else {
            map[rid] = chain
        }
        tableVersions[table] = map
    }

    func undoDelete(table: String, rid: RID, tid: UInt64) {
        lock.lock(); defer { lock.unlock() }
        guard var map = tableVersions[table], var chain = map[rid], let lastIndex = chain.indices.last else { return }
        if chain[lastIndex].endTID == tid {
            chain[lastIndex].endTID = nil
            chain[lastIndex].endStatus = nil
            map[rid] = chain
            tableVersions[table] = map
        }
    }

    // MARK: - Snapshot & visibility

    func snapshot(for tid: UInt64?, isolationCutoff: UInt64? = nil) -> Snapshot {
        lock.lock(); defer { lock.unlock() }
        let cutoff = isolationCutoff ?? tid ?? UInt64.max
        return Snapshot(tid: tid,
                        activeTIDs: activeTIDs,
                        committedTIDs: committedTIDs,
                        cutoffTID: cutoff)
    }

    func visibleRows(table: String, snapshot: Snapshot, readerTID: UInt64?) -> [RID: Row] {
        lock.lock(); defer { lock.unlock() }
        guard let map = tableVersions[table] else { return [:] }
        var result: [RID: Row] = [:]
        for (rid, chain) in map {
            guard let visible = latestVisibleVersion(chain: chain, snapshot: snapshot, readerTID: readerTID) else { continue }
            result[rid] = visible.row
        }
        return result
    }

    func minimumActiveTID() -> UInt64? {
        lock.lock(); defer { lock.unlock() }
        return activeTIDs.min()
    }

    func vacuum(table: String? = nil, cutoff: UInt64?) {
        lock.lock(); defer { lock.unlock() }
        let candidates = table.map { [$0] } ?? Array(tableVersions.keys)
        for name in candidates {
            guard var map = tableVersions[name] else { continue }
            for (rid, chain) in map {
                let pruned = chain.filter { version in
                    guard let endTid = version.endTID, let endStatus = version.endStatus else { return true }
                    guard endStatus == .committed else { return true }
                    if let cutoff = cutoff { return endTid >= cutoff }
                    return false
                }
                if pruned.isEmpty {
                    map.removeValue(forKey: rid)
                } else if pruned.count != chain.count {
                    map[rid] = pruned
                }
            }
            tableVersions[name] = map
        }
    }

    // MARK: - Internals

    private func latestVisibleVersion(chain: [Version], snapshot: Snapshot, readerTID: UInt64?) -> Version? {
        for version in chain.reversed() {
            if isVisible(version, snapshot: snapshot, readerTID: readerTID) {
                return version
            }
        }
        return nil
    }

    private func isVisible(_ version: Version, snapshot: Snapshot, readerTID: UInt64?) -> Bool {
        if version.beginStatus == .aborted { return false }
        if let reader = readerTID, reader == version.beginTID {
            if version.beginStatus == .inProgress {
                if let endTid = version.endTID, endTid == reader, version.endStatus == .inProgress {
                    return false
                }
                return true
            }
        }
        if version.beginStatus != .committed {
            return false
        }
        if version.beginTID > snapshot.cutoffTID && readerTID != version.beginTID {
            return false
        }
        if let endTid = version.endTID, let endStatus = version.endStatus {
            if let reader = readerTID, reader == endTid {
                return false
            }
            switch endStatus {
            case .aborted:
                return true
            case .inProgress:
                return endTid == readerTID
            case .committed:
                return endTid > snapshot.cutoffTID
            }
        }
        return true
    }

    private func updateVersions(for tid: UInt64, to status: Status) {
        for (table, map) in tableVersions {
            var updated = map
            for (rid, chain) in map {
                var newChain = chain
                var changed = false
                for index in newChain.indices {
                    if newChain[index].beginTID == tid {
                        newChain[index].beginStatus = status
                        changed = true
                    }
                    if newChain[index].endTID == tid {
                        if status == .aborted {
                            newChain[index].endTID = nil
                            newChain[index].endStatus = nil
                        } else {
                            newChain[index].endStatus = status
                        }
                        changed = true
                    }
                }
                if status == .aborted {
                    newChain.removeAll { $0.beginTID == tid && $0.endTID == nil && $0.beginStatus == .aborted }
                    if let lastIndex = newChain.indices.last,
                       newChain[lastIndex].endStatus == .aborted {
                        newChain[lastIndex].endTID = nil
                        newChain[lastIndex].endStatus = nil
                    }
                }
                if newChain.isEmpty {
                    updated.removeValue(forKey: rid)
                } else if changed {
                    updated[rid] = newChain
                }
            }
            tableVersions[table] = updated
        }
    }

    private func purgeAbortedVersions(tid: UInt64) {
        for (table, map) in tableVersions {
            var updated = map
            for (rid, chain) in map {
                let filtered = chain.filter { !($0.beginTID == tid && $0.beginStatus == .aborted) }
                if filtered.isEmpty {
                    updated.removeValue(forKey: rid)
                } else {
                    updated[rid] = filtered
                }
            }
            tableVersions[table] = updated
        }
    }
}

extension MVCCManager {
    func allVersions(for table: String) -> [RID: [Version]] {
        lock.lock(); defer { lock.unlock() }
        return tableVersions[table] ?? [:]
    }
}

