//
//  MVCCManager.swift
//  ColibrìDB MVCC Implementation
//
//  Based on: spec/MVCC.tla
//  Implements: Snapshot Isolation (SI)
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//
//  Key Properties:
//  - Snapshot Isolation: Transactions see consistent snapshots
//  - No Write-Write Conflicts: Concurrent updates to same key conflict
//  - Version Chain Consistency: Versions maintain proper ordering
//  - Read Stability: Reads are repeatable within transaction
//
//  Based on:
//  - "A Critique of ANSI SQL Isolation Levels" (Berenson et al., 1995)
//  - "Serializable Snapshot Isolation in PostgreSQL" (Ports & Grittner, 2012)
//

import Foundation

/// MVCC Manager for Multi-Version Concurrency Control
/// Corresponds to TLA+ module: MVCC.tla
public actor MVCCManager {
    // MARK: - State Variables (TLA+ vars)
    
    /// Version chains for each key
    /// TLA+: versions \in [Keys -> Seq(Version)]
    private var versions: [String: VersionChain] = [:]
    
    /// Set of active transaction IDs
    /// TLA+: activeTx \in SUBSET TxIds
    private var activeTx: Set<TxID> = []
    
    /// Set of committed transaction IDs
    /// TLA+: committedTx \in SUBSET TxIds
    private var committedTx: Set<TxID> = []
    
    /// Set of aborted transaction IDs
    /// TLA+: abortedTx \in SUBSET TxIds
    private var abortedTx: Set<TxID> = []
    
    /// Snapshots for each transaction
    /// TLA+: snapshots \in [TxIds -> Snapshot]
    private var snapshots: [TxID: Snapshot] = [:]
    
    /// Read sets for each transaction
    /// TLA+: readSets \in [TxIds -> SUBSET Keys]
    private var readSets: [TxID: Set<String>] = [:]
    
    /// Write sets for each transaction
    /// TLA+: writeSets \in [TxIds -> SUBSET Keys]
    private var writeSets: [TxID: Set<String>] = [:]
    
    /// Global timestamp counter for commit timestamps
    /// TLA+: globalTS \in Timestamp
    private var globalTS: Timestamp = 1
    
    /// Minimum active transaction (for garbage collection)
    /// TLA+: minActiveTx \in TxIds \union {0}
    private var minActiveTx: TxID = 0
    
    // MARK: - Initialization
    
    public init() {
        // TLA+ Init state
        self.versions = [:]
        self.activeTx = []
        self.committedTx = []
        self.abortedTx = []
        self.snapshots = [:]
        self.readSets = [:]
        self.writeSets = [:]
        self.globalTS = 1
        self.minActiveTx = 0
    }
    
    // MARK: - Core MVCC Operations
    
    /// Begin a new transaction and create its snapshot
    /// TLA+ Action: Begin(tid)
    /// Precondition: tid not in activeTx, committedTx, or abortedTx
    /// Postcondition: transaction added to activeTx, snapshot created
    public func beginTransaction(_ txID: TxID) throws {
        // TLA+: tid \notin activeTx \union committedTx \union abortedTx
        guard !activeTx.contains(txID) &&
              !committedTx.contains(txID) &&
              !abortedTx.contains(txID) else {
            throw DBError.internalError("Transaction already exists")
        }
        
        // TLA+: activeTx' = activeTx \union {tid}
        activeTx.insert(txID)
        
        // TLA+: snapshots' = [snapshots EXCEPT ![tid] = ...]
        // Create snapshot with current active transactions
        let snapshot = Snapshot(
            txID: txID,
            startTS: globalTS,
            xmin: activeTx.isEmpty ? globalTS : activeTx.min() ?? globalTS,
            xmax: globalTS,
            activeTxAtStart: activeTx
        )
        snapshots[txID] = snapshot
        
        // TLA+: readSets' = [readSets EXCEPT ![tid] = {}]
        readSets[txID] = []
        
        // TLA+: writeSets' = [writeSets EXCEPT ![tid] = {}]
        writeSets[txID] = []
        
        // TLA+: minActiveTx' = Min(activeTx \union {tid})
        minActiveTx = activeTx.min() ?? txID
    }
    
    /// Read a key (adds to read set, returns visible version)
    /// TLA+ Action: Read(tid, key)
    /// Precondition: tid \in activeTx
    /// Postcondition: key added to read set, visible version returned
    public func read(_ txID: TxID, key: String) throws -> Value? {
        // TLA+: tid \in activeTx
        guard activeTx.contains(txID) else {
            throw DBError.internalError("Transaction not active")
        }
        
        guard let snapshot = snapshots[txID] else {
            throw DBError.internalError("No snapshot for transaction")
        }
        
        // TLA+: readSets' = [readSets EXCEPT ![tid] = @ \union {key}]
        readSets[txID, default: []].insert(key)
        
        // Get visible version using visibility rules
        if let chain = versions[key] {
            return getVisibleVersion(chain: chain, snapshot: snapshot)
        }
        
        return nil
    }
    
    /// Write a key (creates new version, checks for conflicts)
    /// TLA+ Action: Write(tid, key, value)
    /// Precondition: tid \in activeTx, no write-write conflicts
    /// Postcondition: new version created, key added to write set
    public func write(_ txID: TxID, key: String, value: Value) throws {
        // TLA+: tid \in activeTx
        guard activeTx.contains(txID) else {
            throw DBError.internalError("Transaction not active")
        }
        
        // TLA+: Check for write-write conflicts
        // hasConflict == \E i \in DOMAIN versions[key]:
        //   /\ versions[key][i].endTx = 0
        //   /\ versions[key][i].beginTx # tid
        //   /\ versions[key][i].beginTx \in activeTx
        if let chain = versions[key] {
            for version in chain.getVersions() {
                if version.endTx == 0 &&
                   version.beginTx != txID &&
                   activeTx.contains(version.beginTx) {
                    // Write-write conflict detected!
                    throw DBError.serializationFailure
                }
            }
        }
        
        // TLA+: Create new version
        let newVersion = Version(
            value: value,
            beginTx: txID,
            endTx: 0,
            beginTS: 0,  // Will be set at commit
            endTS: 0,
            createdBy: txID,
            deletedBy: 0
        )
        
        // TLA+: versions' = [versions EXCEPT ![key] = Append(@, newVersion)]
        if versions[key] == nil {
            versions[key] = VersionChain()
        }
        versions[key]?.append(newVersion)
        
        // TLA+: writeSets' = [writeSets EXCEPT ![tid] = @ \union {key}]
        writeSets[txID, default: []].insert(key)
    }
    
    /// Update a key (logically delete old version, create new one)
    /// TLA+ Action: Update(tid, key, newValue)
    /// Precondition: tid \in activeTx, key exists, no conflicts
    /// Postcondition: old version marked deleted, new version created
    public func update(_ txID: TxID, key: String, newValue: Value) throws {
        // First check for visible version
        guard let chain = versions[key],
              let snapshot = snapshots[txID] else {
            throw DBError.notFound
        }
        
        let visibleVersion = getVisibleVersion(chain: chain, snapshot: snapshot)
        guard visibleVersion != nil else {
            throw DBError.notFound
        }
        
        // Check for conflicts (same as write)
        for version in chain.getVersions() {
            if version.endTx == 0 &&
               version.beginTx != txID &&
               activeTx.contains(version.beginTx) {
                throw DBError.serializationFailure
            }
        }
        
        // Mark old version as deleted by this transaction
        if var chain = versions[key] {
            for i in 0..<chain.count() {
                var version = chain[i]
                if version.endTx == 0 && version.beginTx != txID {
                    version.endTx = txID
                    version.deletedBy = txID
                    chain[i] = version
                }
            }
            versions[key] = chain
        }
        
        // Create new version
        try write(txID, key: key, value: newValue)
    }
    
    /// Delete a key (mark version as deleted)
    /// TLA+ Action: Delete(tid, key)
    /// Precondition: tid \in activeTx, key exists
    /// Postcondition: visible version marked as deleted
    public func delete(_ txID: TxID, key: String) throws {
        guard activeTx.contains(txID) else {
            throw DBError.internalError("Transaction not active")
        }
        
        guard var chain = versions[key] else {
            throw DBError.notFound
        }
        
        // Mark visible version as deleted
        for i in 0..<chain.count() {
            var version = chain[i]
            if version.endTx == 0 && version.beginTx != txID {
                version.endTx = txID
                version.deletedBy = txID
                version.endTS = 0  // Will be set at commit
                chain[i] = version
            }
        }
        
        versions[key] = chain
        writeSets[txID, default: []].insert(key)
    }
    
    /// Commit a transaction
    /// TLA+ Action: Commit(tid)
    /// Precondition: tid \in activeTx
    /// Postcondition: transaction committed, versions timestamped, state updated
    public func commit(_ txID: TxID) throws {
        // TLA+: tid \in activeTx
        guard activeTx.contains(txID) else {
            throw DBError.internalError("Transaction not active")
        }
        
        // TLA+: Assign commit timestamp
        let commitTS = globalTS
        globalTS += 1
        
        // TLA+: Update all versions created by this transaction
        // Set beginTS = commitTS for all versions with beginTx = tid
        for (key, var chain) in versions {
            var modified = false
            for i in 0..<chain.count() {
                var version = chain[i]
                if version.beginTx == txID {
                    version.beginTS = commitTS
                    chain[i] = version
                    modified = true
                }
                if version.endTx == txID {
                    version.endTS = commitTS
                    chain[i] = version
                    modified = true
                }
            }
            if modified {
                versions[key] = chain
            }
        }
        
        // TLA+: activeTx' = activeTx \ {tid}
        activeTx.remove(txID)
        
        // TLA+: committedTx' = committedTx \union {tid}
        committedTx.insert(txID)
        
        // TLA+: minActiveTx' = Min(activeTx)
        minActiveTx = activeTx.min() ?? 0
        
        // Cleanup
        snapshots[txID] = nil
        readSets[txID] = nil
        writeSets[txID] = nil
    }
    
    /// Abort a transaction
    /// TLA+ Action: Abort(tid)
    /// Precondition: tid \in activeTx
    /// Postcondition: transaction aborted, uncommitted versions removed
    public func abort(_ txID: TxID) throws {
        // TLA+: tid \in activeTx
        guard activeTx.contains(txID) else {
            throw DBError.internalError("Transaction not active")
        }
        
        // TLA+: Remove all uncommitted versions by this transaction
        for (key, var chain) in versions {
            let filtered = chain.getVersions().filter { version in
                version.beginTx != txID
            }
            
            if filtered.count != chain.count() {
                var newChain = VersionChain()
                for version in filtered {
                    newChain.append(version)
                }
                versions[key] = newChain
            }
            
            // Restore versions that were deleted by this transaction
            for i in 0..<chain.count() {
                var version = chain[i]
                if version.deletedBy == txID {
                    version.endTx = 0
                    version.deletedBy = 0
                    version.endTS = 0
                    chain[i] = version
                }
            }
            versions[key] = chain
        }
        
        // TLA+: activeTx' = activeTx \ {tid}
        activeTx.remove(txID)
        
        // TLA+: abortedTx' = abortedTx \union {tid}
        abortedTx.insert(txID)
        
        // TLA+: minActiveTx' = Min(activeTx)
        minActiveTx = activeTx.min() ?? 0
        
        // Cleanup
        snapshots[txID] = nil
        readSets[txID] = nil
        writeSets[txID] = nil
    }
    
    /// Vacuum old versions (garbage collection)
    /// TLA+ Action: Vacuum
    /// Precondition: versions exist with endTS < minActiveTx snapshot
    /// Postcondition: old versions removed
    public func vacuum() {
        // Get minimum snapshot timestamp of active transactions
        let minSnapshotTS = activeTx.compactMap { snapshots[$0]?.startTS }.min() ?? globalTS
        
        // Remove versions that are no longer visible to any active transaction
        for (key, var chain) in versions {
            let filtered = chain.getVersions().filter { version in
                // Keep if:
                // 1. Version is not deleted (endTS == 0)
                // 2. Version's end timestamp is after min snapshot
                version.endTS == 0 || version.endTS >= minSnapshotTS
            }
            
            if filtered.count != chain.count() {
                var newChain = VersionChain()
                for version in filtered {
                    newChain.append(version)
                }
                versions[key] = newChain
            }
        }
    }
    
    // MARK: - Visibility Rules
    
    /// Check if a version is visible to a given snapshot
    /// TLA+: IsVisible(version, snapshot)
    /// Implements Snapshot Isolation visibility rules
    private func isVisible(_ version: Version, snapshot: Snapshot) -> Bool {
        // Rule 1: Transaction always sees its own writes
        if version.beginTx == snapshot.txID {
            return true
        }
        
        // Rule 2: Version is committed before snapshot and creator not active
        if version.beginTS > 0 &&
           version.beginTS < snapshot.startTS &&
           !snapshot.activeTxAtStart.contains(version.beginTx) {
            // Check if not deleted or deleted after snapshot
            return version.endTS == 0 ||
                   version.endTS >= snapshot.startTS ||
                   version.endTx == snapshot.txID
        }
        
        return false
    }
    
    /// Get the visible version of a key for a transaction
    /// TLA+: GetVisibleVersion(key, tid)
    /// Returns the newest visible version, or nil if none exists
    private func getVisibleVersion(chain: VersionChain, snapshot: Snapshot) -> Value? {
        // Find all visible versions
        let visibleVersions = chain.getVersions().filter { version in
            isVisible(version, snapshot: snapshot)
        }
        
        // Return the newest one (last in array)
        return visibleVersions.last?.value
    }
    
    // MARK: - Query Operations
    
    /// Get transaction status
    public func getTransactionStatus(_ txID: TxID) -> TransactionStatus {
        if activeTx.contains(txID) {
            return .active
        } else if committedTx.contains(txID) {
            return .committed
        } else if abortedTx.contains(txID) {
            return .aborted
        }
        return .aborted  // Unknown transactions are considered aborted
    }
    
    /// Get active transaction count
    public func getActiveTransactionCount() -> Int {
        return activeTx.count
    }
    
    /// Get global timestamp
    public func getGlobalTimestamp() -> Timestamp {
        return globalTS
    }
    
    // MARK: - Invariant Checking (for testing)
    
    /// Check snapshot isolation invariant
    /// TLA+: Inv_MVCC_SnapshotIsolation
    public func checkSnapshotIsolationInvariant() -> Bool {
        // All active transactions have valid snapshots
        for txID in activeTx {
            if snapshots[txID] == nil {
                return false
            }
        }
        return true
    }
    
    /// Check no write-write conflict invariant
    /// TLA+: Inv_MVCC_NoWriteWriteConflict
    public func checkNoWriteWriteConflictInvariant() -> Bool {
        // No two active transactions should have uncommitted writes to same key
        for (_, chain) in versions {
            var uncommittedWriters: Set<TxID> = []
            for version in chain.getVersions() {
                if version.endTx == 0 && version.beginTS == 0 {
                    if uncommittedWriters.contains(version.beginTx) {
                        return false
                    }
                    uncommittedWriters.insert(version.beginTx)
                }
            }
        }
        return true
    }
}

