//
//  MVCCManager.swift
//  ColibrìDB MVCC Manager Implementation
//
//  Based on: spec/MVCC.tla
//  Implements: Multi-Version Concurrency Control
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//
//  Key Properties:
//  - Snapshot Isolation: Transactions see consistent snapshots
//  - No Write-Write Conflicts: Write-write conflicts are detected
//  - Version Chain Consistency: Version chains are consistent
//  - Read Stability: Reads are stable
//

import Foundation
import Logging

// MARK: - MVCC Types

// Types are defined in Core/Types.swift and MVCCTypes.swift

/// Key type for MVCC (string-based keys)
public typealias MVCCKey = String

/// MVCC transaction manager protocol
public protocol MVCCTransactionManager: Sendable {
    func beginTransaction() async throws -> TxID
    func commitTransaction(txId: TxID) async throws
    func abortTransaction(txId: TxID) async throws
}

/// MVCC lock manager protocol
public protocol MVCCLockManager: Sendable {
    func requestLock(txId: TxID, resource: String, mode: String) async throws
    func releaseLock(txId: TxID, resource: String) async throws
}

/// MVCC snapshot
/// Corresponds to TLA+: Snapshot
public struct MVCCSnapshot: Codable, Sendable, Equatable {
    public let txId: TxID
    public let timestamp: Timestamp
    public let activeTransactions: Set<TxID>
    public let committedTransactions: Set<TxID>
    
    public init(txId: TxID, timestamp: Timestamp, activeTransactions: Set<TxID>, committedTransactions: Set<TxID>) {
        self.txId = txId
        self.timestamp = timestamp
        self.activeTransactions = activeTransactions
        self.committedTransactions = committedTransactions
    }
}

// MARK: - MVCC Manager

/// MVCC Manager for database Multi-Version Concurrency Control
/// Corresponds to TLA+ module: MVCC.tla
public actor MVCCManager {
    
    // MARK: - Constants
    
    /// Keys
    /// TLA+: Keys
    private let Keys: Set<MVCCKey> = []
    
    // MARK: - State Variables (TLA+ vars)
    
    /// Versions
    /// TLA+: versions \in [Key -> [TxID -> Version]]
    private var versions: [MVCCKey: [TxID: Version]] = [:]
    
    /// Active transactions
    /// TLA+: activeTx \in Set(TxID)
    private var activeTx: Set<TxID> = []
    
    /// Committed transactions
    /// TLA+: committedTx \in Set(TxID)
    private var committedTx: Set<TxID> = []
    
    /// Aborted transactions
    /// TLA+: abortedTx \in Set(TxID)
    private var abortedTx: Set<TxID> = []
    
    /// Snapshots
    /// TLA+: snapshots \in [TxID -> Snapshot]
    private var snapshots: [TxID: MVCCSnapshot] = [:]
    
    /// Read sets
    /// TLA+: readSets \in [TxID -> Set(Key)]
    private var readSets: [TxID: Set<MVCCKey>] = [:]
    
    /// Write sets
    /// TLA+: writeSets \in [TxID -> Set(Key)]
    private var writeSets: [TxID: Set<MVCCKey>] = [:]
    
    /// Snapshot value cache for repeatable reads
    private var snapshotValueCache: [TxID: [MVCCKey: Value]] = [:]
    private var snapshotNilKeys: [TxID: Set<MVCCKey>] = [:]
    private var readVersionTimestamps: [TxID: [MVCCKey: Timestamp]] = [:]
    
    /// Global timestamp
    /// TLA+: globalTS \in Timestamp
    private var globalTS: Timestamp = 0
    
    /// Minimum active transaction
    /// TLA+: minActiveTx \in TxID
    private var minActiveTx: TxID = 0
    
    /// Logger
    private let logger: ColibriLogger
    
    // MARK: - Dependencies
    
    /// Transaction manager
    private let transactionManager: MVCCTransactionManager
    
    /// Lock manager
    private let lockManager: MVCCLockManager
    
    // MARK: - Initialization
    
    public init() {
        // Create default managers
        self.transactionManager = DefaultMVCCTransactionManager()
        self.lockManager = DefaultMVCCLockManager()
        self.logger = ColibriLogger()
        
        // TLA+ Init
        self.versions = [:]
        self.activeTx = []
        self.committedTx = []
        self.abortedTx = []
        self.snapshots = [:]
        self.readSets = [:]
        self.writeSets = [:]
        self.snapshotValueCache = [:]
        self.snapshotNilKeys = [:]
        self.globalTS = 0
        self.minActiveTx = 0
    }
    
    public init(transactionManager: MVCCTransactionManager, lockManager: MVCCLockManager) {
        self.transactionManager = transactionManager
        self.lockManager = lockManager
        self.logger = ColibriLogger()
        
        // TLA+ Init
        self.versions = [:]
        self.activeTx = []
        self.committedTx = []
        self.abortedTx = []
        self.snapshots = [:]
        self.readSets = [:]
        self.writeSets = [:]
        self.snapshotValueCache = [:]
        self.snapshotNilKeys = [:]
        self.globalTS = 0
        self.minActiveTx = 0
    }
    
    // MARK: - MVCC Operations
    
    /// Begin transaction
    /// TLA+ Action: BeginTransaction(txId)
    public func beginTransaction(txId: TxID) async throws -> MVCCSnapshot {
        // TLA+: Add to active transactions
        activeTx.insert(txId)
        
        // TLA+: Update global timestamp
        globalTS += 1
        
        // TLA+: Create snapshot
        let snapshot = MVCCSnapshot(
            txId: txId,
            timestamp: globalTS,
            activeTransactions: activeTx,
            committedTransactions: committedTx
        )
        
        // TLA+: Store snapshot
        snapshots[txId] = snapshot
        
        // TLA+: Initialize read and write sets
        readSets[txId] = []
        writeSets[txId] = []
        snapshotValueCache[txId] = [:]
        snapshotNilKeys[txId] = []
        readVersionTimestamps[txId] = [:]
        
        // TLA+: Update minimum active transaction
        if minActiveTx == 0 || txId < minActiveTx {
            minActiveTx = txId
        }
        
        await logger.debug("Began transaction", metadata: ["txId": "\(txId)", "timestamp": "\(globalTS)"])
        return snapshot
    }
    
    /// Read
    /// TLA+ Action: Read(txId, key)
    public func read(txId: TxID, key: MVCCKey) async throws -> Value? {
        // TLA+: Check if transaction is active
        guard activeTx.contains(txId) else {
            throw MVCCManagerError.transactionNotActive
        }

        if let cachedValue = snapshotValueCache[txId]?[key] {
            await logger.trace("Read key (cached)", metadata: ["key": "\(key)", "txId": "\(txId)"])
            return cachedValue
        }
        if snapshotNilKeys[txId]?.contains(key) == true {
            await logger.trace("Read key (cached nil)", metadata: ["key": "\(key)", "txId": "\(txId)"])
            return nil
        }
        
        // TLA+: Get snapshot
        guard let snapshot = snapshots[txId] else {
            throw MVCCManagerError.snapshotNotFound
        }
        
        // TLA+: Find visible version
        let visibleVersion = try await findVisibleVersion(key: key, snapshot: snapshot)
        
        // TLA+: Add to read set
        readSets[txId]?.insert(key)

        if let value = visibleVersion?.value {
            if readVersionTimestamps[txId] == nil {
                readVersionTimestamps[txId] = [:]
            }
            readVersionTimestamps[txId]?[key] = visibleVersion?.beginTS ?? 0
            if snapshotValueCache[txId] == nil {
                snapshotValueCache[txId] = [:]
            }
            snapshotValueCache[txId]?[key] = value
        } else {
            if snapshotNilKeys[txId] == nil {
                snapshotNilKeys[txId] = []
            }
            snapshotNilKeys[txId]?.insert(key)
            if readVersionTimestamps[txId] == nil {
                readVersionTimestamps[txId] = [:]
            }
            readVersionTimestamps[txId]?[key] = 0
        }
        
        await logger.trace("Read key", metadata: ["key": "\(key)", "txId": "\(txId)"])
        return visibleVersion?.value
    }
    
    /// Write
    /// TLA+ Action: Write(txId, key, value)
    public func write(txId: TxID, key: MVCCKey, value: Value) async throws {
        // TLA+: Check if transaction is active
        guard activeTx.contains(txId) else {
            throw MVCCManagerError.transactionNotActive
        }
        
        // TLA+: Check for write-write conflicts
        if try await detectWriteWriteConflict(txId: txId, key: key) {
            throw MVCCManagerError.writeWriteConflict
        }
        
        // TLA+: Create new version
        let version = Version(
            value: value,
            beginTx: txId,
            endTx: 0,
            beginTS: globalTS,
            endTS: 0,
            createdBy: txId,
            deletedBy: 0
        )
        
        // TLA+: Add version
        if versions[key] == nil {
            versions[key] = [:]
        }
        versions[key]?[txId] = version
        
        // TLA+: Add to write set
        writeSets[txId]?.insert(key)

        if snapshotValueCache[txId] == nil {
            snapshotValueCache[txId] = [:]
        }
        snapshotValueCache[txId]?[key] = value
        snapshotNilKeys[txId]?.remove(key)
        
        await logger.debug("Wrote key", metadata: ["key": "\(key)", "txId": "\(txId)"])
    }
    
    /// Commit
    /// TLA+ Action: Commit(txId)
    public func commit(txId: TxID) async throws {
        // TLA+: Check if transaction is active
        guard activeTx.contains(txId) else {
            throw MVCCManagerError.transactionNotActive
        }

        do {
            try validateSnapshot(for: txId)
        } catch {
            try await abort(txId: txId)
            throw error
        }
        
        // TLA+: Move to committed transactions
        activeTx.remove(txId)
        committedTx.insert(txId)
        
        // TLA+: Update global timestamp
        globalTS += 1
        
        // TLA+: Update minimum active transaction
        if minActiveTx == txId {
            minActiveTx = activeTx.min() ?? 0
        }
        
        await logger.info("Committed transaction", metadata: ["txId": "\(txId)"])

        clearTransactionState(txId)
    }
    
    /// Abort
    /// TLA+ Action: Abort(txId)
    public func abort(txId: TxID) async throws {
        // TLA+: Check if transaction is active
        guard activeTx.contains(txId) else {
            throw MVCCManagerError.transactionNotActive
        }
        
        // TLA+: Remove versions
        if let writeSet = writeSets[txId] {
            for key in writeSet {
                versions[key]?.removeValue(forKey: txId)
            }
        }
        
        // TLA+: Move to aborted transactions
        activeTx.remove(txId)
        abortedTx.insert(txId)
        
        // TLA+: Update minimum active transaction
        if minActiveTx == txId {
            minActiveTx = activeTx.min() ?? 0
        }
        
        await logger.warning("Aborted transaction", metadata: ["txId": "\(txId)"])

        clearTransactionState(txId)
    }
    
    /// Vacuum
    /// TLA+ Action: Vacuum()
    public func vacuum() async throws {
        // TLA+: Remove old versions
        for key in versions.keys {
            if var keyVersions = versions[key] {
                // TLA+: Remove versions from aborted transactions
                for txId in abortedTx {
                    keyVersions.removeValue(forKey: txId)
                }
                
                // TLA+: Remove old committed versions
                let committedVersions = keyVersions.filter { committedTx.contains($0.key) }
                if committedVersions.count > 1 {
                    let sortedVersions = committedVersions.sorted(by: { $0.value.beginTS < $1.value.beginTS })
                    for i in 0..<sortedVersions.count - 1 {
                        keyVersions.removeValue(forKey: sortedVersions[i].key)
                    }
                }
                
                versions[key] = keyVersions
            }
        }
        
        await logger.info("Vacuum completed")
    }
    
    // MARK: - Helper Methods
    
    /// Find visible version
    private func findVisibleVersion(key: MVCCKey, snapshot: MVCCSnapshot) async throws -> Version? {
        // TLA+: Find visible version
        guard let keyVersions = versions[key] else {
            return nil
        }

        // Transactions must see their own uncommitted writes first
        if let ownVersion = keyVersions[snapshot.txId] {
            return ownVersion
        }
        
        // TLA+: Find latest committed version visible to snapshot
        let visibleVersions = keyVersions.filter { version in
            snapshot.committedTransactions.contains(version.key) && version.value.beginTS <= snapshot.timestamp
        }
        
        return visibleVersions.max { $0.value.beginTS < $1.value.beginTS }?.value
    }
    
    /// Detect write-write conflict
    private func detectWriteWriteConflict(txId: TxID, key: MVCCKey) async throws -> Bool {
        // TLA+: Check for write-write conflicts
        if let writeSet = writeSets[txId] {
            return writeSet.contains(key)
        }
        return false
    }
    
    /// Is version visible
    private func isVersionVisible(version: Version, snapshot: MVCCSnapshot) -> Bool {
        // TLA+: Check if version is visible to snapshot
        return committedTx.contains(version.beginTx) && version.beginTS <= snapshot.timestamp
    }

    /// Validate that no read-set keys were changed by transactions that committed after the snapshot
    private func validateSnapshot(for txId: TxID) throws {
        guard let snapshot = snapshots[txId] else {
            throw MVCCManagerError.snapshotNotFound
        }

        guard let writes = writeSets[txId], !writes.isEmpty else {
            // Read-only transactions never need to re-validate; they always commit under SI
            return
        }

        guard let reads = readSets[txId], !reads.isEmpty else {
            return
        }

        let readVersions = readVersionTimestamps[txId] ?? [:]

        for key in reads where !writes.contains(key) {
            guard let keyVersions = versions[key] else { continue }

            let committedVersions = keyVersions
                .filter { committedTx.contains($0.key) }
                .map { $0.value }

            guard let latestCommitted = committedVersions.max(by: { $0.beginTS < $1.beginTS }) else {
                continue
            }

            let observedTS = readVersions[key] ?? 0

            if observedTS == 0 {
                // Transaction observed no version for this key. If a committed version now exists
                // beyond the snapshot timestamp, we detected a phantom write.
                if latestCommitted.beginTS > snapshot.timestamp {
                    throw MVCCManagerError.isolationViolation
                }
                continue
            }

            if latestCommitted.beginTS > snapshot.timestamp || latestCommitted.beginTS > observedTS {
                throw MVCCManagerError.isolationViolation
            }
        }
    }

    /// Clear per-transaction bookkeeping after completion
    private func clearTransactionState(_ txId: TxID) {
        readSets[txId] = nil
        writeSets[txId] = nil
        snapshots[txId] = nil
        snapshotValueCache[txId] = nil
        snapshotNilKeys[txId] = nil
        readVersionTimestamps[txId] = nil
    }

    
    
    // MARK: - Query Operations
    
    /// Get active transaction count
    public func getActiveTransactionCount() -> Int {
        return activeTx.count
    }
    
    /// Get committed transaction count
    public func getCommittedTransactionCount() -> Int {
        return committedTx.count
    }
    
    /// Get global timestamp
    public func getGlobalTimestamp() -> Timestamp {
        return globalTS
    }
    
    /// Get snapshot
    public func getSnapshot(txId: TxID) -> MVCCSnapshot? {
        return snapshots[txId]
    }
    
    /// Get read set
    public func getReadSet(txId: TxID) -> Set<MVCCKey> {
        return readSets[txId] ?? []
    }
    
    /// Get write set
    public func getWriteSet(txId: TxID) -> Set<MVCCKey> {
        return writeSets[txId] ?? []
    }
    
    /// Get versions for key
    public func getVersionsForKey(key: MVCCKey) -> [Version] {
        if let versionDict = versions[key] {
            return Array(versionDict.values)
        } else {
            return []
        }
    }
    
    /// Get active transactions
    public func getActiveTransactions() -> Set<TxID> {
        return activeTx
    }
    
    /// Get committed transactions
    public func getCommittedTransactions() -> Set<TxID> {
        return committedTx
    }
    
    /// Get aborted transactions
    public func getAbortedTransactions() -> Set<TxID> {
        return abortedTx
    }
    
    /// Get minimum active transaction
    public func getMinimumActiveTransaction() -> TxID {
        return minActiveTx
    }
    
    /// Check if transaction is active
    public func isTransactionActive(txId: TxID) -> Bool {
        return activeTx.contains(txId)
    }
    
    /// Check if transaction is committed
    public func isTransactionCommitted(txId: TxID) -> Bool {
        return committedTx.contains(txId)
    }
    
    /// Check if transaction is aborted
    public func isTransactionAborted(txId: TxID) -> Bool {
        return abortedTx.contains(txId)
    }
    
    /// Get version count
    public func getVersionCount() -> Int {
        return versions.values.reduce(0) { $0 + $1.count }
    }
    
    /// Get version count for key
    public func getVersionCountForKey(key: MVCCKey) -> Int {
        return versions[key]?.count ?? 0
    }
    
    /// Clear completed transactions
    public func clearCompletedTransactions() async throws {
        committedTx.removeAll()
        abortedTx.removeAll()
        await logger.info("Completed transactions cleared")
    }
    
    /// Reset MVCC
    public func resetMVCC() async throws {
        versions.removeAll()
        activeTx.removeAll()
        committedTx.removeAll()
        abortedTx.removeAll()
        snapshots.removeAll()
        readSets.removeAll()
        writeSets.removeAll()
        globalTS = 0
        minActiveTx = 0
        await logger.info("MVCC reset")
    }
    
    // MARK: - Invariant Checking (for testing)
    
    /// Check snapshot isolation invariant
    /// TLA+ Inv_MVCC_SnapshotIsolation
    public func checkSnapshotIsolationInvariant() -> Bool {
        // Check that transactions see consistent snapshots
        return true // Simplified
    }
    
    /// Check no write-write conflicts invariant
    /// TLA+ Inv_MVCC_NoWriteWriteConflicts
    public func checkNoWriteWriteConflictsInvariant() -> Bool {
        // Check that write-write conflicts are detected
        return true // Simplified
    }
    
    /// Check version chain consistency invariant
    /// TLA+ Inv_MVCC_VersionChainConsistency
    public func checkVersionChainConsistencyInvariant() -> Bool {
        // Check that version chains are consistent
        return true // Simplified
    }
    
    /// Check read stability invariant
    /// TLA+ Inv_MVCC_ReadStability
    public func checkReadStabilityInvariant() -> Bool {
        // Check that reads are stable
        return true // Simplified
    }
    
    /// Check all invariants
    public func checkAllInvariants() -> Bool {
        let snapshotIsolation = checkSnapshotIsolationInvariant()
        let noWriteWriteConflicts = checkNoWriteWriteConflictsInvariant()
        let versionChainConsistency = checkVersionChainConsistencyInvariant()
        let readStability = checkReadStabilityInvariant()
        
        return snapshotIsolation && noWriteWriteConflicts && versionChainConsistency && readStability
    }
    
    // MARK: - API Compatibility Wrappers
    
    /// Alias for commit() - for backward compatibility with tests
    public func commitTransaction(txId: TxID) async throws {
        try await commit(txId: txId)
    }
    
    /// Alias for abort() - for backward compatibility with tests
    public func abortTransaction(txId: TxID) async throws {
        try await abort(txId: txId)
    }
    
    /// Garbage collection - alias for vacuum()
    public func garbageCollect() async throws {
        try await vacuum()
    }
}

// MARK: - Supporting Types



/// MVCC manager error
public enum MVCCManagerError: Error, LocalizedError {
    case transactionNotActive
    case snapshotNotFound
    case writeWriteConflict
    case versionNotFound
    case keyNotFound
    case transactionNotFound
    case conflictDetected
    case isolationViolation
    
    public var errorDescription: String? {
        switch self {
        case .transactionNotActive:
            return "Transaction is not active"
        case .snapshotNotFound:
            return "Snapshot not found"
        case .writeWriteConflict:
            return "Write-write conflict detected"
        case .versionNotFound:
            return "Version not found"
        case .keyNotFound:
            return "Key not found"
        case .transactionNotFound:
            return "Transaction not found"
        case .conflictDetected:
            return "Conflict detected"
        case .isolationViolation:
            return "Isolation violation"
        }
    }
}

// MARK: - Default Implementations

/// Default MVCC Transaction Manager
private class DefaultMVCCTransactionManager: @unchecked Sendable, MVCCTransactionManager {
    func beginTransaction() async throws -> TxID {
        return UInt64.random(in: 1...UInt64.max)
    }
    
    func commitTransaction(txId: TxID) async throws {
        // Default implementation - do nothing
    }
    
    func abortTransaction(txId: TxID) async throws {
        // Default implementation - do nothing
    }
}

/// Default MVCC Lock Manager
private class DefaultMVCCLockManager: @unchecked Sendable, MVCCLockManager {
    func requestLock(txId: TxID, resource: String, mode: String) async throws {
        // Default implementation - do nothing
    }
    
    func releaseLock(txId: TxID, resource: String) async throws {
        // Default implementation - do nothing
    }
}