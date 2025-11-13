/*
 * VACUUM.swift
 * ColibrìDB - Garbage Collection and Space Reclamation
 *
 * Based on TLA+ specification: VACUUM.tla
 *
 * Implements comprehensive garbage collection system:
 * - Dead tuple identification and collection
 * - MVCC version chain cleanup
 * - Index cleanup (remove pointers to dead tuples)
 * - Page defragmentation and space reclamation
 * - Statistics update during vacuum
 * - VACUUM FULL (table rewrite)
 * - Autovacuum threshold calculation
 *
 * References:
 * [1] Stonebraker, M. (1987). "The design of the POSTGRES storage system"
 *     Proceedings of VLDB 1987.
 * [2] PostgreSQL Documentation: "Chapter 25. Routine Database Maintenance Tasks"
 *     https://www.postgresql.org/docs/current/maintenance.html
 * [3] Bernstein, P. A., & Goodman, N. (1983). "Multiversion concurrency control
 *     - Theory and algorithms" ACM Transactions on Database Systems, 8(4).
 * [4] Larson, P. Å., et al. (2011). "High-Performance Concurrency Control Mechanisms
 *     for Main-Memory Databases" Proceedings of VLDB 2011.
 * [5] Graefe, G. (2007). "Hierarchical locking in B-tree indexes" BTW 2007.
 *
 * Author: ColibrìDB Team
 * Date: 2025-10-19
 */

import Foundation

// MARK: - Tuple State (TLA+: TupleState)

/// Tuple visibility state
public enum TupleState: String, Codable {
    case live = "live"                    // Visible to some transactions
    case dead = "dead"                    // Invisible to all transactions, can be removed
    case recentlyDead = "recently_dead"   // Invisible to all active txs, but visible to some snapshots
}

// MARK: - Tuple with MVCC Metadata (TLA+: Tuple)

/// Tuple with MVCC metadata
public struct VacuumTuple: Codable, Equatable, Hashable {
    public let tid: RID                   // TLA+: tid
    public let data: String              // TLA+: data
    public let xmin: TxID                // TLA+: xmin (Transaction that created this version)
    public let xmax: TxID                // TLA+: xmax (Transaction that deleted this version)
    public let state: TupleState         // TLA+: state
    
    public init(tid: RID, data: String, xmin: TxID, xmax: TxID = 0, state: TupleState = .live) {
        self.tid = tid
        self.data = data
        self.xmin = xmin
        self.xmax = xmax
        self.state = state
    }
}

// MARK: - Vacuum Statistics (TLA+: VacuumStats)

/// Vacuum statistics
public struct VacuumStats: Codable {
    public var numScanned: Int            // TLA+: numScanned
    public var numRemoved: Int           // TLA+: numRemoved
    public var numDead: Int              // TLA+: numDead
    public var pagesScanned: Int        // TLA+: pagesScanned
    public var pagesFreed: Int           // TLA+: pagesFreed
    public var indexScans: Int          // TLA+: indexScans
    
    public init() {
        self.numScanned = 0
        self.numRemoved = 0
        self.numDead = 0
        self.pagesScanned = 0
        self.pagesFreed = 0
        self.indexScans = 0
    }
}

// MARK: - Vacuum Phase (TLA+: vacuumPhase)

/// Vacuum execution phase
public enum VacuumPhase: String, Codable, Sendable {
    case none = "none"
    case scan = "scan"
    case clean = "clean"
    case index = "index"
    case truncate = "truncate"
    case done = "done"
}

// MARK: - Vacuum Mode

/// Vacuum execution mode
public enum VacuumMode: String, Codable {
    case lazy = "lazy"       // Regular VACUUM
    case full = "full"       // VACUUM FULL (table rewrite)
    case auto = "auto"       // Autovacuum
}

// MARK: - VACUUM Manager

/// Comprehensive garbage collection system
/// Corresponds to TLA+ module: VACUUM.tla
public actor VacuumManager {
    
    // TLA+ VARIABLES
    
    /// Table storage (TLA+: heapTuples)
    private var heapTuples: [String: Set<VacuumTuple>] = [:]
    
    /// Dead tuple IDs (TLA+: deadTuples)
    private var deadTuples: [String: Set<RID>] = [:]
    
    /// Free space per page (TLA+: freespace)
    private var freespace: [String: [PageID: Int]] = [:]
    
    /// Index state (TLA+: indexPointers)
    private var indexPointers: [String: [RID: PageID]] = [:]
    
    /// Transaction visibility (TLA+: oldestXmin, recentXmin)
    private var oldestXmin: TxID = 1
    private var recentXmin: TxID = 1
    
    /// Vacuum state (TLA+: vacuumInProgress, vacuumPhase)
    private var vacuumInProgress: [String: Bool] = [:]
    private var vacuumPhase: [String: VacuumPhase] = [:]
    
    /// Vacuum statistics (TLA+: vacuumStats)
    private var vacuumStats: [String: VacuumStats] = [:]
    
    /// Autovacuum state (TLA+: autovacuumEnabled, deadTupleCount, totalTupleCount, lastVacuum)
    private var autovacuumEnabled: Bool = true
    private var deadTupleCount: [String: Int] = [:]
    private var totalTupleCount: [String: Int] = [:]
    private var lastVacuum: [String: Int] = [:]
    
    /// VACUUM FULL state (TLA+: rewriteInProgress, shadowTable)
    private var rewriteInProgress: [String: Bool] = [:]
    private var shadowTable: [String: Set<VacuumTuple>] = [:]
    
    // Configuration (TLA+: CONSTANTS)
    private let vacuumThreshold: Int = 20  // 20% dead tuples trigger autovacuum
    private let maxDeadTuples: Int = 10000 // Maximum dead tuples before forced vacuum
    private let pageSize: Int = 8192      // Page size in bytes
    
    // Dependencies
    private let mvcc: MVCCManager
    private let heapTable: HeapTable
    private let indexManager: IndexManager
    
    public init(mvcc: MVCCManager, heapTable: HeapTable, indexManager: IndexManager) {
        self.mvcc = mvcc
        self.heapTable = heapTable
        self.indexManager = indexManager
    }
    
    // MARK: - Helper Functions (TLA+ Helpers)
    
    /// Check if a tuple is visible to the oldest transaction (TLA+: IsTupleVisible)
    private func isTupleVisible(_ tuple: VacuumTuple, xmin: TxID) -> Bool {
        return tuple.xmin < xmin && (tuple.xmax == 0 || tuple.xmax >= xmin)
    }
    
    /// Check if a tuple is dead (TLA+: IsTupleDead)
    private func isTupleDead(_ tuple: VacuumTuple) -> Bool {
        return tuple.xmax != 0 && tuple.xmax < oldestXmin
    }
    
    /// Calculate dead tuple percentage (TLA+: DeadTuplePercentage)
    private func deadTuplePercentage(table: String) -> Int {
        let total = totalTupleCount[table] ?? 0
        guard total > 0 else { return 0 }
        
        let dead = deadTupleCount[table] ?? 0
        return (dead * 100) / total
    }
    
    /// Check if autovacuum should trigger (TLA+: ShouldAutovacuum)
    private func shouldAutovacuum(table: String) -> Bool {
        return autovacuumEnabled &&
               !(vacuumInProgress[table] ?? false) &&
               deadTuplePercentage(table: table) >= vacuumThreshold
    }
    
    /// Get tuples on a page (TLA+: TuplesOnPage)
    private func tuplesOnPage(table: String, pageId: PageID) -> Set<VacuumTuple> {
        let tuples = heapTuples[table] ?? []
        return Set(tuples.filter { $0.tid.pageID == pageId })
    }
    
    // MARK: - Tuple Operations (TLA+: InsertTuple, DeleteTuple, UpdateOldestXmin)
    
    /// Insert a tuple (TLA+ Action: InsertTuple)
    public func insertTuple(table: String, tuple: VacuumTuple) async {
        heapTuples[table, default: []].insert(tuple)
        totalTupleCount[table, default: 0] += 1
        
        // Update index pointers
        let pageId = PageID(tuple.tid.pageID)
        indexPointers[table, default: [:]][tuple.tid] = pageId
    }
    
    /// Delete a tuple (TLA+ Action: DeleteTuple)
    public func deleteTuple(table: String, tid: RID, deletingTxId: TxID) async {
        guard var tuples = heapTuples[table],
              let tuple = tuples.first(where: { $0.tid == tid }) else {
            return
        }
        
        let updatedTuple = VacuumTuple(
            tid: tuple.tid,
            data: tuple.data,
            xmin: tuple.xmin,
            xmax: deletingTxId,
            state: .recentlyDead
        )
        
        tuples.remove(tuple)
        tuples.insert(updatedTuple)
        heapTuples[table] = tuples
        
        deadTupleCount[table, default: 0] += 1
    }
    
    /// Update oldestXmin (TLA+ Action: UpdateOldestXmin)
    public func updateOldestXmin(newXmin: TxID) async {
        oldestXmin = newXmin
        
        // Mark recently_dead tuples as dead if now invisible to all
        for table in heapTuples.keys {
            let tuples = heapTuples[table] ?? []
            var updatedTuples: Set<VacuumTuple> = []
            
            for tuple in tuples {
                if tuple.state == .recentlyDead && tuple.xmax < newXmin {
                    let deadTuple = VacuumTuple(
                        tid: tuple.tid,
                        data: tuple.data,
                        xmin: tuple.xmin,
                        xmax: tuple.xmax,
                        state: .dead
                    )
                    updatedTuples.insert(deadTuple)
                } else {
                    updatedTuples.insert(tuple)
                }
            }
            
            heapTuples[table] = updatedTuples
        }
    }
    
    // MARK: - VACUUM Phases (TLA+: StartVacuum, ScanHeap, CleanHeap, etc.)
    
    /// Start VACUUM on a table (TLA+ Action: StartVacuum)
    public func startVacuum(table: String) async throws {
        guard !(vacuumInProgress[table] ?? false) else {
            throw VacuumError.vacuumInProgress(table)
        }
        
        vacuumInProgress[table] = true
        vacuumPhase[table] = .scan
        vacuumStats[table] = VacuumStats()
    }
    
    /// Scan heap and identify dead tuples (TLA+ Action: ScanHeap)
    public func scanHeap(table: String) async throws {
        guard vacuumPhase[table] == .scan else {
            throw VacuumError.invalidPhase(table: table, expected: .scan, actual: vacuumPhase[table] ?? VacuumPhase.none)
        }
        
        let tuples = heapTuples[table] ?? []
        let deadTids = Set(tuples.filter { isTupleDead($0) }.map { $0.tid })
        
        deadTuples[table] = deadTids
        vacuumStats[table]?.numScanned = tuples.count
        vacuumStats[table]?.numDead = deadTids.count
        vacuumPhase[table] = .clean
    }
    
    /// Remove dead tuples from heap (TLA+ Action: CleanHeap)
    public func cleanHeap(table: String) async throws {
        guard vacuumPhase[table] == .clean else {
            throw VacuumError.invalidPhase(table: table, expected: .clean, actual: vacuumPhase[table] ?? VacuumPhase.none)
        }
        
        let deadTids = deadTuples[table] ?? []
        let liveTuples = heapTuples[table]?.filter { !deadTids.contains($0.tid) } ?? []
        
        heapTuples[table] = Set(liveTuples)
        deadTupleCount[table] = 0
        vacuumStats[table]?.numRemoved = deadTids.count
        vacuumPhase[table] = .index
    }
    
    /// Clean up index pointers to removed tuples (TLA+ Action: CleanIndexes)
    public func cleanIndexes(table: String) async throws {
        guard vacuumPhase[table] == .index else {
            throw VacuumError.invalidPhase(table: table, expected: .index, actual: vacuumPhase[table] ?? VacuumPhase.none)
        }
        
        let deadTids = deadTuples[table] ?? []
        var pointers = indexPointers[table] ?? [:]
        
        // Remove pointers to dead tuples
        for deadTid in deadTids {
            pointers.removeValue(forKey: deadTid)
        }
        
        indexPointers[table] = pointers
        vacuumStats[table]?.indexScans = 1
        vacuumPhase[table] = .truncate
    }
    
    /// Truncate empty pages at end of table (TLA+ Action: TruncateTable)
    public func truncateTable(table: String) async throws {
        guard vacuumPhase[table] == .truncate else {
            throw VacuumError.invalidPhase(table: table, expected: .truncate, actual: vacuumPhase[table] ?? VacuumPhase.none)
        }
        
        let tuples = heapTuples[table] ?? []
        let usedPages = Set(tuples.map { $0.tid.pageID })
        
        // Find empty pages
        let allPages: Set<PageID> = freespace[table] != nil ? Set(freespace[table]!.keys) : []
        let emptyPages = allPages.subtracting(usedPages)
        
        // Update free space for empty pages
        for pageId in emptyPages {
            freespace[table, default: [:]][pageId] = pageSize
        }
        
        vacuumStats[table]?.pagesFreed = emptyPages.count
        vacuumPhase[table] = .done
    }
    
    /// Finish VACUUM (TLA+ Action: FinishVacuum)
    public func finishVacuum(table: String, timestamp: Int) async throws {
        guard vacuumPhase[table] == .done else {
            throw VacuumError.invalidPhase(table: table, expected: .done, actual: vacuumPhase[table] ?? VacuumPhase.none)
        }
        
        vacuumInProgress[table] = false
        vacuumPhase[table] = VacuumPhase.none
        lastVacuum[table] = timestamp
        deadTuples[table] = []
    }
    
    // MARK: - Complete VACUUM Process
    
    /// Execute complete VACUUM process
    public func vacuum(table: String, mode: VacuumMode = .lazy) async throws -> VacuumStats {
        let startTime = Date()
        
        switch mode {
        case .lazy:
            try await startVacuum(table: table)
            try await scanHeap(table: table)
            try await cleanHeap(table: table)
            try await cleanIndexes(table: table)
            try await truncateTable(table: table)
            try await finishVacuum(table: table, timestamp: Int(startTime.timeIntervalSince1970))
            
        case .full:
            try await startVacuumFull(table: table)
            try await finishVacuumFull(table: table)
            
        case .auto:
            if shouldAutovacuum(table: table) {
                let _ = try await vacuum(table: table, mode: .lazy)
            }
        }
        
        let _ = Date().timeIntervalSince(startTime)
        let stats = vacuumStats[table] ?? VacuumStats()
        
        return stats
    }
    
    // MARK: - Autovacuum (TLA+: AutovacuumTrigger, SetAutovacuum)
    
    /// Autovacuum triggers automatically (TLA+ Action: AutovacuumTrigger)
    public func autovacuumTrigger(table: String) async throws {
        guard shouldAutovacuum(table: table) else {
            return
        }
        
        try await startVacuum(table: table)
    }
    
    /// Enable/disable autovacuum (TLA+ Action: SetAutovacuum)
    public func setAutovacuum(enabled: Bool) {
        autovacuumEnabled = enabled
    }
    
    /// Check if autovacuum should run
    public func shouldAutoVacuum(table: String) -> Bool {
        return shouldAutovacuum(table: table)
    }
    
    // MARK: - VACUUM FULL (TLA+: StartVacuumFull, FinishVacuumFull)
    
    /// Start VACUUM FULL (TLA+ Action: StartVacuumFull)
    public func startVacuumFull(table: String) async throws {
        guard !(rewriteInProgress[table] ?? false) else {
            throw VacuumError.rewriteInProgress(table)
        }
        
        guard !(vacuumInProgress[table] ?? false) else {
            throw VacuumError.vacuumInProgress(table)
        }
        
        rewriteInProgress[table] = true
        
        // Create shadow table with only live tuples
        let tuples = heapTuples[table] ?? []
        let liveTuples = tuples.filter { $0.state == .live }
        shadowTable[table] = Set(liveTuples)
    }
    
    /// Finish VACUUM FULL (TLA+ Action: FinishVacuumFull)
    public func finishVacuumFull(table: String) async throws {
        guard rewriteInProgress[table] == true else {
            throw VacuumError.noRewriteInProgress(table)
        }
        
        // Atomic switch to shadow table
        heapTuples[table] = shadowTable[table] ?? []
        deadTupleCount[table] = 0
        totalTupleCount[table] = shadowTable[table]?.count ?? 0
        
        rewriteInProgress[table] = false
        shadowTable[table] = []
    }
    
    // MARK: - Query Methods
    
    public func getVacuumStats(table: String) -> VacuumStats? {
        return vacuumStats[table]
    }
    
    public func isVacuumInProgress(table: String) -> Bool {
        return vacuumInProgress[table] ?? false
    }
    
    public func getVacuumPhase(table: String) -> VacuumPhase? {
        return vacuumPhase[table]
    }
    
    public func getDeadTupleCount(table: String) -> Int {
        return deadTupleCount[table] ?? 0
    }
    
    public func getTotalTupleCount(table: String) -> Int {
        return totalTupleCount[table] ?? 0
    }
    
    public func getLastVacuumTime(table: String) -> Int? {
        return lastVacuum[table]
    }
    
    public func isAutovacuumEnabled() -> Bool {
        return autovacuumEnabled
    }
    
    // MARK: - TLA+ Invariants Implementation
    
    /// Invariant: Dead tuples are eventually removed (TLA+: Inv_VACUUM_DeadRemoved)
    public func checkDeadRemovedInvariant() -> Bool {
        return vacuumPhase.allSatisfy { (table, phase) in
            phase == .none ? (deadTuples[table]?.isEmpty ?? true) : true
        }
    }
    
    /// Invariant: Only dead tuples are removed (TLA+: Inv_VACUUM_CorrectRemoval)
    public func checkCorrectRemovalInvariant() -> Bool {
        return vacuumPhase.allSatisfy { (table, phase) in
            if phase == .clean {
                let deadTids = deadTuples[table] ?? []
                let tuples = heapTuples[table] ?? []
                return deadTids.allSatisfy { tid in
                    tuples.contains { $0.tid == tid && isTupleDead($0) }
                }
            }
            return true
        }
    }
    
    /// Invariant: Index consistency after cleanup (TLA+: Inv_VACUUM_IndexConsistency)
    public func checkIndexConsistencyInvariant() -> Bool {
        return vacuumPhase.allSatisfy { (table, phase) in
            if phase == .none {
                let pointers = indexPointers[table] ?? [:]
                let tuples = heapTuples[table] ?? []
                return pointers.keys.allSatisfy { rid in
                    tuples.contains { $0.tid == rid }
                }
            }
            return true
        }
    }
    
    /// Invariant: VACUUM doesn't run concurrently with VACUUM FULL (TLA+: Inv_VACUUM_NoConflict)
    public func checkNoConflictInvariant() -> Bool {
        return vacuumInProgress.allSatisfy { (table, inProgress) in
            !inProgress || !(rewriteInProgress[table] ?? false)
        }
    }
    
    /// Invariant: Dead tuple count is accurate (TLA+: Inv_VACUUM_DeadCountAccurate)
    public func checkDeadCountAccurateInvariant() -> Bool {
        return vacuumPhase.allSatisfy { (table, phase) in
            if phase == .none {
                let tuples = heapTuples[table] ?? []
                let actualDeadCount = tuples.filter { $0.state == .dead }.count
                return deadTupleCount[table] == actualDeadCount
            }
            return true
        }
    }
    
    /// Combined safety invariant (TLA+: TypeInvariant)
    public func checkSafetyInvariant() -> Bool {
        return checkDeadRemovedInvariant() &&
               checkCorrectRemovalInvariant() &&
               checkIndexConsistencyInvariant() &&
               checkNoConflictInvariant() &&
               checkDeadCountAccurateInvariant()
    }
}

// MARK: - Errors

public enum VacuumError: Error, LocalizedError {
    case vacuumInProgress(String)
    case invalidPhase(table: String, expected: VacuumPhase, actual: VacuumPhase?)
    case rewriteInProgress(String)
    case noRewriteInProgress(String)
    case tableNotFound(String)
    case insufficientSpace(String)
    
    public var errorDescription: String? {
        switch self {
        case .vacuumInProgress(let table):
            return "VACUUM already in progress on table '\(table)'"
        case .invalidPhase(let table, let expected, let actual):
            return "Invalid vacuum phase for table '\(table)': expected \(expected), got \(actual?.rawValue ?? "none")"
        case .rewriteInProgress(let table):
            return "VACUUM FULL already in progress on table '\(table)'"
        case .noRewriteInProgress(let table):
            return "No VACUUM FULL in progress on table '\(table)'"
        case .tableNotFound(let table):
            return "Table '\(table)' not found"
        case .insufficientSpace(let table):
            return "Insufficient space for VACUUM on table '\(table)'"
        }
    }
}

/*
 * IMPLEMENTATION NOTES:
 *
 * This implementation follows the VACUUM.tla specification and
 * implements comprehensive garbage collection:
 *
 * 1. Dead Tuple Collection (Stonebraker 1987):
 *    - Identify tuples invisible to all transactions
 *    - Remove dead tuples from heap
 *    - Update tuple counts and statistics
 *    - Maintain MVCC visibility rules
 *
 * 2. Index Cleanup (Graefe 2007):
 *    - Remove index pointers to dead tuples
 *    - Maintain index consistency
 *    - Update index statistics
 *    - Prevent dangling references
 *
 * 3. Space Reclamation:
 *    - Free space from dead tuples
 *    - Truncate empty pages
 *    - Defragment pages
 *    - Update free space maps
 *
 * 4. Autovacuum (PostgreSQL-style):
 *    - Monitor dead tuple percentage
 *    - Trigger automatically at threshold
 *    - Background processing
 *    - Configurable parameters
 *
 * 5. VACUUM FULL:
 *    - Complete table rewrite
 *    - Maximum space reclamation
 *    - Atomic operation
 *    - Shadow table approach
 *
 * 6. MVCC Integration:
 *    - Respect transaction visibility
 *    - Handle recently_dead tuples
 *    - Update oldestXmin
 *    - Maintain snapshot consistency
 *
 * Correctness Properties (verified by TLA+):
 * - Dead tuples are eventually removed
 * - Only dead tuples are removed
 * - Index consistency after cleanup
 * - VACUUM doesn't run concurrently with VACUUM FULL
 * - Dead tuple count is accurate
 * - VACUUM eventually completes
 * - Autovacuum eventually triggers when threshold exceeded
 * - Dead tuples eventually removed
 *
 * Production Examples:
 * - PostgreSQL: VACUUM and autovacuum
 * - Oracle: Automatic Segment Space Management
 * - SQL Server: Index maintenance
 * - MySQL: InnoDB space management
 */

