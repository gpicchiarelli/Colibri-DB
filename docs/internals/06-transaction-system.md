# Transaction System Internals

## Overview

ColibrìDB implements a comprehensive transaction system using Multi-Version Concurrency Control (MVCC) to provide ACID properties while enabling high concurrency. This chapter provides a detailed analysis of the transaction management, MVCC implementation, locking mechanisms, and concurrency control algorithms.

## MVCC Manager Architecture

### Class Structure

```swift
/// Multi-version concurrency control manager responsible for tracking row versions,
/// transaction visibility and garbage-collecting obsolete tuples once they become invisible
/// to every active transaction.
final class MVCCManager {
    // MARK: - Nested types

    enum Status: String, Codable { case inProgress, committed, aborted }

    struct Version: Codable {
        var row: Row
        var beginTID: UInt64
        var beginStatus: Status
        var endTID: UInt64?
        var endStatus: Status?
        var createdAt: Date

        var isDeleted: Bool { endTID != nil && endStatus != .aborted }
    }

    struct Snapshot {
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
}
```

**Detailed Analysis:**

#### Core Data Structures

##### `Status` Enum
```swift
enum Status: String, Codable { case inProgress, committed, aborted }
```
- **`inProgress`**: Transaction is currently executing
- **`committed`**: Transaction has been successfully committed
- **`aborted`**: Transaction has been rolled back
- **`Codable`**: Enables serialization for persistence
- **`String`**: Human-readable status representation

##### `Version` Struct
```swift
struct Version: Codable {
    var row: Row
    var beginTID: UInt64
    var beginStatus: Status
    var endTID: UInt64?
    var endStatus: Status?
    var createdAt: Date

    var isDeleted: Bool { endTID != nil && endStatus != .aborted }
}
```

**Field Analysis:**
- **`row: Row`**: The actual data row
- **`beginTID: UInt64`**: Transaction ID that created this version
- **`beginStatus: Status`**: Status of the creating transaction
- **`endTID: UInt64?`**: Transaction ID that ended this version (optional)
- **`endStatus: Status?`**: Status of the ending transaction (optional)
- **`createdAt: Date`**: Timestamp when version was created
- **`isDeleted: Bool`**: Computed property indicating if version is deleted

**Memory Layout:**
```
Version Layout (Variable Size):
┌─────────────┬─────────────┬─────────────┬─────────────┐
│ Row Data    │ Begin TID   │ Begin Status│ End TID     │
│ (Variable)  │ (8 bytes)   │ (1 byte)    │ (8 bytes)   │
├─────────────┼─────────────┼─────────────┼─────────────┤
│ End Status  │ Created At  │ Padding     │             │
│ (1 byte)    │ (8 bytes)   │ (Variable)  │             │
└─────────────┴─────────────┴─────────────┴─────────────┘
```

##### `Snapshot` Struct
```swift
struct Snapshot {
    let tid: UInt64?
    let activeTIDs: Set<UInt64>
    let committedTIDs: Set<UInt64>
    let cutoffTID: UInt64
}
```

**Field Analysis:**
- **`tid: UInt64?`**: Transaction ID taking the snapshot
- **`activeTIDs: Set<UInt64>`**: Set of currently active transaction IDs
- **`committedTIDs: Set<UInt64>`**: Set of committed transaction IDs
- **`cutoffTID: UInt64`**: Logical cutoff for visibility determination

**Usage:**
- **Visibility**: Determines which versions are visible to a transaction
- **Consistency**: Ensures consistent point-in-time view
- **Isolation**: Provides transaction isolation

#### State Management

##### `tableVersions: [String: [RID: [Version]]]`
- **Outer Key**: Table name (String)
- **Middle Key**: Record ID (RID)
- **Inner Value**: Array of versions for the record
- **Purpose**: Stores all versions of all records in all tables
- **Memory**: O(n) where n is total number of versions

##### Transaction ID Sets
- **`activeTIDs: Set<UInt64>`**: Currently active transactions
- **`committedTIDs: Set<UInt64>`**: Successfully committed transactions
- **`abortedTIDs: Set<UInt64>`**: Rolled back transactions
- **Purpose**: Track transaction states for visibility
- **Performance**: O(1) for membership checks

##### Synchronization
- **`lock: NSLock`**: Protects all state modifications
- **Thread Safety**: Ensures atomic operations
- **Performance**: O(1) for lock acquisition
- **Deadlock Prevention**: Single lock prevents deadlocks

### Transaction Lifecycle

#### Begin Transaction

```swift
func begin(tid: UInt64) {
    lock.lock(); defer { lock.unlock() }
    activeTIDs.insert(tid)
}
```

**Detailed Analysis:**

#### Process
1. **Lock Acquisition**: Acquire exclusive lock
2. **TID Registration**: Add transaction ID to active set
3. **Lock Release**: Release lock automatically via defer

#### Performance
- **Lock Acquisition**: O(1) operation
- **Set Insertion**: O(1) average case
- **Total Time**: O(1) operation
- **Memory**: O(1) memory allocation

#### Thread Safety
- **Exclusive Lock**: Prevents concurrent modifications
- **Atomic Operation**: Begin is atomic
- **State Consistency**: Ensures consistent state

#### Commit Transaction

```swift
func commit(tid: UInt64) {
    lock.lock(); defer { lock.unlock() }
    guard activeTIDs.remove(tid) != nil else { return }
    committedTIDs.insert(tid)
    updateVersions(for: tid, to: .committed)
}
```

**Detailed Analysis:**

#### Process
1. **Lock Acquisition**: Acquire exclusive lock
2. **TID Removal**: Remove from active set
3. **TID Registration**: Add to committed set
4. **Version Update**: Update all versions created by transaction
5. **Lock Release**: Release lock automatically

#### Error Handling
- **Guard Check**: Ensure transaction was active
- **Early Return**: Return if transaction not found
- **Idempotent**: Safe to call multiple times

#### Performance
- **Lock Acquisition**: O(1) operation
- **Set Operations**: O(1) for remove and insert
- **Version Update**: O(n) where n is number of versions
- **Total Time**: O(n) where n is number of versions

#### Rollback Transaction

```swift
func rollback(tid: UInt64) {
    lock.lock(); defer { lock.unlock() }
    guard activeTIDs.remove(tid) != nil else { return }
    abortedTIDs.insert(tid)
    updateVersions(for: tid, to: .aborted)
    purgeAbortedVersions(tid: tid)
}
```

**Detailed Analysis:**

#### Process
1. **Lock Acquisition**: Acquire exclusive lock
2. **TID Removal**: Remove from active set
3. **TID Registration**: Add to aborted set
4. **Version Update**: Update all versions created by transaction
5. **Version Purging**: Remove aborted versions
6. **Lock Release**: Release lock automatically

#### Cleanup
- **Version Update**: Mark versions as aborted
- **Version Purging**: Remove aborted versions
- **Memory Reclamation**: Free memory used by aborted versions

#### Performance
- **Lock Acquisition**: O(1) operation
- **Set Operations**: O(1) for remove and insert
- **Version Update**: O(n) where n is number of versions
- **Version Purging**: O(n) where n is number of versions
- **Total Time**: O(n) where n is number of versions

### Version Management

#### Register Insert

```swift
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
```

**Detailed Analysis:**

#### Process
1. **Lock Acquisition**: Acquire exclusive lock
2. **Map Access**: Get or create table version map
3. **Chain Access**: Get or create version chain for RID
4. **TID Resolution**: Use provided TID or default to 0
5. **Status Determination**: Set status based on TID presence
6. **Version Creation**: Create new version with metadata
7. **Idempotency Check**: Check for duplicate insert
8. **Chain Update**: Add or update version in chain
9. **Map Update**: Update table version map
10. **TID Registration**: Register TID if committed

#### Idempotency
- **Duplicate Check**: Check if insert is duplicate
- **WAL Replay**: Safe for WAL recovery
- **Condition Check**: Multiple conditions for duplicate
- **Version Replacement**: Replace duplicate version

#### Performance
- **Lock Acquisition**: O(1) operation
- **Map Access**: O(1) average case
- **Chain Access**: O(1) average case
- **Version Creation**: O(1) operation
- **Chain Update**: O(1) for append
- **Total Time**: O(1) average case

#### Register Delete

```swift
func registerDelete(table: String, rid: RID, row: Row, tid: UInt64?) {
    lock.lock(); defer { lock.unlock() }
    var map = tableVersions[table] ?? [:]
    var chain = map[rid] ?? []
    let endTid = tid ?? 0
    let endStatus: Status = (tid == nil) ? .committed : .inProgress
    
    if let last = chain.last,
       last.endTID == nil {
        // Update existing version
        last.endTID = endTid
        last.endStatus = endStatus
    } else {
        // Create new version for delete
        let deleteVersion = Version(row: row,
                                   beginTID: endTid,
                                   beginStatus: endStatus,
                                   endTID: endTid,
                                   endStatus: endStatus,
                                   createdAt: Date())
        chain.append(deleteVersion)
    }
    
    map[rid] = chain
    tableVersions[table] = map
    if endStatus == .committed { committedTIDs.insert(endTid) }
}
```

**Detailed Analysis:**

#### Process
1. **Lock Acquisition**: Acquire exclusive lock
2. **Map Access**: Get or create table version map
3. **Chain Access**: Get or create version chain for RID
4. **TID Resolution**: Use provided TID or default to 0
5. **Status Determination**: Set status based on TID presence
6. **Version Update**: Update existing version or create new
7. **Map Update**: Update table version map
8. **TID Registration**: Register TID if committed

#### Delete Strategies
- **Update Existing**: Update last version if not ended
- **Create New**: Create new version if chain is empty
- **Tombstone**: Create tombstone version for delete

#### Performance
- **Lock Acquisition**: O(1) operation
- **Map Access**: O(1) average case
- **Chain Access**: O(1) average case
- **Version Update**: O(1) operation
- **Total Time**: O(1) average case

### Visibility and Snapshot Management

#### Create Snapshot

```swift
func createSnapshot(tid: UInt64?) -> Snapshot {
    lock.lock(); defer { lock.unlock() }
    let cutoffTID = committedTIDs.max() ?? 0
    return Snapshot(tid: tid,
                   activeTIDs: activeTIDs,
                   committedTIDs: committedTIDs,
                   cutoffTID: cutoffTID)
}
```

**Detailed Analysis:**

#### Process
1. **Lock Acquisition**: Acquire exclusive lock
2. **Cutoff Calculation**: Find maximum committed TID
3. **Snapshot Creation**: Create snapshot with current state
4. **Lock Release**: Release lock automatically

#### Cutoff TID
- **Purpose**: Determines visibility cutoff
- **Calculation**: Maximum committed transaction ID
- **Usage**: Transactions with TID > cutoff are invisible
- **Performance**: O(n) where n is number of committed transactions

#### Snapshot Contents
- **TID**: Transaction taking snapshot
- **Active TIDs**: Currently active transactions
- **Committed TIDs**: Successfully committed transactions
- **Cutoff TID**: Visibility cutoff

#### Performance
- **Lock Acquisition**: O(1) operation
- **Cutoff Calculation**: O(n) where n is committed transactions
- **Snapshot Creation**: O(1) operation
- **Total Time**: O(n) where n is committed transactions

#### Check Visibility

```swift
func isVisible(version: Version, snapshot: Snapshot) -> Bool {
    // Version is visible if:
    // 1. It was created by a committed transaction
    // 2. It was created before the snapshot cutoff
    // 3. It was not deleted by a committed transaction
    
    let beginCommitted = snapshot.committedTIDs.contains(version.beginTID)
    let beginBeforeCutoff = version.beginTID <= snapshot.cutoffTID
    let notDeleted = version.endTID == nil || 
                    !snapshot.committedTIDs.contains(version.endTID ?? 0)
    
    return beginCommitted && beginBeforeCutoff && notDeleted
}
```

**Detailed Analysis:**

#### Visibility Rules
1. **Begin Committed**: Version must be created by committed transaction
2. **Begin Before Cutoff**: Version must be created before snapshot cutoff
3. **Not Deleted**: Version must not be deleted by committed transaction

#### Logic
- **`beginCommitted`**: Check if creating transaction is committed
- **`beginBeforeCutoff`**: Check if version is before cutoff
- **`notDeleted`**: Check if version is not deleted
- **Combination**: All conditions must be true

#### Performance
- **Set Lookup**: O(1) average case for committed TIDs
- **Comparison**: O(1) for TID comparison
- **Total Time**: O(1) operation

### Garbage Collection

#### Purge Aborted Versions

```swift
private func purgeAbortedVersions(tid: UInt64) {
    for (table, ridMap) in tableVersions {
        for (rid, versions) in ridMap {
            let filteredVersions = versions.filter { version in
                !(version.beginTID == tid && version.beginStatus == .aborted) &&
                !(version.endTID == tid && version.endStatus == .aborted)
            }
            if filteredVersions.count != versions.count {
                tableVersions[table]?[rid] = filteredVersions
            }
        }
    }
}
```

**Detailed Analysis:**

#### Process
1. **Table Iteration**: Iterate through all tables
2. **RID Iteration**: Iterate through all RIDs in table
3. **Version Filtering**: Filter out aborted versions
4. **Map Update**: Update map if versions were removed

#### Filtering Logic
- **Begin Aborted**: Remove versions created by aborted transaction
- **End Aborted**: Remove versions ended by aborted transaction
- **Keep Others**: Keep all other versions

#### Performance
- **Table Iteration**: O(t) where t is number of tables
- **RID Iteration**: O(r) where r is number of RIDs
- **Version Filtering**: O(v) where v is number of versions
- **Total Time**: O(t * r * v) where t, r, v are table, RID, version counts

#### Purge Obsolete Versions

```swift
func purgeObsoleteVersions() {
    lock.lock(); defer { lock.unlock() }
    let snapshot = createSnapshot(tid: nil)
    
    for (table, ridMap) in tableVersions {
        for (rid, versions) in ridMap {
            let visibleVersions = versions.filter { version in
                isVisible(version: version, snapshot: snapshot)
            }
            if visibleVersions.count != versions.count {
                tableVersions[table]?[rid] = visibleVersions
            }
        }
    }
}
```

**Detailed Analysis:**

#### Process
1. **Lock Acquisition**: Acquire exclusive lock
2. **Snapshot Creation**: Create current snapshot
3. **Table Iteration**: Iterate through all tables
4. **RID Iteration**: Iterate through all RIDs in table
5. **Version Filtering**: Keep only visible versions
6. **Map Update**: Update map if versions were removed

#### Visibility Check
- **Snapshot**: Use current snapshot for visibility
- **Filtering**: Keep only visible versions
- **Cleanup**: Remove obsolete versions

#### Performance
- **Lock Acquisition**: O(1) operation
- **Snapshot Creation**: O(n) where n is committed transactions
- **Table Iteration**: O(t) where t is number of tables
- **RID Iteration**: O(r) where r is number of RIDs
- **Version Filtering**: O(v) where v is number of versions
- **Total Time**: O(n + t * r * v) where n, t, r, v are respective counts

## Lock Manager

### Class Structure

```swift
public final class LockManager {
    private var locks: [String: LockInfo] = [:]
    private let lock = NSLock()
    private let defaultTimeout: TimeInterval
    
    struct LockInfo {
        var type: LockType
        var holders: Set<UInt64>
        var waiters: [UInt64]
        var grantedAt: Date
    }
    
    enum LockType {
        case shared
        case exclusive
    }
}
```

**Detailed Analysis:**

#### Core Data Structures

##### `LockInfo` Struct
```swift
struct LockInfo {
    var type: LockType
    var holders: Set<UInt64>
    var waiters: [UInt64]
    var grantedAt: Date
}
```

**Field Analysis:**
- **`type: LockType`**: Type of lock (shared or exclusive)
- **`holders: Set<UInt64>`**: Set of transaction IDs holding the lock
- **`waiters: [UInt64]`**: Queue of transaction IDs waiting for the lock
- **`grantedAt: Date`**: Timestamp when lock was granted

##### `LockType` Enum
```swift
enum LockType {
    case shared
    case exclusive
}
```

**Analysis:**
- **`shared`**: Multiple transactions can hold simultaneously
- **`exclusive`**: Only one transaction can hold
- **Compatibility**: Shared locks are compatible with each other
- **Exclusivity**: Exclusive locks are incompatible with all others

#### Lock Acquisition

```swift
func acquireLock(resource: String, tid: UInt64, type: LockType) -> Bool {
    lock.lock(); defer { lock.unlock() }
    
    if let lockInfo = locks[resource] {
        // Check if lock can be granted
        if canGrantLock(lockInfo: lockInfo, tid: tid, type: type) {
            grantLock(resource: resource, tid: tid, type: type)
            return true
        } else {
            // Add to wait queue
            addToWaitQueue(resource: resource, tid: tid)
            return false
        }
    } else {
        // Create new lock
        createLock(resource: resource, tid: tid, type: type)
        return true
    }
}
```

**Detailed Analysis:**

#### Process
1. **Lock Acquisition**: Acquire manager lock
2. **Resource Check**: Check if resource is locked
3. **Grant Check**: Check if lock can be granted
4. **Grant or Wait**: Grant lock or add to wait queue
5. **Lock Release**: Release manager lock

#### Lock Granting Logic
- **New Resource**: Create new lock if resource not locked
- **Compatible Lock**: Grant if lock is compatible
- **Incompatible Lock**: Add to wait queue if incompatible

#### Performance
- **Lock Acquisition**: O(1) operation
- **Resource Lookup**: O(1) average case
- **Grant Check**: O(1) operation
- **Total Time**: O(1) average case

#### Lock Release

```swift
func releaseLock(resource: String, tid: UInt64) {
    lock.lock(); defer { lock.unlock() }
    
    guard var lockInfo = locks[resource] else { return }
    
    // Remove holder
    lockInfo.holders.remove(tid)
    
    if lockInfo.holders.isEmpty {
        // No more holders, grant to waiters
        if let nextWaiter = lockInfo.waiters.first {
            lockInfo.waiters.removeFirst()
            lockInfo.holders.insert(nextWaiter)
            lockInfo.grantedAt = Date()
        } else {
            // No waiters, remove lock
            locks.removeValue(forKey: resource)
            return
        }
    }
    
    locks[resource] = lockInfo
}
```

**Detailed Analysis:**

#### Process
1. **Lock Acquisition**: Acquire manager lock
2. **Resource Check**: Check if resource is locked
3. **Holder Removal**: Remove transaction from holders
4. **Empty Check**: Check if no more holders
5. **Waiter Grant**: Grant lock to next waiter
6. **Lock Removal**: Remove lock if no waiters

#### Waiter Processing
- **FIFO Queue**: Process waiters in first-in-first-out order
- **Immediate Grant**: Grant lock immediately when available
- **Lock Removal**: Remove lock when no more waiters

#### Performance
- **Lock Acquisition**: O(1) operation
- **Resource Lookup**: O(1) average case
- **Holder Removal**: O(1) operation
- **Waiter Processing**: O(1) operation
- **Total Time**: O(1) average case

## Two-Phase Commit

### Class Structure

```swift
public final class TwoPhaseCommit {
    private var preparedTransactions: Set<UInt64> = []
    private var coordinatorTID: UInt64?
    private let lock = NSLock()
    
    func prepare(tid: UInt64) -> Bool {
        lock.lock(); defer { lock.unlock() }
        preparedTransactions.insert(tid)
        return true
    }
    
    func commit(tid: UInt64) -> Bool {
        lock.lock(); defer { lock.unlock() }
        guard preparedTransactions.contains(tid) else { return false }
        preparedTransactions.remove(tid)
        return true
    }
    
    func abort(tid: UInt64) -> Bool {
        lock.lock(); defer { lock.unlock() }
        preparedTransactions.remove(tid)
        return true
    }
}
```

**Detailed Analysis:**

#### Process
1. **Prepare Phase**: All participants prepare for commit
2. **Commit Phase**: All participants commit if all prepared
3. **Abort Phase**: All participants abort if any failed

#### State Management
- **`preparedTransactions`**: Set of prepared transaction IDs
- **`coordinatorTID`**: Coordinator transaction ID
- **`lock`**: Protects state modifications

#### Performance
- **Prepare**: O(1) operation
- **Commit**: O(1) operation
- **Abort**: O(1) operation
- **Total Time**: O(1) for each operation

## Performance Characteristics

### Time Complexity

| Operation | Time Complexity | Space Complexity |
|-----------|----------------|------------------|
| Begin Transaction | O(1) | O(1) |
| Commit Transaction | O(n) | O(1) |
| Rollback Transaction | O(n) | O(1) |
| Register Insert | O(1) | O(1) |
| Register Delete | O(1) | O(1) |
| Create Snapshot | O(n) | O(1) |
| Check Visibility | O(1) | O(1) |
| Purge Versions | O(t * r * v) | O(1) |

### Memory Usage

| Component | Memory | Purpose |
|-----------|--------|---------|
| Version Chains | O(v) | Store all versions |
| Transaction Sets | O(t) | Track transaction states |
| Lock Manager | O(l) | Manage resource locks |
| Two-Phase Commit | O(p) | Track prepared transactions |

### Concurrency

| Aspect | Performance | Notes |
|--------|-------------|-------|
| Read Concurrency | High | MVCC enables concurrent reads |
| Write Concurrency | Medium | Locking limits write concurrency |
| Lock Contention | Low | Fine-grained locking |
| Deadlock Prevention | High | Single lock prevents deadlocks |

## Design Decisions

### Why MVCC?

- **Concurrency**: Enables high read concurrency
- **Consistency**: Provides consistent snapshots
- **Performance**: Reduces lock contention
- **Complexity**: More complex than locking

### Why Version Chains?

- **Efficiency**: O(1) access to latest version
- **History**: Maintains complete history
- **Recovery**: Enables point-in-time recovery
- **Memory**: Uses more memory than single version

### Why Single Lock?

- **Simplicity**: Prevents deadlocks
- **Performance**: Good for moderate concurrency
- **Debugging**: Easier to debug
- **Scalability**: May limit high concurrency

## Future Optimizations

### Lock-Free Operations

- **Atomic Operations**: Use atomic operations for simple state
- **Lock-Free Data Structures**: Implement lock-free version chains
- **Performance**: Better concurrency
- **Complexity**: More complex implementation

### Parallel Garbage Collection

- **Background Threads**: Use background threads for GC
- **Incremental GC**: Perform GC incrementally
- **Performance**: Reduce GC pause times
- **Memory**: Better memory utilization

### Optimistic Concurrency

- **Version Checking**: Check versions before commit
- **Conflict Detection**: Detect conflicts early
- **Performance**: Better for low-conflict workloads
- **Complexity**: More complex conflict resolution

---

*This analysis provides a comprehensive understanding of ColibrìDB's transaction system and MVCC implementation. For specific implementation details, see the corresponding source files.*
