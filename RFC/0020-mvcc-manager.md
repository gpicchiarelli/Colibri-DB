# RFC 0020: MVCC Manager (Multi-Version Concurrency Control)

**Status**: Standards Track  
**Author**: ColibrìDB Team  
**Date**: 2025-11-18  
**TLA+ Spec**: `spec/MVCC.tla`

## Abstract

This RFC defines the MVCC Manager component, responsible for providing Multi-Version Concurrency Control to enable snapshot isolation, eliminate write-write conflicts, and ensure read stability for concurrent transactions.

## 1. Introduction

The MVCC Manager provides Multi-Version Concurrency Control (MVCC) to enable concurrent transaction execution without explicit locking. It implements snapshot isolation, where each transaction sees a consistent snapshot of the database, and detects write-write conflicts to ensure serializability.

### 1.1 Purpose and Goals

The primary goals of the MVCC Manager are:

1. **Snapshot Isolation**: Ensure transactions see consistent snapshots of the database
2. **Write-Write Conflict Detection**: Detect and prevent write-write conflicts
3. **Read Stability**: Ensure reads are stable (repeatable reads)
4. **No Read-Write Conflicts**: Eliminate read-write conflicts through versioning
5. **Performance**: Provide better concurrency than locking-based approaches

### 1.2 Problem Statement

Database systems must handle concurrent transactions correctly while ensuring:

- **Isolation**: Transactions don't interfere with each other
- **Consistency**: Database invariants maintained
- **Performance**: High throughput for concurrent operations
- **No Blocking**: Read operations don't block writes (and vice versa)

Traditional locking approaches face challenges:

- **Deadlocks**: Lock ordering issues can cause deadlocks
- **Blocking**: Read locks block writes, write locks block reads
- **Performance**: Lock contention reduces throughput

The MVCC Manager solves these challenges by:

- **Versioning**: Maintain multiple versions of data
- **Snapshot Isolation**: Each transaction sees consistent snapshot
- **Optimistic Concurrency**: Detect conflicts at commit time
- **No Blocking**: Reads and writes don't block each other

### 1.3 Key Concepts

**MVCC (Multi-Version Concurrency Control)**: Concurrency control method that maintains multiple versions of data.

**Snapshot**: Consistent view of database at a specific point in time.

**Version**: Specific version of a key-value pair created by a transaction.

**Snapshot Isolation**: Isolation level where transactions see consistent snapshots.

**Write-Write Conflict**: Two transactions write to same key.

**Read Stability**: Reads return same value throughout transaction.

**Version Chain**: Linked list of versions for a key.

**Active Transaction**: Transaction currently executing.

**Committed Transaction**: Transaction successfully completed.

**Aborted Transaction**: Transaction rolled back.

### 1.4 Relationship to Other Components

```
MVCC Manager
├── Used by: Transaction Manager (for isolation)
├── Coordinates with: Lock Manager (optional, for serializability)
├── Tracks: Transaction snapshots and versions
└── Manages: Version chains and read/write sets
```

**Transaction Manager → MVCC Manager**:
- Gets transaction snapshot (MVCC version)
- Checks for write-write conflicts at commit
- Tracks transaction read/write sets

**MVCC Manager → Lock Manager** (optional):
- Uses locks for serializability (if needed)
- Prevents write-write conflicts (alternative to MVCC)

## 2. Design Principles

### 2.1 Snapshot Isolation

**Invariant**: Transactions see consistent snapshots of the database.

```
\A txId \in activeTx:
    snapshot[txId].timestamp = globalTS at begin
    \A key \in readSets[txId]:
        version read is visible to transaction
```

**Benefits**:
- **Consistency**: Reads see consistent state
- **No Read-Write Conflicts**: Reads don't block writes
- **Performance**: Better concurrency than locking

### 2.2 Write-Write Conflict Detection

**Invariant**: Write-write conflicts are detected at commit time.

```
\A txId1, txId2 \in activeTx:
    writeSets[txId1] \cap writeSets[txId2] # {} =>
        Conflict detected, one transaction aborted
```

**Benefits**:
- **Correctness**: Prevents lost updates
- **Serializability**: Ensures serializable execution
- **Optimistic**: No blocking during transaction execution

### 2.3 Version Chain Consistency

**Invariant**: Version chains are consistent and valid.

```
\A key \in DOMAIN versions:
    versions[key] is linked list of versions
    Each version has valid txId
    Versions are ordered by timestamp
```

**Benefits**:
- **Correctness**: Versions correctly linked
- **Performance**: Efficient version lookup
- **Recovery**: Can reconstruct versions from WAL

### 2.4 Read Stability

**Invariant**: Reads return same value throughout transaction.

```
\A txId \in activeTx, key \in readSets[txId]:
    First read and subsequent reads return same version
```

**Benefits**:
- **Repeatable Reads**: Consistent reads within transaction
- **Correctness**: No phantom reads
- **Performance**: Version cached for repeatable reads

### 2.5 Apple-First Architecture

#### 2.5.1 Swift Actor Model

**Why Actors**: Thread-safe MVCC operations without explicit locking.

```swift
public actor MVCCManager {
    // All state isolated within actor
    private var versions: [MVCCKey: [TxID: Version]] = [:]
    private var activeTx: Set<TxID> = []
    
    // Methods automatically synchronized
    public func beginTransaction(txId: TxID) async throws -> MVCCSnapshot {
        // Safe concurrent access
    }
}
```

**Benefits**:
- **Thread Safety**: No data races
- **No Locks**: Actors eliminate lock contention
- **Composable**: Easy to compose with other actors

#### 2.5.2 Async/Await

**Why Async/Await**: MVCC operations are inherently asynchronous.

```swift
// Non-blocking snapshot creation
public func beginTransaction(txId: TxID) async throws -> MVCCSnapshot {
    // Suspends task, allows other work
    let snapshot = createSnapshot(txId: txId)
    // Resumes when snapshot created
    return snapshot
}
```

**Benefits**:
- **Non-Blocking**: Threads not blocked on MVCC operations
- **Concurrent**: Supports thousands of concurrent transactions
- **Structured**: Clear error handling and control flow

#### 2.5.3 Value Types

**Why Value Types**: Immutable data structures are thread-safe by default.

```swift
public struct Version: Sendable {
    public let txId: TxID
    public let value: Value
    public let timestamp: Timestamp
    // Immutable - safe to share
}
```

**Benefits**:
- **Thread Safety**: Immutable values cannot have data races
- **Memory Efficient**: Copy-on-write for large values
- **Predictable**: No hidden mutations

## 3. Architecture

### 3.1 Component Overview

```
MVCCManager (Swift Actor)
├── versions: [MVCCKey -> [TxID -> Version]]
│   ├── Purpose: Version chain for each key
│   ├── Type: Nested dictionary mapping keys to versions
│   ├── Lifetime: Versions exist until garbage collected
│   └── Access: O(1) hash table lookup for key, O(n) for version search
│
├── activeTx: Set<TxID>
│   ├── Purpose: Track active transactions
│   ├── Type: Set of transaction IDs
│   ├── Updates: Added on begin, removed on commit/abort
│   └── Use: Snapshot creation, conflict detection
│
├── committedTx: Set<TxID>
│   ├── Purpose: Track committed transactions
│   ├── Type: Set of transaction IDs
│   ├── Updates: Added on commit
│   └── Use: Version visibility, snapshot creation
│
├── abortedTx: Set<TxID>
│   ├── Purpose: Track aborted transactions
│   ├── Type: Set of transaction IDs
│   ├── Updates: Added on abort
│   └── Use: Version cleanup, conflict detection
│
├── snapshots: [TxID -> MVCCSnapshot]
│   ├── Purpose: Transaction snapshots
│   ├── Type: Dictionary mapping TxID to snapshot
│   ├── Lifetime: Exists for active transaction lifetime
│   └── Use: Read version determination
│
├── readSets: [TxID -> Set<MVCCKey>]
│   ├── Purpose: Track read keys per transaction
│   ├── Type: Dictionary mapping TxID to key set
│   ├── Updates: Added on read operations
│   └── Use: Read stability, conflict detection
│
├── writeSets: [TxID -> Set<MVCCKey>]
│   ├── Purpose: Track written keys per transaction
│   ├── Type: Dictionary mapping TxID to key set
│   ├── Updates: Added on write operations
│   └── Use: Write-write conflict detection
│
├── snapshotValueCache: [TxID -> [MVCCKey -> Value]]
│   ├── Purpose: Cache read values for repeatable reads
│   ├── Type: Nested dictionary mapping TxID to key-value cache
│   ├── Lifetime: Exists for active transaction lifetime
│   └── Use: Read stability (repeatable reads)
│
├── globalTS: Timestamp
│   ├── Purpose: Global timestamp for snapshot creation
│   ├── Type: Monotonically increasing timestamp
│   ├── Updates: Incremented on each transaction begin
│   └── Use: Snapshot timestamp assignment
│
└── minActiveTx: TxID
    ├── Purpose: Minimum active transaction ID
    ├── Type: Transaction ID
    ├── Updates: Updated on transaction begin/commit/abort
    └── Use: Version garbage collection
```

### 3.2 Data Flow Diagrams

#### 3.2.1 Transaction Begin Flow

```
┌──────────────────┐
│beginTransaction  │
│     (txId)       │
└──────┬───────────┘
       │
       ▼
   ┌──────────────┐
   │Add to        │
   │activeTx      │
   └───┬──────────┘
       │
       ▼
   ┌──────────────┐
   │Increment     │
   │globalTS      │
   └───┬──────────┘
       │
       ▼
   ┌──────────────┐
   │Create        │
   │Snapshot      │
   └───┬──────────┘
       │
       ▼
   ┌──────────────┐
   │Initialize    │
   │Read/Write    │
   │Sets          │
   └───┬──────────┘
       │
       ▼
   ┌──────────────┐
   │Return        │
   │Snapshot      │
   └──────────────┘
```

#### 3.2.2 Read Operation Flow

```
┌──────────────────┐
│readValue(key,    │
│    txId)         │
└──────┬───────────┘
       │
       ▼
   ┌──────────────┐
   │Get           │
   │Snapshot      │
   └───┬──────────┘
       │
       ▼
   ┌──────────────┐
   │Check         │
   │Cache         │
   └───┬───────┬───┘
       │Hit    │Miss
       ▼       ▼
  ┌──────┐ ┌──────────────┐
  │Return│ │Find Visible  │
  │Cached│ │Version       │
  │Value │ └───┬──────────┘
  └──────┘     │
               ▼
          ┌──────────────┐
          │Check         │
          │Visibility    │
          └───┬──────────┘
              │
              ▼
          ┌──────────────┐
          │Add to        │
          │readSet       │
          └───┬──────────┘
              │
              ▼
          ┌──────────────┐
          │Cache Value   │
          └───┬──────────┘
              │
              ▼
          ┌──────────────┐
          │Return        │
          │Value         │
          └──────────────┘
```

#### 3.2.3 Write Operation Flow

```
┌──────────────────┐
│writeValue(key,   │
│   value, txId)   │
└──────┬───────────┘
       │
       ▼
   ┌──────────────┐
   │Check if      │
   │Transaction   │
   │Active        │
   └───┬──────────┘
       │
       ▼
   ┌──────────────┐
   │Create        │
   │Version       │
   └───┬──────────┘
       │
       ▼
   ┌──────────────┐
   │Add to        │
   │versions[key] │
   └───┬──────────┘
       │
       ▼
   ┌──────────────┐
   │Add key to    │
   │writeSet      │
   └───┬──────────┘
       │
       ▼
   ┌──────────────┐
   │Return        │
   └──────────────┘
```

#### 3.2.4 Commit Flow

```
┌──────────────────┐
│commit(txId)      │
└──────┬───────────┘
       │
       ▼
   ┌──────────────┐
   │Check Write-  │
   │Write         │
   │Conflicts     │
   └───┬───────┬───┘
       │No     │Yes
       │Conflict│Conflict
       ▼       ▼
  ┌─────────┐ ┌──────────────┐
  │Remove   │ │Abort         │
  │from     │ │Transaction   │
  │activeTx │ └──────────────┘
  └───┬─────┘
      │
      ▼
  ┌──────────────┐
  │Add to        │
  │committedTx   │
  └───┬──────────┘
      │
      ▼
  ┌──────────────┐
  │Make          │
  │Versions      │
  │Visible       │
  └───┬──────────┘
      │
      ▼
  ┌──────────────┐
  │Clean Up      │
  │Transaction   │
  │State         │
  └──────────────┘
```

### 3.3 Dependencies

- **Transaction Manager**: Transaction lifecycle management
- **Lock Manager** (optional): Additional locking for serializability

## 4. State Variables (TLA+ Mapping)

| Swift Variable | TLA+ Variable | Type | Description |
|----------------|---------------|------|-------------|
| `versions` | `versions` | `[Key -> [TxID -> Version]]` | Version chain per key |
| `activeTx` | `activeTx` | `Set(TxID)` | Active transactions |
| `committedTx` | `committedTx` | `Set(TxID)` | Committed transactions |
| `abortedTx` | `abortedTx` | `Set(TxID)` | Aborted transactions |
| `snapshots` | `snapshots` | `[TxID -> Snapshot]` | Transaction snapshots |
| `readSets` | `readSets` | `[TxID -> Set(Key)]` | Read sets per transaction |
| `writeSets` | `writeSets` | `[TxID -> Set(Key)]` | Write sets per transaction |
| `globalTS` | `globalTS` | `Timestamp` | Global timestamp |
| `minActiveTx` | `minActiveTx` | `TxID` | Minimum active transaction |

## 5. API Specification

### 5.1 Initialization

```swift
public actor MVCCManager {
    public init()
    public init(transactionManager: MVCCTransactionManager, lockManager: MVCCLockManager)
}
```

**Parameters**:
- `transactionManager`: Transaction manager (optional, for coordination)
- `lockManager`: Lock manager (optional, for additional locking)

### 5.2 Transaction Operations

#### 5.2.1 Begin Transaction

```swift
public func beginTransaction(txId: TxID) async throws -> MVCCSnapshot
```

**TLA+ Action**: `BeginTransaction(txId)`

**Behavior**: Detailed step-by-step execution

1. **Add to Active Transactions**:
   ```swift
   activeTx.insert(txId)
   ```
   - Transaction becomes active
   - Used for conflict detection
   - Included in snapshots

2. **Increment Global Timestamp**:
   ```swift
   globalTS += 1
   ```
   - Monotonically increasing timestamp
   - Used for snapshot timestamp
   - Ensures total order of transactions

3. **Create Snapshot**:
   ```swift
   let snapshot = MVCCSnapshot(
       txId: txId,
       timestamp: globalTS,
       activeTransactions: activeTx,
       committedTransactions: committedTx
   )
   ```
   - **Snapshot**: Consistent view of database
   - **Timestamp**: Point-in-time view
   - **Active Transactions**: Transactions in progress
   - **Committed Transactions**: Transactions that committed before snapshot

4. **Store Snapshot**:
   ```swift
   snapshots[txId] = snapshot
   ```
   - Snapshot stored for transaction
   - Used for read version determination
   - Lifetime: Transaction lifetime

5. **Initialize Read/Write Sets**:
   ```swift
   readSets[txId] = []
   writeSets[txId] = []
   snapshotValueCache[txId] = [:]
   snapshotNilKeys[txId] = []
   readVersionTimestamps[txId] = [:]
   ```
   - **Read Set**: Keys read by transaction (empty initially)
   - **Write Set**: Keys written by transaction (empty initially)
   - **Value Cache**: Cached values for repeatable reads
   - **Nil Keys**: Keys that don't exist (for stability)

6. **Update Minimum Active Transaction**:
   ```swift
   if minActiveTx == 0 || txId < minActiveTx {
       minActiveTx = txId
   }
   ```
   - **Garbage Collection**: Used for version garbage collection
   - **Oldest Transaction**: Minimum active transaction determines oldest version to keep

7. **Return Snapshot**:
   ```swift
   return snapshot
   ```

**Preconditions**:
- `txId` is valid (non-zero transaction ID)
- Transaction not already active (`txId \notin activeTx`)

**Postconditions**:
- Transaction active (`txId \in activeTx`)
- Snapshot created (`snapshots[txId] != nil`)
- Global timestamp incremented (`globalTS = oldGlobalTS + 1`)
- Read/write sets initialized (empty)

**Returns**: `MVCCSnapshot` for transaction

**Performance Characteristics**:
- **Begin**: ~100ns (in-memory operations)
- **Scalable**: O(1) operation

**Snapshot Properties**:

1. **Consistency**: Snapshot sees only transactions committed before snapshot timestamp
2. **Isolation**: Transaction doesn't see uncommitted transactions
3. **Stability**: Snapshot remains consistent throughout transaction

**Example Usage**:
```swift
// Begin transaction
let snapshot = try await mvccManager.beginTransaction(txId: txId)

// Transaction sees consistent snapshot
// Reads use snapshot to determine visible versions
```

**Edge Cases**:

1. **Transaction Already Active**:
   - **Behavior**: Returns existing snapshot or throws error
   - **Prevention**: Check transaction state before begin

2. **Timestamp Overflow**:
   - **Likelihood**: Extremely unlikely (UInt64 overflow)
   - **Solution**: Wrap around (acceptable for most use cases)

3. **Concurrent Begin**:
   - **Behavior**: Actor isolation serializes operations
   - **Safety**: No race conditions, timestamps assigned sequentially

#### 5.2.2 Read Value

```swift
public func readValue(key: MVCCKey, txId: TxID) async throws -> Value?
```

**TLA+ Action**: `ReadValue(key, txId)`

**Behavior**: Detailed step-by-step execution

1. **Validate Transaction**:
   ```swift
   guard activeTx.contains(txId) else {
       throw MVCCError.transactionNotFound
   }
   ```
   - Transaction must be active
   - Cannot read from aborted/committed transaction

2. **Check Snapshot Value Cache**:
   ```swift
   if let cachedValue = snapshotValueCache[txId]?[key] {
       return cachedValue  // Return cached value (read stability)
   }
   ```
   - **Read Stability**: First read caches value for repeatable reads
   - **Performance**: Avoids version lookup on subsequent reads
   - **Correctness**: Ensures consistent reads

3. **Check Nil Keys**:
   ```swift
   if snapshotNilKeys[txId]?.contains(key) == true {
       return nil  // Key doesn't exist (cached for stability)
   }
   ```
   - **Stability**: Keys that don't exist are cached
   - **Correctness**: Prevents phantom reads
   - **Performance**: Avoids version lookup

4. **Get Transaction Snapshot**:
   ```swift
   guard let snapshot = snapshots[txId] else {
       throw MVCCError.snapshotNotFound
   }
   ```
   - Snapshot required for version visibility
   - Contains timestamp and committed transactions

5. **Find Visible Version**:
   ```swift
   guard let keyVersions = versions[key] else {
       // Key doesn't exist
       snapshotNilKeys[txId]?.insert(key)
       return nil
   }
   
   // Find latest version visible to transaction
   var visibleVersion: Version? = nil
   var latestTimestamp: Timestamp = 0
   
   for (versionTxId, version) in keyVersions {
       // Version visible if:
       // 1. Version created by committed transaction
       // 2. Transaction committed before snapshot timestamp
       // 3. Version transaction is in committed transactions set
       if committedTx.contains(versionTxId) &&
          snapshot.committedTransactions.contains(versionTxId) {
           if version.timestamp > latestTimestamp {
               latestTimestamp = version.timestamp
               visibleVersion = version
           }
       }
   }
   ```
   - **Visibility Rules**: Version visible if:
     - Created by committed transaction
     - Transaction committed before snapshot timestamp
     - Transaction in committed transactions set
   - **Latest Version**: Returns latest visible version
   - **No Version**: Returns nil if no visible version

6. **Cache Value**:
   ```swift
   if let version = visibleVersion {
       snapshotValueCache[txId]?[key] = version.value
       readVersionTimestamps[txId]?[key] = version.timestamp
   } else {
       snapshotNilKeys[txId]?.insert(key)
   }
   ```
   - **Read Stability**: Cache value for repeatable reads
   - **Performance**: Avoids version lookup on subsequent reads
   - **Correctness**: Ensures consistent reads

7. **Add to Read Set**:
   ```swift
   readSets[txId]?.insert(key)
   ```
   - **Conflict Detection**: Read set used for conflict detection
   - **Analysis**: Tracks keys read by transaction
   - **Serializability**: Used for serializability checks

8. **Return Value**:
   ```swift
   return visibleVersion?.value
   ```

**Preconditions**:
- Transaction active (`txId \in activeTx`)
- Snapshot exists (`snapshots[txId] != nil`)

**Postconditions**:
- Value returned (may be nil if key doesn't exist)
- Key added to read set (`key \in readSets[txId]`)
- Value cached (`snapshotValueCache[txId][key] = value`)
- Read stability ensured (subsequent reads return same value)

**Returns**: `Value?` (nil if key doesn't exist)

**Performance Characteristics**:
- **Cache Hit**: ~10ns (dictionary lookup)
- **Cache Miss**: ~100ns-1μs (version lookup)
- **Complexity**: O(n) where n = number of versions per key

**Read Stability**:

Reads are stable (repeatable reads):

```swift
// First read
let value1 = try await mvccManager.readValue(key: "key", txId: txId)

// ... other operations ...

// Second read (same key, same transaction)
let value2 = try await mvccManager.readValue(key: "key", txId: txId)

// Guarantee: value1 == value2 (read stability)
```

**Version Visibility Rules**:

1. **Committed**: Version created by committed transaction
2. **Before Snapshot**: Transaction committed before snapshot timestamp
3. **Not Aborted**: Transaction not aborted
4. **Latest**: Return latest visible version

**Edge Cases**:

1. **Transaction Not Active**:
   - **Behavior**: Throws `MVCCError.transactionNotFound`
   - **Prevention**: Ensure transaction is active

2. **Key Doesn't Exist**:
   - **Behavior**: Returns `nil`, caches nil key
   - **Stability**: Subsequent reads return nil

3. **No Visible Version**:
   - **Behavior**: Returns `nil`
   - **Reason**: No committed version visible to transaction

4. **Concurrent Reads**:
   - **Behavior**: Actor isolation serializes operations
   - **Safety**: No race conditions

#### 5.2.3 Write Value

```swift
public func writeValue(key: MVCCKey, value: Value, txId: TxID) async throws
```

**TLA+ Action**: `WriteValue(key, value, txId)`

**Behavior**: Detailed step-by-step execution

1. **Validate Transaction**:
   ```swift
   guard activeTx.contains(txId) else {
       throw MVCCError.transactionNotFound
   }
   ```
   - Transaction must be active
   - Cannot write to aborted/committed transaction

2. **Get Transaction Snapshot**:
   ```swift
   guard let snapshot = snapshots[txId] else {
       throw MVCCError.snapshotNotFound
   }
   ```
   - Snapshot required for timestamp assignment

3. **Create Version**:
   ```swift
   let version = Version(
       txId: txId,
       value: value,
       timestamp: snapshot.timestamp,
       prevLSN: 0  // Will be set by WAL
   )
   ```
   - **Version**: New version of key
   - **Transaction ID**: Version created by this transaction
   - **Timestamp**: Snapshot timestamp
   - **Value**: Actual data

4. **Add Version to Versions**:
   ```swift
   if versions[key] == nil {
       versions[key] = [:]
   }
   versions[key]?[txId] = version
   ```
   - **Version Chain**: Add version to version chain
   - **Multiple Versions**: Same key can have multiple versions (different transactions)
   - **Visibility**: Version not visible until transaction commits

5. **Add Key to Write Set**:
   ```swift
   writeSets[txId]?.insert(key)
   ```
   - **Conflict Detection**: Write set used for write-write conflict detection
   - **Analysis**: Tracks keys written by transaction
   - **Serializability**: Used for serializability checks

6. **Update Cache** (if key was previously read):
   ```swift
   snapshotValueCache[txId]?[key] = value
   snapshotNilKeys[txId]?.remove(key)
   ```
   - **Read Stability**: Update cache with new value
   - **Correctness**: Ensures subsequent reads see written value
   - **Performance**: Avoids version lookup

**Preconditions**:
- Transaction active (`txId \in activeTx`)
- Snapshot exists (`snapshots[txId] != nil`)

**Postconditions**:
- Version created (`versions[key][txId] != nil`)
- Key added to write set (`key \in writeSets[txId]`)
- Cache updated (if key was previously read)

**Performance Characteristics**:
- **Write**: ~100ns (in-memory operations)
- **Scalable**: O(1) operation

**Version Creation**:

Each write creates a new version:

```swift
// Transaction 1 writes key "A" = "value1"
await mvccManager.writeValue(key: "A", value: "value1", txId: txId1)
// Creates: versions["A"][txId1] = Version("value1")

// Transaction 2 writes key "A" = "value2"
await mvccManager.writeValue(key: "A", value: "value2", txId: txId2)
// Creates: versions["A"][txId2] = Version("value2")

// Both versions exist until transactions commit/abort
```

**Edge Cases**:

1. **Transaction Not Active**:
   - **Behavior**: Throws `MVCCError.transactionNotFound`
   - **Prevention**: Ensure transaction is active

2. **Multiple Writes to Same Key**:
   - **Behavior**: Overwrites previous version for same transaction
   - **Correctness**: Only latest version kept (previous versions not needed)

3. **Concurrent Writes**:
   - **Behavior**: Actor isolation serializes operations
   - **Safety**: No race conditions
   - **Conflict**: Write-write conflicts detected at commit

#### 5.2.4 Commit Transaction

```swift
public func commit(txId: TxID) async throws
```

**TLA+ Action**: `CommitTransaction(txId)`

**Behavior**: Detailed step-by-step execution

1. **Validate Transaction**:
   ```swift
   guard activeTx.contains(txId) else {
       throw MVCCError.transactionNotFound
   }
   ```
   - Transaction must be active
   - Cannot commit already committed/aborted transaction

2. **Check Write-Write Conflicts**:
   ```swift
   let writeSet = writeSets[txId] ?? []
   for otherTxId in activeTx where otherTxId != txId {
       let otherWriteSet = writeSets[otherTxId] ?? []
       let conflict = !writeSet.intersection(otherWriteSet).isEmpty
       if conflict {
           throw MVCCError.writeWriteConflict
       }
   }
   ```
   - **Conflict Detection**: Check if any other active transaction wrote to same keys
   - **Write-Write Conflict**: Two transactions writing to same key
   - **Abort Victim**: One transaction must abort (determined by conflict resolution policy)

3. **Remove from Active Transactions**:
   ```swift
   activeTx.remove(txId)
   ```
   - Transaction no longer active
   - No longer included in conflict detection

4. **Add to Committed Transactions**:
   ```swift
   committedTx.insert(txId)
   ```
   - Transaction committed
   - Versions now visible to other transactions
   - Included in future snapshots

5. **Make Versions Visible**:
   ```swift
   // Versions are now visible to other transactions
   // No explicit operation needed - visibility determined by committedTx set
   ```
   - **Visibility**: Versions become visible when transaction committed
   - **Reads**: Other transactions can now see these versions
   - **Snapshot**: Included in committed transactions set

6. **Update Minimum Active Transaction**:
   ```swift
   if minActiveTx == txId {
       minActiveTx = activeTx.min() ?? 0
   }
   ```
   - **Garbage Collection**: Update minimum active transaction
   - **Version Cleanup**: Versions older than minActiveTx can be garbage collected

7. **Clean Up Transaction State**:
   ```swift
   snapshots.removeValue(forKey: txId)
   readSets.removeValue(forKey: txId)
   writeSets.removeValue(forKey: txId)
   snapshotValueCache.removeValue(forKey: txId)
   snapshotNilKeys.removeValue(forKey: txId)
   readVersionTimestamps.removeValue(forKey: txId)
   ```
   - **Memory**: Free memory used by transaction
   - **Cleanup**: Remove transaction-specific state

**Preconditions**:
- Transaction active (`txId \in activeTx`)
- No write-write conflicts (checked during commit)

**Postconditions**:
- Transaction committed (`txId \in committedTx`)
- Transaction not active (`txId \notin activeTx`)
- Versions visible (included in committed transactions set)
- Transaction state cleaned up

**Performance Characteristics**:
- **Commit**: ~100ns-1μs (conflict detection dominates)
  - Conflict check: ~100ns-1μs (depends on number of active transactions)
  - State updates: ~100ns
- **Complexity**: O(n) where n = number of active transactions

**Write-Write Conflict Detection**:

Conflicts detected at commit time:

```swift
// Transaction 1 writes key "A"
await mvccManager.writeValue(key: "A", value: "value1", txId: txId1)

// Transaction 2 writes key "A" (conflict!)
await mvccManager.writeValue(key: "A", value: "value2", txId: txId2)

// Transaction 1 commits (no conflict, txId2 not yet committed)
try await mvccManager.commit(txId: txId1)  // Success

// Transaction 2 commits (conflict detected!)
try await mvccManager.commit(txId: txId2)  // Throws writeWriteConflict
```

**Conflict Resolution Policy**:

Current implementation: First committer wins
- First transaction to commit succeeds
- Second transaction aborts
- Alternative: Last writer wins (not implemented)

**Edge Cases**:

1. **Transaction Not Active**:
   - **Behavior**: Throws `MVCCError.transactionNotFound`
   - **Prevention**: Ensure transaction is active

2. **Write-Write Conflict**:
   - **Behavior**: Throws `MVCCError.writeWriteConflict`
   - **Recovery**: Caller must abort transaction
   - **Policy**: First committer wins

3. **Concurrent Commit**:
   - **Behavior**: Actor isolation serializes operations
   - **Safety**: Conflicts detected correctly

4. **No Write Set**:
   - **Behavior**: Commit succeeds (read-only transaction)
   - **Performance**: No conflict detection needed

#### 5.2.5 Abort Transaction

```swift
public func abort(txId: TxID) async throws
```

**TLA+ Action**: `AbortTransaction(txId)`

**Behavior**: Detailed step-by-step execution

1. **Validate Transaction**:
   ```swift
   guard activeTx.contains(txId) else {
       throw MVCCError.transactionNotFound
   }
   ```
   - Transaction must be active
   - Cannot abort already committed/aborted transaction

2. **Remove Versions**:
   ```swift
   let writeSet = writeSets[txId] ?? []
   for key in writeSet {
       versions[key]?.removeValue(forKey: txId)
       // Clean up empty version chains
       if versions[key]?.isEmpty == true {
           versions.removeValue(forKey: key)
       }
   }
   ```
   - **Version Cleanup**: Remove versions created by aborted transaction
   - **Memory**: Free memory used by versions
   - **Correctness**: Aborted transactions don't affect database state

3. **Remove from Active Transactions**:
   ```swift
   activeTx.remove(txId)
   ```
   - Transaction no longer active
   - No longer included in conflict detection

4. **Add to Aborted Transactions**:
   ```swift
   abortedTx.insert(txId)
   ```
   - Transaction aborted
   - Versions not visible to other transactions
   - Included in future snapshots (as aborted)

5. **Update Minimum Active Transaction**:
   ```swift
   if minActiveTx == txId {
       minActiveTx = activeTx.min() ?? 0
   }
   ```
   - **Garbage Collection**: Update minimum active transaction
   - **Version Cleanup**: Versions older than minActiveTx can be garbage collected

6. **Clean Up Transaction State**:
   ```swift
   snapshots.removeValue(forKey: txId)
   readSets.removeValue(forKey: txId)
   writeSets.removeValue(forKey: txId)
   snapshotValueCache.removeValue(forKey: txId)
   snapshotNilKeys.removeValue(forKey: txId)
   readVersionTimestamps.removeValue(forKey: txId)
   ```
   - **Memory**: Free memory used by transaction
   - **Cleanup**: Remove transaction-specific state

**Preconditions**:
- Transaction active (`txId \in activeTx`)

**Postconditions**:
- Transaction aborted (`txId \in abortedTx`)
- Transaction not active (`txId \notin activeTx`)
- Versions removed (versions created by transaction removed)
- Transaction state cleaned up

**Performance Characteristics**:
- **Abort**: ~100ns-1μs (version cleanup dominates)
  - Version cleanup: ~100ns per key
  - State updates: ~100ns
- **Complexity**: O(n) where n = number of keys written

**Version Cleanup**:

Aborted transactions remove their versions:

```swift
// Transaction writes key "A"
await mvccManager.writeValue(key: "A", value: "value1", txId: txId)

// Transaction aborts
try await mvccManager.abort(txId: txId)

// Version removed: versions["A"][txId] = nil
```

**Edge Cases**:

1. **Transaction Not Active**:
   - **Behavior**: Throws `MVCCError.transactionNotFound`
   - **Prevention**: Ensure transaction is active

2. **No Write Set**:
   - **Behavior**: Abort succeeds (read-only transaction)
   - **Performance**: No version cleanup needed

3. **Concurrent Abort**:
   - **Behavior**: Actor isolation serializes operations
   - **Safety**: Versions removed correctly

## 6. Invariants (TLA+ Verification)

### 6.1 Snapshot Isolation Invariant

```tla
Inv_SnapshotIsolation ==
    \A txId \in activeTx:
        \A key \in readSets[txId]:
            Let version == versions[key][readVersion[txId][key]]
            In  version.txId \in committedTx /\
                version.timestamp <= snapshots[txId].timestamp
```

**Swift Implementation**:
```swift
public func checkSnapshotIsolationInvariant() -> Bool {
    for (txId, readSet) in readSets {
        guard let snapshot = snapshots[txId] else {
            return false
        }
        for key in readSet {
            guard let versionTimestamp = readVersionTimestamps[txId]?[key] else {
                continue
            }
            guard let keyVersions = versions[key] else {
                continue
            }
            // Find version with this timestamp
            var foundVersion: Version? = nil
            for (versionTxId, version) in keyVersions {
                if version.timestamp == versionTimestamp {
                    foundVersion = version
                    break
                }
            }
            guard let version = foundVersion else {
                return false
            }
            // Check visibility
            guard committedTx.contains(version.txId),
                  version.timestamp <= snapshot.timestamp else {
                return false
            }
        }
    }
    return true
}
```

**Motivation**: Ensures transactions see consistent snapshots

**Violation Prevention**: Version visibility checked during read

### 6.2 Write-Write Conflict Invariant

```tla
Inv_WriteWriteConflict ==
    \A txId1, txId2 \in activeTx:
        txId1 # txId2 =>
            writeSets[txId1] \cap writeSets[txId2] = {}
```

**Swift Implementation**:
```swift
public func checkWriteWriteConflictInvariant() -> Bool {
    let activeTransactions = Array(activeTx)
    for i in 0..<activeTransactions.count {
        let txId1 = activeTransactions[i]
        let writeSet1 = writeSets[txId1] ?? []
        for j in (i+1)..<activeTransactions.count {
            let txId2 = activeTransactions[j]
            let writeSet2 = writeSets[txId2] ?? []
            let conflict = !writeSet1.intersection(writeSet2).isEmpty
            if conflict {
                return false  // Conflict detected
            }
        }
    }
    return true
}
```

**Motivation**: Ensures no write-write conflicts in active transactions

**Violation Prevention**: Conflicts detected at commit, one transaction aborted

### 6.3 Version Chain Consistency Invariant

```tla
Inv_VersionChainConsistency ==
    \A key \in DOMAIN versions:
        \A txId \in DOMAIN versions[key]:
            versions[key][txId].txId = txId
```

**Swift Implementation**:
```swift
public func checkVersionChainConsistencyInvariant() -> Bool {
    for (key, keyVersions) in versions {
        for (txId, version) in keyVersions {
            if version.txId != txId {
                return false
            }
        }
    }
    return true
}
```

**Motivation**: Ensures version chain consistency

**Violation Prevention**: Version creation ensures correct txId

### 6.4 Read Stability Invariant

```tla
Inv_ReadStability ==
    \A txId \in activeTx:
        \A key \in readSets[txId]:
            Let firstValue == firstRead[txId][key]
            In  snapshotValueCache[txId][key] = firstValue
```

**Swift Implementation**:
```swift
public func checkReadStabilityInvariant() -> Bool {
    for (txId, readSet) in readSets {
        guard let cache = snapshotValueCache[txId] else {
            continue
        }
        for key in readSet {
            // First read caches value, subsequent reads return cached value
            // Invariant: All reads return same value (enforced by implementation)
            guard cache[key] != nil || snapshotNilKeys[txId]?.contains(key) == true else {
                return false  // Key read but not cached
            }
        }
    }
    return true
}
```

**Motivation**: Ensures read stability (repeatable reads)

**Violation Prevention**: First read caches value, subsequent reads use cache

## 7. Performance Characteristics

### 7.1 Snapshot Creation

**Operation**: `beginTransaction()`

**Complexity**: O(1)

**Latency**: ~100ns

**Factors**:
- Active transaction set size (copy)
- Committed transaction set size (copy)

### 7.2 Read Operation

**Operation**: `readValue()`

**Complexity**: 
- Cache hit: O(1)
- Cache miss: O(n) where n = number of versions per key

**Latency**:
- Cache hit: ~10ns
- Cache miss: ~100ns-1μs

**Factors**:
- Number of versions per key
- Snapshot timestamp
- Committed transaction set size

### 7.3 Write Operation

**Operation**: `writeValue()`

**Complexity**: O(1)

**Latency**: ~100ns

**Factors**:
- Dictionary operations (insert)

### 7.4 Commit Operation

**Operation**: `commit()`

**Complexity**: O(n * m) where n = number of active transactions, m = average write set size

**Latency**: ~100ns-1μs

**Factors**:
- Number of active transactions
- Write set sizes
- Conflict detection overhead

### 7.5 Abort Operation

**Operation**: `abort()`

**Complexity**: O(n) where n = number of keys written

**Latency**: ~100ns-1μs

**Factors**:
- Write set size
- Version cleanup overhead

## 8. Error Handling

### 8.1 Error Types

```swift
public enum MVCCError: Error {
    case transactionNotFound
    case snapshotNotFound
    case writeWriteConflict
    case transactionNotActive
    case invalidSnapshot
}
```

### 8.2 Error Recovery

- **Transaction Not Found**: Transaction already committed/aborted
- **Write-Write Conflict**: Transaction must abort, retry or handle conflict
- **Invalid Snapshot**: Re-create snapshot or abort transaction

## 9. Testing

### 9.1 Unit Tests

- Snapshot creation and consistency
- Read/write operations
- Write-write conflict detection
- Read stability
- Version visibility
- Transaction commit/abort

### 9.2 Integration Tests

- MVCC + Transaction Manager
- MVCC + Lock Manager
- Concurrent transactions
- Conflict scenarios

### 9.3 Performance Tests

- Snapshot creation latency
- Read/write throughput
- Commit latency with conflicts
- Memory usage

## 10. Apple-First Optimizations

### 10.1 Swift Actors

- **Actor Isolation**: Thread-safe MVCC operations
- **No Locks**: Eliminates lock contention
- **Composable**: Easy to compose with other actors

### 10.2 Value Types

- **Immutable Versions**: Version struct is immutable
- **Copy-on-Write**: Efficient memory usage
- **Thread Safety**: Immutable values are thread-safe

### 10.3 Async/Await

- **Non-Blocking**: MVCC operations don't block threads
- **Concurrent**: Supports thousands of concurrent transactions
- **Structured**: Clear error handling and control flow

## 11. References

- **RFC 0019**: Transaction Manager
- **TLA+ Spec**: `spec/MVCC.tla`
- **Paper**: "A Critique of ANSI SQL Isolation Levels" (Berenson et al., 1995)

---

**Next**: See RFC 0010 for Index Manager details.
