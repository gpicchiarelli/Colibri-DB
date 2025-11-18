# RFC 0019: Transaction Manager

**Status**: Standards Track  
**Author**: ColibrìDB Team  
**Date**: 2025-11-18  
**TLA+ Spec**: `spec/TransactionManager.tla`

## Abstract

This RFC defines the Transaction Manager component, responsible for managing transaction lifecycle, ensuring ACID properties, and coordinating with MVCC, Lock Manager, and WAL for transaction processing.

## 1. Introduction

The Transaction Manager is the central coordinator for all transaction operations, ensuring atomicity, consistency, isolation, and durability (ACID). It integrates with MVCC for concurrency control, Lock Manager for deadlock prevention, and WAL for durability.

### 1.1 Purpose and Goals

The primary goals of the Transaction Manager are:

1. **ACID Guarantees**: Ensure all transactions maintain ACID properties
2. **Lifecycle Management**: Coordinate transaction begin, commit, and abort
3. **Concurrency Control**: Integrate with MVCC and Lock Manager for isolation
4. **Durability**: Coordinate with WAL to ensure committed transactions survive crashes
5. **Distributed Transactions**: Support two-phase commit for distributed scenarios

### 1.2 Problem Statement

Database systems must handle concurrent transactions correctly while ensuring:

- **Atomicity**: Transactions are all-or-nothing (commit or abort)
- **Consistency**: Database invariants maintained
- **Isolation**: Transactions don't interfere with each other
- **Durability**: Committed transactions survive crashes

The Transaction Manager solves these challenges by:

- Coordinating transaction lifecycle (begin, commit, abort)
- Tracking transaction state and operations
- Integrating with MVCC for snapshot isolation
- Using WAL for durability guarantees
- Supporting two-phase commit for distributed transactions

### 1.3 Key Concepts

**Transaction**: Unit of work that must be atomic:
- **Active**: Transaction in progress
- **Preparing**: Two-phase commit prepare phase
- **Committed**: Transaction completed successfully
- **Aborted**: Transaction rolled back

**ACID Properties**:
- **Atomicity**: All-or-nothing execution
- **Consistency**: Database invariants maintained
- **Isolation**: Transactions isolated from each other
- **Durability**: Committed changes survive crashes

**Two-Phase Commit (2PC)**:
- **Phase 1 (Prepare)**: All participants prepare
- **Phase 2 (Commit/Abort)**: All participants commit or abort

**Transaction Isolation Levels**:
- **Read Uncommitted**: No isolation (not implemented)
- **Read Committed**: Read only committed data (MVCC default)
- **Repeatable Read**: Snapshot isolation (MVCC)
- **Serializable**: Full serialization (MVCC + locking)

### 1.4 Relationship to Other Components

```
Transaction Manager
├── Uses: WAL Manager (durability)
├── Uses: MVCC Manager (isolation)
├── Uses: Lock Manager (deadlock prevention)
├── Coordinates: Transaction lifecycle
└── Tracks: Transaction state and operations
```

**Transaction Manager → WAL Manager**:
- Writes commit/abort records to WAL
- Ensures WAL flush before transaction commit completes
- Guarantees durability

**Transaction Manager → MVCC Manager**:
- Gets transaction snapshot (MVCC version)
- Tracks transaction read/write sets
- Ensures isolation

**Transaction Manager → Lock Manager**:
- Acquires locks for write operations
- Prevents deadlocks through timeout
- Ensures serializability (if used)

## 2. Design Principles

### 2.1 ACID Properties

1. **Atomicity**: Transactions are all-or-nothing
2. **Consistency**: Transactions maintain database invariants
3. **Isolation**: Transactions don't interfere with each other
4. **Durability**: Committed transactions survive crashes

### 2.2 Transaction Lifecycle

```
Active → Preparing → Committed/Aborted
   ↓
   └─→ Aborted (explicit or timeout)
```

### 2.3 Two-Phase Commit

For distributed transactions:
1. **Prepare Phase**: All participants prepare
2. **Commit Phase**: All participants commit or abort

## 3. Architecture

### 3.1 Component Overview

```
TransactionManager (Swift Actor)
├── transactions: [TxID -> Transaction]
├── txOperations: [TxID -> [Operation]]
├── txLocks: [TxID -> Set<String>]
├── txStartTime: [TxID -> Timestamp]
├── preparedTransactions: Set<TxID>
├── coordinatorState: CoordinatorState
├── participantVotes: [TxID -> [String -> Bool]]
├── walManager: WALManagerProtocol
├── mvccManager: MVCCManagerProtocol
└── lockManager: LockManager?
```

### 3.2 Dependencies

- **WALManager**: Write-ahead logging for durability
- **MVCCManager**: Multi-version concurrency control
- **LockManager**: Deadlock prevention

## 4. State Variables (TLA+ Mapping)

| Swift Variable | TLA+ Variable | Type | Description |
|----------------|---------------|------|-------------|
| `transactions` | `transactions` | `[TxID -> Transaction]` | Active transactions |
| `txOperations` | `txOperations` | `[TxID -> Seq(Operation)]` | Operations per transaction |
| `txLocks` | `txLocks` | `[TxID -> Set(String)]` | Locks per transaction |
| `txStartTime` | `txStartTime` | `[TxID -> Timestamp]` | Transaction start time |
| `preparedTransactions` | `preparedTransactions` | `Set(TxID)` | Prepared transactions |

## 5. API Specification

### 5.1 Initialization

```swift
public actor TransactionManager {
    public init(
        walManager: WALManagerProtocol,
        mvccManager: MVCCManagerProtocol,
        lockManager: LockManager?
    )
}
```

**Parameters**:
- `walManager`: WAL manager for durability
- `mvccManager`: MVCC manager for concurrency
- `lockManager`: Optional lock manager for deadlock prevention

### 5.2 Transaction Operations

#### 5.2.1 Begin Transaction

```swift
public func beginTransaction() async throws -> TxID
```

**TLA+ Action**: `BeginTransaction()`

**Behavior**: Detailed step-by-step execution

1. **Generate Transaction ID**:
   ```swift
   let txId = nextTID
   nextTID += 1
   ```
   - **Unique ID**: Monotonically increasing sequence
   - **Atomic**: Single actor ensures no race conditions
   - **Range**: UInt64 (supports ~1.8*10^19 transactions)

2. **Get Transaction Snapshot (MVCC)**:
   ```swift
   let snapshot = try await mvccManager.beginTransaction(txId: txId)
   ```
   - **Snapshot**: Read-consistent view of database
   - **Isolation**: Transaction sees consistent snapshot
   - **Version**: MVCC version for this transaction

3. **Create Transaction Object**:
   ```swift
   let transaction = Transaction(
       txId: txId,
       state: .active,
       startTime: UInt64(Date().timeIntervalSince1970 * 1000),
       endTime: nil,
       resources: [],
       participants: [],
       isDirty: false
   )
   ```
   - **State**: Initialized to `Active`
   - **Timestamp**: Wall-clock start time
   - **Resources**: Empty (will be populated during transaction)
   - **Participants**: Empty (for distributed transactions)

4. **Initialize Transaction State**:
   ```swift
   transactions[txId] = transaction
   txStartTime[txId] = transaction.startTime
   txOperations[txId] = []
   txLocks[txId] = []
   ```
   - **Transaction Map**: Track active transactions
   - **Operation List**: Initialize empty (will track operations)
   - **Lock Set**: Initialize empty (will track acquired locks)

5. **Write Begin Record to WAL** (optional):
   ```swift
   // Optional: Write begin record to WAL for debugging
   // Most systems don't write begin records (implicit)
   ```

**Preconditions**:
- System not crashed (enforced by caller)
- MVCC Manager available (required for snapshot)

**Postconditions**:
- Transaction created (`transactions[txId] != nil`)
- Transaction state is `Active` (`transactions[txId].state == .active`)
- Transaction snapshot obtained (MVCC version assigned)
- `txStartTime[txId]` recorded
- `txOperations[txId]` initialized (empty list)
- `txLocks[txId]` initialized (empty set)

**Returns**: Transaction ID (`TxID`)

**Performance Characteristics**:
- **Begin**: ~100ns (in-memory operations)
- **With MVCC**: +10-50ns (snapshot creation)
- **Scalable**: O(1) operation

**Example Usage**:
```swift
// Begin transaction
let txId = try await transactionManager.beginTransaction()

// Perform operations
try await db.insert(table: "users", row: row, txID: txId)
try await db.update(table: "users", row: row, txID: txId)

// Commit transaction
try await transactionManager.commitTransaction(txId: txId)
```

**Edge Cases**:

1. **Transaction ID Overflow**: UInt64 overflow
   - **Likelihood**: Extremely unlikely
   - **Solution**: Wrap around (acceptable for most use cases)

2. **Concurrent Begins**:
   - **Behavior**: Actor isolation serializes operations
   - **Safety**: No race conditions, IDs assigned sequentially
   - **Performance**: May serialize unnecessarily (acceptable)

3. **MVCC Manager Unavailable**:
   - **Behavior**: Error propagates to caller
   - **Recovery**: Cannot begin transaction without MVCC

**Errors**:
- `TransactionError.mvccError`: MVCC Manager error (propagated from MVCC Manager)

**Transaction State Transitions**:

```
┌──────────┐
│   None   │
└────┬─────┘
     │ beginTransaction()
     ▼
┌──────────┐
│  Active  │
└────┬─────┘
     │
     ├── commitTransaction() ───► ┌──────────┐
     │                             │ Committed│
     │                             └──────────┘
     │
     ├── abortTransaction() ──────► ┌──────────┐
     │                               │  Aborted │
     │                               └──────────┘
     │
     └── timeout ──────────────────► ┌──────────┐
                                     │  Aborted │
                                     └──────────┘
```

**MVCC Snapshot Details**:

The transaction snapshot obtained from MVCC Manager provides:

1. **Read Version**: Version number for reading
   - Transaction reads data at this version
   - Sees committed transactions at this version
   - Ignores uncommitted transactions

2. **Write Version**: Version number for writing
   - Transaction writes create new versions
   - Versions are visible only after commit
   - Enables isolation without locking (optimistic)

3. **Isolation**: Snapshot isolation
   - Read-only transactions never conflict
   - Write transactions conflict only on same pages
   - Serializable through MVCC conflict detection

#### 5.2.2 Commit Transaction

```swift
public func commitTransaction(txId: TxID) async throws
```

**TLA+ Action**: `CommitTransaction(txId)`

**Behavior**: Detailed step-by-step execution

1. **Validate Transaction**:
   ```swift
   guard var transaction = transactions[txId] else {
       throw TransactionError.transactionNotFound(txId: txId)
   }
   ```
   - Transaction must exist
   - Transaction must be active

2. **Check Transaction State**:
   ```swift
   guard transaction.state == .active else {
       throw TransactionError.transactionNotActive(txId: txId)
   }
   ```
   - Only active transactions can commit
   - Already committed/aborted transactions cannot commit

3. **Prepare Transaction** (two-phase commit):
   ```swift
   try await prepareTransaction(txId: txId)
   ```
   - **Prepare Phase**: Ensures transaction can commit
   - **Validation**: Checks constraints, conflicts
   - **State**: Transaction state becomes `Prepared`

4. **Commit with MVCC**:
   ```swift
   try await mvccManager.commit(txId: txId)
   ```
   - **MVCC Commit**: Makes transaction versions visible
   - **Conflict Detection**: Checks for write-write conflicts
   - **Version Assignment**: Assigns commit version

5. **Write Commit Record to WAL**:
   ```swift
   let commitLSN = try await walManager.append(
       kind: .commit,
       txID: txId,
       pageID: 0,  // No page for commit record
       payload: Data()
   )
   ```
   - **Durability**: Commit record in WAL ensures durability
   - **Recovery**: Recovery can identify committed transactions
   - **LSN**: Commit LSN recorded

6. **Flush WAL**:
   ```swift
   try await walManager.flush()
   ```
   - **Durability**: Ensures commit record is durable
   - **Critical**: Transaction not committed until WAL flushed
   - **Performance**: May use group commit for efficiency

7. **Update Transaction State**:
   ```swift
   transaction.state = .committed
   transaction.endTime = UInt64(Date().timeIntervalSince1970 * 1000)
   transactions[txId] = transaction
   ```
   - **State**: Transaction state becomes `Committed`
   - **Timestamp**: End time recorded
   - **Completion**: Transaction complete

8. **Release All Locks**:
   ```swift
   if let lockManager = lockManager {
       for lock in txLocks[txId] ?? [] {
           try await lockManager.releaseLock(lock: lock, txId: txId)
       }
   }
   txLocks[txId] = []
   ```
   - **Lock Release**: All locks acquired by transaction released
   - **Deadlock Prevention**: Prevents deadlocks
   - **Concurrency**: Enables other transactions to proceed

9. **Update Metrics**:
   ```swift
   // Update transaction metrics
   // (e.g., committed transactions count, average duration)
   ```

**Preconditions**:
- Transaction exists (`transactions[txId] != nil`)
- Transaction state is `Active` (`transactions[txId].state == .active`)
- MVCC Manager available (required for commit)

**Postconditions**:
- Transaction committed (`transactions[txId].state == .committed`)
- Commit record in WAL (durable)
- WAL flushed (commit record durable)
- Locks released (`txLocks[txId] == []`)
- Transaction end time recorded
- MVCC versions visible (committed transaction visible to others)

**Performance Characteristics**:
- **Commit**: ~1-5ms (WAL flush dominates)
  - Validation: ~100ns
  - MVCC commit: ~100ns
  - WAL append: ~100ns
  - WAL flush: ~1-5ms (with fsync)
- **Without Group Commit**: ~2-5ms per transaction
- **With Group Commit**: ~0.2-0.5ms per transaction (amortized)

**Commit Flow Diagram**:

```
┌──────────────────┐
│commitTransaction │
│      (txId)      │
└──────┬───────────┘
       │
       ▼
   ┌──────────────┐
   │Validate      │
   │Transaction   │
   └───┬──────────┘
       │
       ▼
   ┌──────────────┐
   │Prepare       │
   │Transaction   │
   └───┬──────────┘
       │
       ▼
   ┌──────────────┐
   │MVCC Commit   │
   └───┬──────────┘
       │
       ▼
   ┌──────────────┐
   │Write Commit  │
   │to WAL        │
   └───┬──────────┘
       │
       ▼
   ┌──────────────┐
   │Flush WAL     │
   └───┬──────────┘
       │
       ▼
   ┌──────────────┐
   │Update State  │
   │to Committed  │
   └───┬──────────┘
       │
       ▼
   ┌──────────────┐
   │Release Locks │
   └───┬──────────┘
       │
       ▼
   ┌──────────────┐
   │Complete      │
   └──────────────┘
```

**Edge Cases**:

1. **Transaction Not Found**:
   - **Behavior**: Throws `TransactionError.transactionNotFound`
   - **Recovery**: Transaction may have already committed/aborted or never existed

2. **Transaction Not Active**:
   - **Behavior**: Throws `TransactionError.transactionNotActive`
   - **Prevention**: Check transaction state before commit

3. **Prepare Failure**:
   - **Behavior**: Transaction aborted, error propagated
   - **Recovery**: Transaction rolled back automatically

4. **MVCC Conflict**:
   - **Behavior**: MVCC commit throws conflict error
   - **Recovery**: Transaction aborted, can retry

5. **WAL Flush Failure**:
   - **Behavior**: WAL flush throws error
   - **State**: Transaction may be committed in memory but not durable
   - **Recovery**: Retry flush or handle disk issues

6. **Concurrent Commit**:
   - **Behavior**: Actor isolation serializes operations
   - **Safety**: Only one commit at a time per transaction

**Errors**:
- `TransactionError.transactionNotFound`: Transaction doesn't exist
- `TransactionError.transactionNotActive`: Transaction not in active state
- `TransactionError.commitFailed`: Commit failed (prepare failure, MVCC conflict, WAL error, etc.)

**Durability Guarantee**:

The commit operation ensures durability through:

1. **WAL Commit Record**: Written before transaction state updated
2. **WAL Flush**: Ensures commit record is durable
3. **State Update**: Transaction state updated only after WAL flush
4. **Recovery**: ARIES recovery can identify committed transactions from WAL

**Example Usage**:
```swift
// Begin transaction
let txId = try await transactionManager.beginTransaction()

// Perform operations
try await db.insert(table: "users", row: row, txID: txId)
try await db.update(table: "users", row: row, txID: txId)

// Commit transaction (ensures durability)
try await transactionManager.commitTransaction(txId: txId)

// Transaction is now committed and durable
```

**Best Practices**:

1. **Always Check Return Value**: Handle commit errors
   ```swift
   do {
       try await transactionManager.commitTransaction(txId: txId)
       // Transaction committed successfully
   } catch TransactionError.commitFailed {
       // Commit failed, transaction aborted
   }
   ```

2. **Monitor Transaction Duration**: Check for long-running transactions
   ```swift
   let duration = Date().timeIntervalSince(startTime)
   if duration > 30.0 {  // 30 seconds
       // Long-running transaction, may timeout
   }
   ```

3. **Use Group Commit**: Enable group commit for better throughput
   - Reduces per-transaction commit latency
   - Improves overall throughput

#### 5.2.3 Abort Transaction

```swift
public func abortTransaction(txId: TxID) async throws
```

**TLA+ Action**: `AbortTransaction(txId)`

**Behavior**: Detailed step-by-step execution

1. **Validate Transaction**:
   ```swift
   guard var transaction = transactions[txId] else {
       throw TransactionError.transactionNotFound(txId: txId)
   }
   ```
   - Transaction must exist
   - Can abort active or prepared transactions

2. **Check Transaction State**:
   ```swift
   guard transaction.state == .active || transaction.state == .prepared else {
       throw TransactionError.transactionNotActive(txId: txId)
   }
   ```
   - Can abort active or prepared transactions
   - Cannot abort already committed/aborted transactions

3. **Abort with MVCC**:
   ```swift
   try await mvccManager.abort(txId: txId)
   ```
   - **MVCC Abort**: Removes transaction versions
   - **Rollback**: Undoes transaction changes
   - **Isolation**: Transaction no longer visible

4. **Undo All Operations**:
   ```swift
   // Get operations in reverse order (undo in reverse)
   let operations = txOperations[txId] ?? []
   for operation in operations.reversed() {
       try await undoOperation(operation: operation)
   }
   ```
   - **Reverse Order**: Undo operations in reverse order
   - **WAL Undo**: Uses WAL undo records if available
   - **Data Rollback**: Restores data to previous state

5. **Write Abort Record to WAL**:
   ```swift
   let abortLSN = try await walManager.append(
       kind: .abort,
       txID: txId,
       pageID: 0,  // No page for abort record
       payload: Data()
   )
   ```
   - **Durability**: Abort record in WAL for recovery
   - **Recovery**: Recovery can identify aborted transactions
   - **Consistency**: Ensures transaction not replayed

6. **Flush WAL** (optional):
   ```swift
   // Optional: Flush abort record (typically not required)
   // try await walManager.flush()
   ```
   - **Durability**: Abort record typically doesn't need immediate flush
   - **Performance**: Can use group commit for efficiency

7. **Update Transaction State**:
   ```swift
   transaction.state = .aborted
   transaction.endTime = UInt64(Date().timeIntervalSince1970 * 1000)
   transactions[txId] = transaction
   ```
   - **State**: Transaction state becomes `Aborted`
   - **Timestamp**: End time recorded
   - **Completion**: Transaction complete (aborted)

8. **Release All Locks**:
   ```swift
   if let lockManager = lockManager {
       for lock in txLocks[txId] ?? [] {
           try await lockManager.releaseLock(lock: lock, txId: txId)
       }
   }
   txLocks[txId] = []
   ```
   - **Lock Release**: All locks acquired by transaction released
   - **Deadlock Prevention**: Prevents deadlocks
   - **Concurrency**: Enables other transactions to proceed

9. **Clean Up Transaction State**:
   ```swift
   txOperations[txId] = []
   txWALRecords[txId] = []
   txWriteSets[txId] = []
   txReadSets[txId] = []
   ```
   - **Cleanup**: Remove operation tracking
   - **Memory**: Free memory used by transaction

**Preconditions**:
- Transaction exists (`transactions[txId] != nil`)
- Transaction state is `Active` or `Prepared` (can abort)

**Postconditions**:
- Transaction aborted (`transactions[txId].state == .aborted`)
- All operations undone (data restored to previous state)
- Abort record in WAL (for recovery)
- Locks released (`txLocks[txId] == []`)
- Transaction end time recorded
- MVCC versions removed (transaction no longer visible)

**Performance Characteristics**:
- **Abort**: ~1-5ms (WAL flush dominates, if enabled)
  - Validation: ~100ns
  - MVCC abort: ~100ns
  - Undo operations: ~1-10ms (depends on number of operations)
  - WAL append: ~100ns
  - Lock release: ~100ns per lock

**Abort Flow Diagram**:

```
┌──────────────────┐
│abortTransaction │
│      (txId)      │
└──────┬───────────┘
       │
       ▼
   ┌──────────────┐
   │Validate      │
   │Transaction   │
   └───┬──────────┘
       │
       ▼
   ┌──────────────┐
   │MVCC Abort    │
   └───┬──────────┘
       │
       ▼
   ┌──────────────┐
   │Undo          │
   │Operations    │
   │(reverse)     │
   └───┬──────────┘
       │
       ▼
   ┌──────────────┐
   │Write Abort   │
   │to WAL        │
   └───┬──────────┘
       │
       ▼
   ┌──────────────┐
   │Update State  │
   │to Aborted    │
   └───┬──────────┘
       │
       ▼
   ┌──────────────┐
   │Release Locks │
   └───┬──────────┘
       │
       ▼
   ┌──────────────┐
   │Clean Up      │
   └──────────────┘
```

**Undo Operations**:

Operations are undone in reverse order:

```swift
// Operation 1: INSERT row1
// Operation 2: UPDATE row2
// Operation 3: DELETE row3

// Undo order:
// 1. Undo DELETE row3 (re-insert row3)
// 2. Undo UPDATE row2 (restore old value)
// 3. Undo INSERT row1 (delete row1)
```

**Edge Cases**:

1. **Transaction Not Found**:
   - **Behavior**: Throws `TransactionError.transactionNotFound`
   - **Recovery**: Transaction may have already aborted or never existed

2. **Transaction Already Committed**:
   - **Behavior**: Throws `TransactionError.transactionNotActive`
   - **Prevention**: Cannot abort committed transactions

3. **MVCC Abort Failure**:
   - **Behavior**: Error propagates to caller
   - **State**: Transaction may be in inconsistent state
   - **Recovery**: May need manual intervention

4. **Undo Operation Failure**:
   - **Behavior**: Error propagates to caller
   - **State**: Some operations may not be undone
   - **Recovery**: Retry abort or handle manually

5. **Concurrent Abort**:
   - **Behavior**: Actor isolation serializes operations
   - **Safety**: Only one abort at a time per transaction

**Errors**:
- `TransactionError.transactionNotFound`: Transaction doesn't exist
- `TransactionError.transactionNotActive`: Transaction not in active/prepared state
- `TransactionError.abortFailed`: Abort failed (undo failure, MVCC error, etc.)

**Automatic Abort Scenarios**:

1. **Timeout**: Transaction exceeds timeout
   ```swift
   // Check timeout
   if Date().timeIntervalSince(startTime) > TX_TIMEOUT_MS {
       try await abortTransaction(txId: txId)
   }
   ```

2. **Deadlock**: Transaction is deadlock victim
   ```swift
   // Lock Manager detects deadlock
   if deadlockVictim == txId {
       try await abortTransaction(txId: txId)
   }
   ```

3. **Constraint Violation**: Transaction violates constraints
   ```swift
   // Constraint check fails
   if !checkConstraints(txId: txId) {
       try await abortTransaction(txId: txId)
   }
   ```

4. **MVCC Conflict**: Transaction has write-write conflict
   ```swift
   // MVCC detects conflict
   if mvccConflict(txId: txId) {
       try await abortTransaction(txId: txId)
   }
   ```

**Example Usage**:
```swift
// Begin transaction
let txId = try await transactionManager.beginTransaction()

// Perform operations
do {
    try await db.insert(table: "users", row: row, txID: txId)
    try await transactionManager.commitTransaction(txId: txId)
} catch {
    // Error occurred, abort transaction
    try await transactionManager.abortTransaction(txId: txId)
}
```

**Best Practices**:

1. **Always Abort on Error**: Use defer or catch to ensure abort
   ```swift
   let txId = try await transactionManager.beginTransaction()
   defer {
       if transactionManager.getTransactionState(txId) == .active {
           try? await transactionManager.abortTransaction(txId: txId)
       }
   }
   
   // Perform operations
   try await db.insert(...)
   try await transactionManager.commitTransaction(txId: txId)
   ```

2. **Monitor Transaction Duration**: Abort long-running transactions
   ```swift
   let startTime = Date()
   // ... perform operations ...
   if Date().timeIntervalSince(startTime) > 30.0 {
       try await transactionManager.abortTransaction(txId: txId)
   }
   ```

#### 5.2.4 Get Transaction State

```swift
public func getTransactionState(txId: TxID) -> TransactionState?
```

**Returns**: Transaction state or `nil` if not found

### 5.3 Two-Phase Commit

#### 5.3.1 Prepare Transaction

```swift
public func prepareTransaction(txId: TxID) async throws
```

**TLA+ Action**: `PrepareTransaction(txId)`

**Behavior**:
1. Check if transaction exists and is active
2. Request votes from all participants
3. Wait for all votes (or timeout)
4. If all votes are YES:
   - Add to `preparedTransactions`
   - Update state to `Prepared`
5. Otherwise:
   - Abort transaction

**Preconditions**:
- Transaction exists
- Transaction state is `Active`

**Postconditions**:
- Transaction prepared or aborted
- All participants voted

#### 5.3.2 Commit Prepared Transaction

```swift
public func commitPreparedTransaction(txId: TxID) async throws
```

**TLA+ Action**: `CommitPreparedTransaction(txId)`

**Behavior**:
1. Check if transaction is prepared
2. Notify all participants to commit
3. Wait for all participants to acknowledge
4. Update state to `Committed`
5. Release locks

**Preconditions**:
- Transaction exists
- Transaction state is `Prepared`

**Postconditions**:
- Transaction committed
- All participants committed
- Locks released

### 5.4 Operation Tracking

#### 5.4.1 Add Operation

```swift
public func addOperation(txId: TxID, operation: Operation) async throws
```

**TLA+ Action**: `AddOperation(txId, operation)`

**Behavior**:
1. Check if transaction exists and is active
2. Add operation to `txOperations[txId]`
3. Record operation in WAL

**Preconditions**:
- Transaction exists
- Transaction state is `Active`

**Postconditions**:
- Operation added
- Operation recorded in WAL

## 6. ACID Properties

### 6.1 Atomicity

**Implementation**:
- All-or-nothing: commit or abort
- WAL records ensure all-or-nothing durability
- Rollback undoes all operations

### 6.2 Consistency

**Implementation**:
- Transaction validates constraints before commit
- Database invariants checked
- Constraint violations cause abort

### 6.3 Isolation

**Implementation**:
- MVCC provides isolation levels
- Lock Manager prevents conflicts
- Serializable isolation through locking

### 6.4 Durability

**Implementation**:
- WAL ensures durability
- Commit record written before commit completes
- WAL flushed before commit acknowledgment

## 7. Invariants (TLA+ Verification)

### 7.1 Transaction State Invariant

```tla
Inv_TransactionState ==
    \A txId \in DOMAIN transactions:
        transactions[txId].state \in {Active, Committed, Aborted, Prepared}
```

**Swift Implementation**:
```swift
public func checkTransactionStateInvariant() -> Bool {
    for (txId, transaction) in transactions {
        guard [.active, .committed, .aborted, .prepared].contains(transaction.state) else {
            return false
        }
    }
    return true
}
```

### 7.2 Prepared Transaction Invariant

```tla
Inv_PreparedTransaction ==
    \A txId \in preparedTransactions:
        txId \in DOMAIN transactions /\
        transactions[txId].state = Prepared
```

### 7.3 Operation Consistency Invariant

```tla
Inv_OperationConsistency ==
    \A txId \in DOMAIN txOperations:
        txId \in DOMAIN transactions /\
        \A op \in txOperations[txId]:
            op.txId = txId
```

## 8. Error Handling

### 8.1 Error Types

```swift
public enum TransactionError: Error {
    case transactionNotFound(txId: TxID)
    case transactionNotActive(txId: TxID)
    case transactionAlreadyCommitted(txId: TxID)
    case transactionAlreadyAborted(txId: TxID)
    case prepareFailed(txId: TxID)
    case commitFailed(txId: TxID)
    case timeout(txId: TxID)
}
```

### 8.2 Error Recovery

- **Transaction Not Found**: Return error
- **Transaction Not Active**: Cannot perform operation
- **Timeout**: Abort transaction automatically

## 9. Timeout Handling

### 9.1 Transaction Timeout

Default: 30 seconds

**Behavior**:
1. Check transaction age
2. If exceeds timeout, abort transaction
3. Log timeout event

### 9.2 Prepare Timeout

Default: 5 seconds

**Behavior**:
1. Wait for participant votes
2. If timeout expires, abort transaction

## 10. Apple-First Optimizations

### 10.1 Swift Actor Performance

- Zero-cost message passing
- Compile-time safety
- Efficient isolation

### 10.2 Async/Await

- Non-blocking operations
- Structured concurrency
- Efficient task scheduling

### 10.3 Memory Management

- ARC for automatic cleanup
- Value types where possible
- Efficient transaction state storage

## 11. Testing

### 11.1 Unit Tests

- Transaction lifecycle
- Commit/abort operations
- Two-phase commit
- Timeout handling
- Invariant verification

### 11.2 Integration Tests

- Transaction + MVCC
- Transaction + Lock Manager
- Transaction + WAL
- Concurrent transactions
- Deadlock scenarios

### 11.3 Performance Tests

- Throughput measurements
- Latency measurements
- Concurrent transaction handling
- Two-phase commit performance

## 12. References

- **RFC 0020**: MVCC Manager
- **RFC 0021**: Lock Manager
- **RFC 0005**: Write-Ahead Logging
- **RFC 0023**: Two-Phase Commit
- **TLA+ Spec**: `spec/TransactionManager.tla`
- **Gray, 1978**: "Notes on Database Operating Systems"

---

**Next**: See RFC 0020 for MVCC Manager details.

