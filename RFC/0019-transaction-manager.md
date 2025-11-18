# RFC 0019: Transaction Manager

**Status**: Standards Track  
**Author**: ColibrìDB Team  
**Date**: 2025-11-18  
**TLA+ Spec**: `spec/TransactionManager.tla`

## Abstract

This RFC defines the Transaction Manager component, responsible for managing transaction lifecycle, ensuring ACID properties, and coordinating with MVCC, Lock Manager, and WAL for transaction processing.

## 1. Introduction

The Transaction Manager is the central coordinator for all transaction operations, ensuring atomicity, consistency, isolation, and durability (ACID). It integrates with MVCC for concurrency control, Lock Manager for deadlock prevention, and WAL for durability.

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

**Behavior**:
1. Generate new transaction ID: `txId = nextTID; nextTID++`
2. Create transaction with state `Active`
3. Record start time
4. Initialize operation list
5. Return transaction ID

**Postconditions**:
- Transaction created
- Transaction state is `Active`
- `txStartTime` recorded

**Returns**: Transaction ID (`TxID`)

#### 5.2.2 Commit Transaction

```swift
public func commitTransaction(txId: TxID) async throws
```

**TLA+ Action**: `CommitTransaction(txId)`

**Behavior**:
1. Check if transaction exists and is active
2. Write commit record to WAL
3. Flush WAL (ensure durability)
4. Update transaction state to `Committed`
5. Release all locks
6. Record end time

**Preconditions**:
- Transaction exists
- Transaction state is `Active`

**Postconditions**:
- Transaction committed
- WAL flushed
- Locks released
- Transaction state is `Committed`

#### 5.2.3 Abort Transaction

```swift
public func abortTransaction(txId: TxID) async throws
```

**TLA+ Action**: `AbortTransaction(txId)`

**Behavior**:
1. Check if transaction exists
2. Undo all operations (using WAL undo records)
3. Write abort record to WAL
4. Update transaction state to `Aborted`
5. Release all locks
6. Record end time

**Preconditions**:
- Transaction exists

**Postconditions**:
- Transaction aborted
- All operations undone
- Locks released
- Transaction state is `Aborted`

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

