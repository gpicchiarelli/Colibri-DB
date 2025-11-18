# RFC 0005: Write-Ahead Logging (WAL)

**Status**: Standards Track  
**Author**: ColibrìDB Team  
**Date**: 2025-11-18  
**TLA+ Spec**: `spec/WAL.tla`

## Abstract

This RFC defines the Write-Ahead Logging (WAL) component, responsible for ensuring data durability and crash recovery through the Log-Before-Data property.

## 1. Introduction

The Write-Ahead Log is a critical component that ensures all changes to data pages are logged before being written to disk. This guarantees durability and enables crash recovery using the ARIES algorithm.

## 2. Design Principles

### 2.1 Log-Before-Data Property

**Invariant**: Data pages are written to disk only after the corresponding WAL records have been flushed.

```
\A pid \in ModifiablePages:
    pageLSN[pid] <= flushedLSN
```

This ensures that in case of a crash, all data changes can be recovered from the WAL.

### 2.2 Durability Guarantee

Committed transactions survive crashes:
- All committed changes are in the WAL
- WAL is flushed before transaction commit completes
- Data pages can be recovered from WAL after crash

### 2.3 Total Order Property

Log records maintain sequential order:
- Each record has a unique, monotonic LSN (Log Sequence Number)
- Records are flushed in LSN order
- Recovery processes records in LSN order

## 3. Architecture

### 3.1 Component Overview

```
FileWAL (Swift Actor)
├── wal: [ConcreteWALRecord]          # Flushed records
├── pendingRecords: [ConcreteWALRecord] # Pending flush
├── nextLSN: LSN                       # Next LSN to assign
├── flushedLSN: LSN                    # Highest flushed LSN
├── pageLSN: [PageID -> LSN]           # Last LSN per page
├── dirtyPageTable: [PageID -> LSN]    # DPT (Dirty Page Table)
└── fileHandle: FileHandle             # WAL file handle
```

### 3.2 Dependencies

- **File System**: APFS for efficient file operations
- **Buffer Manager**: Coordinates flushedLSN for WAL-before-data

## 4. State Variables (TLA+ Mapping)

| Swift Variable | TLA+ Variable | Type | Description |
|----------------|---------------|------|-------------|
| `wal` | `wal` | `Seq(WALRecord)` | Flushed WAL records |
| `pendingRecords` | `pendingRecords` | `Seq(WALRecord)` | Pending flush queue |
| `nextLSN` | `nextLSN` | `LSN` | Next LSN to assign |
| `flushedLSN` | `flushedLSN` | `LSN` | Highest flushed LSN |
| `pageLSN` | `pageLSN` | `[PageID -> LSN]` | Last LSN per page |
| `dirtyPageTable` | `dirtyPageTable` | `[PageID -> LSN]` | Dirty Page Table |
| `txLastLSN` | `txLastLSN` | `[TxID -> LSN]` | Last LSN per transaction |

## 5. API Specification

### 5.1 Initialization

```swift
public actor FileWAL {
    public init(
        walFilePath: URL,
        config: GroupCommitConfig = GroupCommitConfig(),
        fsyncOnFlush: Bool = true
    ) throws
}
```

**Parameters**:
- `walFilePath`: Path to WAL file
- `config`: Group commit configuration
- `fsyncOnFlush`: Whether to fsync on flush (disable for benchmarks)

### 5.2 Core Operations

#### 5.2.1 Append Record

```swift
public func append(
    kind: WALRecordKind,
    txID: TxID,
    pageID: PageID,
    undoNextLSN: LSN = 0,
    payload: Data
) async throws -> LSN
```

**TLA+ Action**: `Append(record)`

**Behavior**:
1. Assign LSN: `lsn = nextLSN; nextLSN++`
2. Set `prevLSN = txLastLSN[txID] ?? 0`
3. Create record with assigned LSN
4. Add to `pendingRecords`
5. Update `txLastLSN[txID] = lsn`
6. Update `pageLSN[pageID] = lsn`
7. If batch size reached, flush automatically

**Preconditions**:
- `~crashed` (system not crashed)

**Postconditions**:
- Record assigned LSN
- Record in `pendingRecords`
- `nextLSN` incremented
- `txLastLSN` updated

**Returns**: Assigned LSN

#### 5.2.2 Flush

```swift
public func flush() async throws
```

**TLA+ Action**: `Flush()`

**Behavior**:
1. Write all `pendingRecords` to disk
2. Update `flushedLSN = max(pendingRecords.lsn)`
3. Append to `wal` array
4. Clear `pendingRecords`
5. Optionally fsync to disk

**Preconditions**:
- `~crashed`
- `pendingRecords # <<>>` (non-empty)

**Postconditions**:
- All pending records flushed
- `flushedLSN` updated
- `pendingRecords` empty
- Records durable on disk

#### 5.2.3 Flush Up To

```swift
public func flush(upTo targetLSN: LSN) async throws
```

**TLA+ Action**: `Flush(upToLSN)`

**Behavior**:
1. Filter records up to `targetLSN`
2. Write to disk
3. Update `flushedLSN`
4. Clear flushed records from `pendingRecords`

**Use Case**: Group commit (flush multiple transactions together)

#### 5.2.4 Update Page LSN

```swift
public func updatePageLSN(_ pageID: PageID, lsn: LSN) throws
```

**TLA+ Action**: `UpdatePageLSN(pageID, lsn)`

**Behavior**:
1. Update `pageLSN[pageID] = lsn`
2. If page not in `dataApplied`, update DPT:
   - `dirtyPageTable[pageID] = lsn` (if not present)

**Preconditions**:
- `~crashed`
- `lsn <= nextLSN`

**Postconditions**:
- `pageLSN` updated
- DPT updated if page dirty

### 5.3 Checkpoint Operations

#### 5.3.1 Checkpoint

```swift
public func checkpoint() throws -> LSN
```

**TLA+ Action**: `Checkpoint()`

**Behavior**:
1. Verify `pendingRecords = <<>>` (empty)
2. Write checkpoint record with:
   - Current `dirtyPageTable`
   - Active transactions
   - Current `flushedLSN`
3. Update `lastCheckpointLSN`
4. Flush checkpoint record

**Preconditions**:
- `~crashed`
- `pendingRecords = <<>>`

**Postconditions**:
- Checkpoint record written
- `lastCheckpointLSN` updated

**Returns**: Checkpoint LSN

### 5.4 Query Operations

#### 5.4.1 Get Flushed LSN

```swift
public func getFlushedLSN() -> LSN
```

**Returns**: Current `flushedLSN`

#### 5.4.2 Get Current LSN

```swift
public func getCurrentLSN() -> LSN
```

**Returns**: Current `nextLSN`

#### 5.4.3 Get Page LSN

```swift
public func getPageLSN(_ pageID: PageID) -> LSN?
```

**Returns**: LSN for page, nil if never modified

## 6. WAL Record Types

### 6.1 Record Structure

```swift
public struct ConcreteWALRecord: Codable, Sendable {
    public let lsn: LSN
    public let prevLSN: LSN
    public let kind: WALRecordKind
    public let txID: TxID
    public let pageID: PageID
    public let undoNextLSN: LSN
    public let payload: Data
    public let timestamp: UInt64
}
```

### 6.2 Record Kinds

| Kind | Description | Use Case |
|------|-------------|----------|
| `heapInsert` | Heap table insert | INSERT operations |
| `heapUpdate` | Heap table update | UPDATE operations |
| `heapDelete` | Heap table delete | DELETE operations |
| `indexInsert` | Index insert | Index maintenance |
| `indexDelete` | Index delete | Index maintenance |
| `commit` | Transaction commit | COMMIT operations |
| `abort` | Transaction abort | ROLLBACK operations |
| `checkpoint` | Checkpoint record | Recovery optimization |

## 7. Group Commit

### 7.1 Group Commit Configuration

```swift
public struct GroupCommitConfig: Codable, Sendable {
    public let maxBatchSize: Int      // Max records per batch
    public let maxBatchTimeMs: Int    // Max time to wait (ms)
    public let enableGroupCommit: Bool
}
```

### 7.2 Group Commit Behavior

1. Append records to `pendingRecords`
2. When batch size reached OR timeout expires:
   - Flush all pending records together
   - Single I/O operation for multiple records
   - Improves throughput

**Benefits**:
- Reduced I/O operations
- Better throughput
- Lower latency per transaction (amortized)

## 8. Invariants (TLA+ Verification)

### 8.1 Log-Before-Data Invariant

```tla
Inv_LogBeforeData ==
    \A pid \in ModifiablePages:
        pageLSN[pid] <= flushedLSN
```

**Swift Implementation**:
```swift
public func checkLogBeforeDataInvariant() -> Bool {
    for (pageID, lsn) in pageLSN {
        guard lsn <= flushedLSN else {
            return false
        }
    }
    return true
}
```

### 8.2 Total Order Invariant

```tla
Inv_TotalOrder ==
    \A i \in 1..Len(wal):
        wal[i].lsn = i /\
        wal[i].prevLSN = wal[i-1].lsn
```

**Swift Implementation**:
```swift
public func checkTotalOrderInvariant() -> Bool {
    for i in 1..<wal.count {
        guard wal[i].lsn == wal[i-1].lsn + 1 else {
            return false
        }
        guard wal[i].prevLSN == wal[i-1].lsn else {
            return false
        }
    }
    return true
}
```

### 8.3 Monotonic LSN Invariant

```tla
Inv_MonotonicLSN ==
    nextLSN > flushedLSN /\
    \A r \in wal:
        r.lsn <= flushedLSN
```

### 8.4 DPT Consistency Invariant

```tla
Inv_DPTConsistency ==
    \A pid \in DOMAIN dirtyPageTable:
        pid \in DOMAIN pageLSN /\
        dirtyPageTable[pid] <= pageLSN[pid]
```

## 9. Recovery Integration

### 9.1 ARIES Recovery Phases

1. **Analysis Phase**: Read WAL to build ATT and DPT
2. **Redo Phase**: Replay all records from `min(DPT.recLSN)`
3. **Undo Phase**: Undo uncommitted transactions

### 9.2 Checkpoint Optimization

Checkpoints reduce recovery time:
- Start redo from `lastCheckpointLSN`
- Use checkpoint DPT as initial DPT
- Skip records before checkpoint

## 10. Performance Characteristics

### 10.1 Throughput

Target: > 10,000 TPS (transactions per second)

**Optimizations**:
- Group commit for batched writes
- Async I/O for non-blocking operations
- APFS optimizations (RFC 0060)

### 10.2 Latency

Target: < 1ms average latency for append

**Optimizations**:
- In-memory `pendingRecords` queue
- Batched flushes (group commit)
- Fsync optional for benchmarks

### 10.3 Durability

Guaranteed:
- All committed records durable
- Fsync on flush (if enabled)
- Crash recovery possible

## 11. Error Handling

### 11.1 Error Types

```swift
public enum WALError: Error {
    case appendFailed
    case flushFailed
    case checkpointFailed
    case fileIOError(String)
}
```

### 11.2 Error Recovery

- **Append Failed**: Return error, transaction aborts
- **Flush Failed**: Retry or abort
- **File IO Error**: Log and propagate

## 12. Apple-First Optimizations

### 12.1 APFS Features

- **Clones**: Efficient checkpoint snapshots (future)
- **Compression**: Transparent compression
- **Snapshots**: Point-in-time recovery

### 12.2 File System Integration

- **FileHandle**: Native Swift file operations
- **Async I/O**: Non-blocking operations
- **Memory-Mapped Files**: Future optimization

### 12.3 Performance

- **GCD**: Efficient task scheduling
- **Value Types**: Stack allocation where possible
- **ARC**: Automatic memory management

## 13. Testing

### 13.1 Unit Tests

- Append and flush operations
- LSN assignment correctness
- DPT maintenance
- Checkpoint creation
- Invariant verification

### 13.2 Integration Tests

- WAL + Buffer Manager coordination
- WAL + Transaction Manager integration
- Recovery scenarios
- Concurrent access

### 13.3 Performance Tests

- Throughput measurements
- Latency measurements
- Group commit effectiveness
- Durability verification

## 14. References

- **RFC 0004**: Buffer Manager
- **RFC 0019**: Transaction Manager
- **RFC 0032**: ARIES Recovery
- **TLA+ Spec**: `spec/WAL.tla`
- **Mohan et al., 1992**: "ARIES: A Transaction Recovery Method"

---

**Next**: See RFC 0019 for Transaction Manager details.

