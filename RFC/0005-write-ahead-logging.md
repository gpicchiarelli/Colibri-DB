# RFC 0005: Write-Ahead Logging (WAL)

**Status**: Standards Track  
**Author**: ColibrìDB Team  
**Date**: 2025-11-18  
**TLA+ Spec**: `spec/WAL.tla`

## Abstract

This RFC defines the Write-Ahead Logging (WAL) component, responsible for ensuring data durability and crash recovery through the Log-Before-Data property.

## 1. Introduction

The Write-Ahead Log is a critical component that ensures all changes to data pages are logged before being written to disk. This guarantees durability and enables crash recovery using the ARIES algorithm.

### 1.1 Purpose and Goals

The primary goals of the Write-Ahead Log are:

1. **Durability Guarantee**: Ensure committed transactions survive crashes
2. **Crash Recovery**: Enable ARIES recovery algorithm to reconstruct database state
3. **Log-Before-Data**: Enforce that WAL records are flushed before data pages
4. **Total Order**: Maintain sequential order of log records for recovery
5. **Performance**: Minimize impact on transaction throughput through group commit

### 1.2 Problem Statement

Database systems face the challenge of ensuring durability while maintaining performance:

- **Crash Risk**: System crashes can occur at any time, losing uncommitted data
- **Performance**: Durability requires disk I/O, which is slow (~5-10ms)
- **Atomicity**: Transactions must be all-or-nothing even during crashes
- **Consistency**: Database must remain consistent after recovery

The WAL solves these challenges by:

- **Logging Before Data**: All changes logged before being written to data pages
- **Group Commit**: Batch multiple transactions together for better throughput
- **Sequential Ordering**: Log records maintain order for correct recovery
- **Crash Recovery**: ARIES algorithm uses WAL to reconstruct database state

### 1.3 Key Concepts

**WAL (Write-Ahead Log)**: Sequential log file containing all database changes.

**LSN (Log Sequence Number)**: Monotonically increasing number assigned to each log record.

**Log-Before-Data Property**: Critical invariant ensuring WAL records are flushed before corresponding data pages:
```
\A pid \in ModifiablePages:
    pageLSN[pid] <= flushedLSN
```

**Dirty Page Table (DPT)**: Tracks which pages have been modified and their recLSN (recovery LSN):
- `dirtyPageTable[pageId] = recLSN`: First LSN that modified this page

**Flushed LSN**: Highest LSN that has been durably written to disk.

**Pending Records**: Log records in memory waiting to be flushed.

**Group Commit**: Batching multiple transaction commits together for efficiency.

**Checkpoint**: Periodic snapshot of database state for faster recovery.

### 1.4 Relationship to Other Components

```
WAL
├── Used by: Transaction Manager (for durability)
├── Coordinates with: Buffer Manager (for flushedLSN)
├── Used by: ARIES Recovery (for crash recovery)
└── Written by: Storage Manager, Index Manager, etc.
```

**Transaction Manager → WAL**:
- Transaction commits write commit record to WAL
- Transaction aborts write abort record to WAL
- WAL flush ensures transaction durability

**Buffer Manager ← WAL**:
- WAL updates BufferManager.flushedLSN after flush
- Buffer Manager checks WAL-before-data before flushing pages
- Buffer Manager flushes dirty pages only after WAL flush

**ARIES Recovery → WAL**:
- Recovery reads WAL records in order
- Replays committed transactions (redo)
- Undoes uncommitted transactions (undo)

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

**Behavior**: Detailed step-by-step execution

1. **Validate System State**:
   ```swift
   guard !crashed else {
       throw WALError.appendFailed("System crashed")
   }
   ```
   - System must not be in crashed state
   - Cannot append records during recovery

2. **Assign LSN**:
   ```swift
   let lsn = nextLSN
   nextLSN += 1
   ```
   - **LSN Assignment**: Monotonically increasing sequence
   - **Atomic**: Single actor ensures no race conditions
   - **Unique**: Each record gets unique LSN

3. **Get Previous LSN**:
   ```swift
   let prevLSN = txLastLSN[txID] ?? 0
   ```
   - **Chain Records**: Links records within same transaction
   - **Undo Chain**: Enables rolling back transaction
   - **First Record**: prevLSN = 0 for first record in transaction

4. **Create WAL Record**:
   ```swift
   let record = ConcreteWALRecord(
       lsn: lsn,
       prevLSN: prevLSN,
       kind: kind,
       txID: txID,
       pageID: pageID,
       undoNextLSN: undoNextLSN,
       payload: payload,
       timestamp: UInt64(Date().timeIntervalSince1970 * 1000)
   )
   ```
   - **Record Structure**: All metadata and data
   - **Timestamp**: Wall-clock time for debugging
   - **Payload**: Actual data changes

5. **Add to Pending Records**:
   ```swift
   pendingRecords.append(record)
   ```
   - **In-Memory Queue**: Records waiting for flush
   - **Ordered**: Maintains LSN order
   - **Not Yet Durable**: Only durable after flush

6. **Update Transaction Last LSN**:
   ```swift
   txLastLSN[txID] = lsn
   ```
   - **Track Transaction**: Record latest LSN per transaction
   - **Undo Chain**: Links records for rollback
   - **Recovery**: Used to find transaction boundaries

7. **Update Page LSN**:
   ```swift
   pageLSN[pageID] = lsn
   ```
   - **Track Pages**: Record latest LSN per page
   - **WAL-Before-Data**: Used to enforce log-before-data property
   - **Recovery**: Used to determine redo start point

8. **Update Dirty Page Table**:
   ```swift
   if dirtyPageTable[pageID] == nil {
       dirtyPageTable[pageID] = lsn  // recLSN
   }
   ```
   - **First Modification**: Records recLSN (first LSN that modified page)
   - **Recovery**: Used to determine redo start point
   - **Checkpoint**: Included in checkpoints for faster recovery

9. **Check Group Commit Threshold**:
   ```swift
   if pendingRecords.count >= config.maxBatchSize {
       try await flush()
   }
   ```
   - **Automatic Flush**: Flushes when batch size reached
   - **Group Commit**: Batches multiple transactions
   - **Performance**: Reduces per-transaction flush overhead

**Preconditions**:
- `~crashed` (system not crashed)
- `txID` is valid (non-zero transaction ID)
- `pageID` is valid (non-zero page ID if applicable)
- `payload` is valid (non-empty for data records)

**Postconditions**:
- Record assigned LSN (`lsn = nextLSN - 1`)
- Record in `pendingRecords` (at end of queue)
- `nextLSN` incremented (`nextLSN = oldNextLSN + 1`)
- `txLastLSN[txID] = lsn` (updated)
- `pageLSN[pageID] = lsn` (updated)
- `dirtyPageTable[pageID]` may be updated (if first modification)

**Returns**: Assigned LSN

**Performance Characteristics**:
- **Append**: ~100ns (in-memory operation)
- **With Auto-Flush**: +5-10ms (if batch size reached)
- **Scalable**: O(1) append operation

**LSN Assignment Guarantees**:

1. **Monotonicity**: LSNs are always increasing
   ```
   \A i, j \in DOMAIN wal:
       i < j => wal[i].lsn < wal[j].lsn
   ```

2. **Uniqueness**: No two records have same LSN
   ```
   \A i, j \in DOMAIN wal:
       i # j => wal[i].lsn # wal[j].lsn
   ```

3. **Sequential**: LSNs are sequential (no gaps during normal operation)
   ```
   \A i \in 1..Len(wal):
       wal[i].lsn = wal[i-1].lsn + 1
   ```

**Example Usage**:
```swift
// Transaction modifies page
let lsn = try await wal.append(
    kind: .heapUpdate,
    txID: txId,
    pageID: pageId,
    undoNextLSN: 0,  // Will be set by caller for undo chain
    payload: updateData
)

// Update page LSN
page.lsn = lsn

// Later: Transaction commits
let commitLSN = try await wal.append(
    kind: .commit,
    txID: txId,
    pageID: 0,  // No page for commit record
    payload: Data()
)

// Flush WAL (ensures durability)
try await wal.flush()
```

**Edge Cases**:

1. **LSN Overflow**: UInt64 can represent ~1.8*10^19 LSNs
   - **Likelihood**: Extremely unlikely (millions of years of operation)
   - **Solution**: If overflow, wrap around (acceptable for most use cases)

2. **System Crash During Append**:
   - **Behavior**: Record in `pendingRecords` but not durable
   - **Recovery**: ARIES recovery handles incomplete transactions
   - **Safety**: Transaction not committed until WAL flushed

3. **Concurrent Appends**:
   - **Behavior**: Actor isolation serializes operations
   - **Safety**: No race conditions, LSNs assigned sequentially
   - **Performance**: May serialize unnecessarily (acceptable)

4. **Very Large Payload**:
   - **Behavior**: Payload stored as-is (no size limit enforced)
   - **Performance**: Large payloads slow down flush
   - **Optimization**: Consider splitting large records into multiple smaller records

**Errors**:
- `WALError.appendFailed`: Cannot append record (system crashed, invalid state, etc.)

#### 5.2.2 Flush

```swift
public func flush() async throws
```

**TLA+ Action**: `Flush()`

**Behavior**: Detailed step-by-step execution

1. **Validate System State**:
   ```swift
   guard !crashed else {
       throw WALError.flushFailed("System crashed")
   }
   ```
   - System must not be crashed
   - Cannot flush during recovery

2. **Check if Pending Records Exist**:
   ```swift
   guard !pendingRecords.isEmpty else {
       return  // Nothing to flush
   }
   ```
   - **Early Exit**: Optimized path if no pending records
   - **Idempotent**: Safe to call multiple times
   - **Performance**: Avoids unnecessary I/O

3. **Serialize Records to Disk Format**:
   ```swift
   let encoder = JSONEncoder()
   let serializedData = try encoder.encode(pendingRecords)
   ```
   - **Encoding**: JSON encoding for durability
   - **Future**: Could use binary format for better performance
   - **Size**: ~100 bytes per record overhead (JSON)

4. **Write to WAL File**:
   ```swift
   try fileHandle.write(serializedData)
   ```
   - **File Handle**: Native Swift FileHandle for I/O
   - **Atomic**: Single write operation
   - **Position**: Appends to end of file (sequential write)

5. **Optionally Fsync**:
   ```swift
   if fsyncEnabled {
       try fileHandle.synchronizeFile()
   }
   ```
   - **Durability**: Fsync ensures data on stable storage
   - **Performance**: Fsync is slow (~10ms on HDD, ~1ms on SSD)
   - **Configurable**: Disabled for benchmarks, enabled for production

6. **Update Flushed LSN**:
   ```swift
   flushedLSN = pendingRecords.map { $0.lsn }.max() ?? flushedLSN
   ```
   - **Maximum LSN**: Highest LSN in batch
   - **Monotonic**: Always increases (or stays same)
   - **Critical**: Used for WAL-before-data property

7. **Move Records to Flushed Array**:
   ```swift
   wal.append(contentsOf: pendingRecords)
   ```
   - **In-Memory Copy**: Keep records in memory for recovery
   - **Ordered**: Maintains LSN order
   - **Bounded**: May need to trim old records (future optimization)

8. **Clear Pending Records**:
   ```swift
   pendingRecords.removeAll()
   ```
   - **Empty Queue**: Ready for next batch
   - **Memory**: Frees memory (but records still in `wal` array)

9. **Update Buffer Manager** (if available):
   ```swift
   // Caller should update BufferManager.flushedLSN
   // await bufferManager.updateFlushedLSN(flushedLSN)
   ```
   - **Coordination**: Notifies Buffer Manager of flush
   - **WAL-Before-Data**: Enables buffer page flushing
   - **Responsibility**: Typically done by caller (Transaction Manager)

**Preconditions**:
- `~crashed` (system not crashed)
- `pendingRecords` may be empty (early exit if empty)

**Postconditions**:
- All pending records flushed to disk
- `flushedLSN` updated (`flushedLSN = max(pendingRecords.lsn)`)
- `pendingRecords` empty (`pendingRecords = []`)
- Records in `wal` array (flushed records)
- Records durable on disk (if fsync enabled)

**Performance Characteristics**:
- **Flush Time**: ~5-10ms (disk I/O dominates)
  - Write: ~1ms (SSD) to ~5ms (HDD)
  - Fsync: ~1ms (SSD) to ~10ms (HDD)
- **Without Fsync**: ~1-5ms (just write)
- **With Fsync**: ~2-15ms (write + fsync)

**Latency Breakdown**:

| Component | SSD | HDD |
|-----------|-----|-----|
| Serialization | ~100μs | ~100μs |
| Disk Write | ~1ms | ~5ms |
| Fsync | ~1ms | ~10ms |
| Updates | ~10μs | ~10μs |
| **Total (no fsync)** | **~1.1ms** | **~5.1ms** |
| **Total (with fsync)** | **~2.1ms** | **~15.1ms** |

**Group Commit Benefits**:

1. **Reduced I/O**: Single write for multiple transactions
2. **Amortized Cost**: Flush overhead shared across transactions
3. **Better Throughput**: Higher transactions per second
4. **Lower Latency**: Per-transaction latency reduced

**Example**: 10 transactions commit together
- **Without Group Commit**: 10 flushes × 2ms = 20ms total, 2ms per transaction
- **With Group Commit**: 1 flush × 2ms = 2ms total, 0.2ms per transaction

**Edge Cases**:

1. **Empty Pending Records**:
   - **Behavior**: Early return (no I/O)
   - **Performance**: Optimized path
   - **Idempotent**: Safe to call multiple times

2. **Disk Full During Flush**:
   - **Behavior**: `FileHandle.write()` throws error
   - **State**: Records remain in `pendingRecords` (not flushed)
   - **Recovery**: Handle disk space, retry flush
   - **Error**: `DBError.ioError` propagated to caller

3. **Fsync Failure**:
   - **Behavior**: Fsync throws error
   - **State**: Records written but may not be durable
   - **Recovery**: Retry fsync or handle hardware failure
   - **Warning**: Data may not be durable on crash

4. **Concurrent Flush**:
   - **Behavior**: Actor isolation serializes operations
   - **Safety**: Only one flush at a time
   - **Result**: Records flushed in order

5. **Very Large Batch**:
   - **Behavior**: All records flushed together
   - **Performance**: Single large write is efficient
   - **Limitation**: Memory usage for large batches

**Errors**:
- `WALError.flushFailed`: Cannot flush records (system crashed, disk full, I/O error, etc.)
- `DBError.ioError`: Disk I/O failed (propagated from FileHandle)

**Durability Guarantees**:

1. **With Fsync Enabled** (default):
   - Records guaranteed on stable storage
   - Survives system crash, power loss
   - Slower (~2-15ms per flush)

2. **Without Fsync** (benchmarks):
   - Records may be in OS buffer cache
   - May be lost on crash or power loss
   - Faster (~1-5ms per flush)

**Best Practices**:

1. **Always Use Fsync in Production**:
   ```swift
   let wal = try FileWAL(
       walFilePath: walPath,
       fsyncOnFlush: true  // Required for production
   )
   ```

2. **Use Group Commit**:
   ```swift
   // Configure group commit
   let config = GroupCommitConfig(
       maxBatchSize: 100,      // Flush when 100 records
       maxBatchTimeMs: 10,     // Or after 10ms
       enableGroupCommit: true
   )
   ```

3. **Monitor Flush Performance**:
   ```swift
   let start = Date()
   try await wal.flush()
   let latency = Date().timeIntervalSince(start) * 1000
   print("Flush latency: \(latency)ms")
   ```

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

**Configuration Parameters**:

1. **maxBatchSize**: Maximum number of records before automatic flush
   - **Typical**: 100-1000 records
   - **Trade-off**: Larger batch = better throughput, higher latency
   - **Example**: `maxBatchSize = 100` flushes when 100 records queued

2. **maxBatchTimeMs**: Maximum time to wait before flush
   - **Typical**: 10-100ms
   - **Purpose**: Ensures low latency even with low transaction rate
   - **Example**: `maxBatchTimeMs = 10` flushes after 10ms even if batch not full

3. **enableGroupCommit**: Enable/disable group commit
   - **Default**: `true` (enabled)
   - **Disable**: For testing or single-threaded scenarios
   - **Performance**: Disabling reduces throughput

**Default Configuration**:
```swift
public init() {
    self.maxBatchSize = 100
    self.maxBatchTimeMs = 10
    self.enableGroupCommit = true
}
```

### 7.2 Group Commit Behavior

**Algorithm**:

1. **Append Records**:
   ```swift
   // Records appended to pendingRecords
   pendingRecords.append(record)
   ```

2. **Check Batch Size Threshold**:
   ```swift
   if pendingRecords.count >= config.maxBatchSize {
       try await flush()
       return
   }
   ```

3. **Schedule Timeout Flush** (if not already scheduled):
   ```swift
   // Background task checks timeout
   Task {
       try? await Task.sleep(nanoseconds: UInt64(config.maxBatchTimeMs) * 1_000_000)
       if !pendingRecords.isEmpty {
           try? await flush()
       }
   }
   ```

4. **Flush When Threshold Reached**:
   - Batch size reached: Immediate flush
   - Timeout expired: Immediate flush
   - Both: Single flush operation

**Benefits**:

1. **Reduced I/O Operations**:
   - **Without Group Commit**: 1 flush per transaction = N flushes for N transactions
   - **With Group Commit**: 1 flush per batch = N/B flushes for N transactions (B = batch size)
   - **Example**: 100 transactions, batch size 10 = 10 flushes (vs 100 without group commit)

2. **Better Throughput**:
   - **Amortized Cost**: Flush overhead shared across transactions
   - **Sequential Writes**: Better disk performance
   - **Example**: 10x throughput improvement with batch size 10

3. **Lower Latency** (amortized):
   - **Per-Transaction**: Latency reduced by batching
   - **Example**: 2ms flush / 10 transactions = 0.2ms per transaction (vs 2ms without)

**Performance Characteristics**:

| Batch Size | Flushes/sec | Throughput | Avg Latency |
|------------|-------------|------------|-------------|
| 1 (disabled) | 500 | 500 tps | 2ms |
| 10 | 50 | 500 tps | 0.2ms |
| 100 | 5 | 500 tps | 0.02ms |
| 1000 | 0.5 | 500 tps | 0.002ms |

**Trade-offs**:

1. **Larger Batch Size**:
   - **Pros**: Better throughput, fewer I/O operations
   - **Cons**: Higher memory usage, slightly higher max latency
   - **Recommendation**: 100-1000 for typical workloads

2. **Smaller Batch Size**:
   - **Pros**: Lower memory usage, lower max latency
   - **Cons**: More I/O operations, lower throughput
   - **Recommendation**: 10-100 for low-latency requirements

3. **Timeout Configuration**:
   - **Shorter Timeout**: Lower latency, more frequent flushes
   - **Longer Timeout**: Better batching, fewer flushes
   - **Recommendation**: 10-100ms for balance

**Example Workloads**:

1. **OLTP (High Transaction Rate)**:
   ```swift
   let config = GroupCommitConfig(
       maxBatchSize: 1000,      // Large batch for throughput
       maxBatchTimeMs: 50,      // Longer timeout for batching
       enableGroupCommit: true
   )
   ```

2. **OLTP (Low Latency Required)**:
   ```swift
   let config = GroupCommitConfig(
       maxBatchSize: 10,        // Small batch for low latency
       maxBatchTimeMs: 5,       // Short timeout for responsiveness
       enableGroupCommit: true
   )
   ```

3. **OLAP (Bulk Operations)**:
   ```swift
   let config = GroupCommitConfig(
       maxBatchSize: 10000,     // Very large batch for bulk operations
       maxBatchTimeMs: 100,     // Longer timeout acceptable
       enableGroupCommit: true
   )
   ```

### 7.3 Group Commit Implementation

**Background Flush Task**:
```swift
private var flushTask: Task<Void, Never>?

private func scheduleFlushIfNeeded() {
    guard config.enableGroupCommit else { return }
    guard flushTask == nil else { return }  // Already scheduled
    
    flushTask = Task {
        try? await Task.sleep(nanoseconds: UInt64(config.maxBatchTimeMs) * 1_000_000)
        
        if !pendingRecords.isEmpty {
            try? await flush()
        }
        
        flushTask = nil
    }
}
```

**Flush Trigger Logic**:
```swift
// In append()
pendingRecords.append(record)

// Check if should flush immediately
if pendingRecords.count >= config.maxBatchSize {
    try await flush()
} else {
    // Schedule timeout flush if not already scheduled
    scheduleFlushIfNeeded()
}
```

**Cancellation**:
```swift
// Cancel flush task when immediate flush occurs
flushTask?.cancel()
flushTask = nil
```

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

