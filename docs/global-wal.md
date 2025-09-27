# Global Write-Ahead Log (WAL) Architecture

## Overview

ColibrìDB implements a **unified Global WAL** system that provides ACID guarantees and crash recovery for the entire database instance. This replaces the previous multiple WAL approach with a single, consistent logging mechanism.

## Key Features

### ✅ **Single WAL Instance**
- One `FileWALManager` per database instance
- Global LSN (Log Sequence Number) monotonically increasing
- All tables, indexes, and catalog operations logged to same WAL

### ✅ **Typed Record System**
All operations are logged as strongly-typed records:

```swift
public enum WALKind: UInt8 {
    case begin = 1
    case commit = 2
    case abort = 3
    case heapInsert = 10
    case heapUpdate = 11
    case heapDelete = 12
    case indexInsert = 20
    case indexDelete = 21
    case catalogCreate = 30
    case catalogDrop = 31
    case catalogUpdate = 32
    case checkpoint = 40
    case clr = 50  // Compensation Log Record
}
```

### ✅ **WAL-Before-Data Guarantee**
- All modifications logged before application
- PageLSN tracking ensures consistency
- `page.pageLSN ≤ wal.flushedLSN` enforced on flush

### ✅ **Group Commit Optimization**
- Configurable batch size (default: 8 records)
- Timeout-based flushing (default: 2ms)
- Automatic compression for large records (>1KB)

### ✅ **Durability Modes**
```swift
public enum DurabilityMode {
    case always      // fsync after every record
    case grouped     // group commit with timeout
    case relaxed     // asynchronous, risk of loss on crash
}
```

## Record Format

### Header Structure
```
[CRC32: 4 bytes][Type: 1 byte][LSN: 8 bytes][DbId: 4 bytes][PageId: 8 bytes][Length: 4 bytes][Payload: variable]
```

### Compression
- Optional LZFSE/zlib compression for large payloads
- Compression flag in type byte
- Automatic threshold-based activation

## ARIES-Style Recovery

### Phase 1: Analysis
- Scan WAL from last checkpoint
- Rebuild Active Transaction Table (ATT)
- Rebuild Dirty Page Table (DPT)

### Phase 2: REDO
- Apply all logged operations idempotently
- Use PageLSN to avoid duplicate application
- Restore database to crash-consistent state

### Phase 3: UNDO
- Roll back uncommitted transactions
- Generate CLR (Compensation Log Records)
- Ensure atomic rollback semantics

## Integration Points

### Database Operations
```swift
// Transaction lifecycle
let lsn = logTransactionBegin(tid: tid, isolationLevel: level)
let lsn = logTransactionCommit(tid: tid)
let lsn = logTransactionAbort(tid: tid)

// Heap operations
let lsn = logHeapInsert(tid: tid, table: table, pageId: pageId, slotId: slotId, row: row)
let lsn = logHeapDelete(tid: tid, table: table, pageId: pageId, slotId: slotId, row: row)

// Index operations  
let lsn = logIndexInsert(tid: tid, indexId: indexId, table: table, keyBytes: keyBytes, rid: rid)
let lsn = logIndexDelete(tid: tid, indexId: indexId, table: table, keyBytes: keyBytes, rid: rid)
```

### Buffer Pool Integration
```swift
// WAL-ahead-of-page enforcement
public func flush(fullSync: Bool = false, wal: FileWALManager?) throws {
    if let wal = wal {
        let flushedLSN = wal.flushedLSN
        let dirtyPages = buffer.getDirtyPages()
        
        for pageId in dirtyPages {
            if let pageLSN = getPageLSN(pageId) {
                assert(pageLSN <= flushedLSN, 
                      "WAL-ahead-of-page violation: page \(pageId) LSN \(pageLSN) > flushed WAL LSN \(flushedLSN)")
            }
        }
    }
    
    try buf?.flushAll()
    try IOHints.synchronize(handle: fh, full: fullSync)
}
```

## Performance Characteristics

### Group Commit Metrics
```swift
let metrics = globalWAL.metrics
print("Throughput: \(metrics.appendsPerSecond) ops/sec")
print("Average batch: \(metrics.averageBatchSize)")
print("P95 latency: \(metrics.p95CommitLatencyMs)ms")
print("Compression ratio: \(metrics.compressionRatio ?? 1.0)")
```

### Expected Performance
- **WAL Append (uncompressed)**: 100K+ ops/sec
- **WAL Append (compressed)**: 50K+ ops/sec  
- **Group Commit**: 8-16 records/batch under load
- **Transaction Commit**: 3K-10K commits/sec (grouped mode)
- **fsync Operations**: 200-500/sec (hardware dependent)

## Configuration

### Database Config
```swift
public struct DBConfig {
    public var walEnabled: Bool = true
    public var walFullFSyncEnabled: Bool = false
    public var walGroupCommitMs: Double = 2.0
    public var walCompression: CompressionAlgorithm = .none
    public var walUseGlobalIndexLogging: Bool = true
}
```

### FileWALManager Init
```swift
let globalWAL = try FileWALManager(
    dbId: 1,
    path: "/path/to/global.wal",
    durabilityMode: .grouped,
    groupCommitThreshold: 8,
    groupCommitTimeoutMs: 2.0,
    compressionAlgorithm: .zlib
)
```

## Migration from Legacy WAL

### What Changed
1. **Single WAL file**: `global.wal` instead of multiple `wal.log` + index WALs
2. **Typed records**: Strongly-typed WAL records instead of generic payloads
3. **Global LSN**: Monotonic LSN across all operations
4. **Unified recovery**: Single recovery process for all components

### Backward Compatibility
- Legacy WAL files are no longer read automatically
- Migration tool would be needed to convert old WAL format
- New installations start fresh with global WAL

### API Changes
- `FileWAL` → `FileWALManager`
- `wal.append()` → typed record methods
- `wal.flushedLSN` remains the same interface
- Recovery API unchanged externally

## Monitoring and Debugging

### WAL Health Checks
```swift
// Check WAL state
let flushedLSN = globalWAL.flushedLSN
let nextLSN = try globalWAL.lastLSN() + 1
let queueDepth = globalWAL.metrics.queueDepth

// Verify page consistency
for pageId in dirtyPages {
    let pageLSN = getPageLSN(pageId)
    assert(pageLSN <= flushedLSN, "WAL consistency violation")
}
```

### Error Handling
```swift
public enum WALError: Error {
    case corruptedHeader(String)
    case incompatibleVersion(String)
    case mismatchedDatabase(String)
    case corruptedRecord(String)
    case ioError(String)
}
```

## Best Practices

### 1. **Always Use Transactions**
```swift
let tid = try database.begin()
defer { try? database.rollback(tid) }

// Perform operations...
try database.insert(into: "users", row: userData, tid: tid)
try database.commit(tid)
```

### 2. **Monitor WAL Growth**
- Checkpoint regularly to truncate WAL
- Monitor `globalWAL.metrics.queueDepth`
- Set appropriate `groupCommitThreshold`

### 3. **Handle Crash Recovery**
```swift
// Recovery is automatic on database open
let database = Database(config: config)
// WAL replay happens during initialization
```

### 4. **Tune for Workload**
- **OLTP**: `durabilityMode = .grouped`, `groupCommitTimeoutMs = 1-2`
- **Batch**: `durabilityMode = .always` or higher timeout
- **Analytics**: `durabilityMode = .relaxed` (careful!)

## Troubleshooting

### Common Issues

**WAL file grows too large:**
- Increase checkpoint frequency
- Check for long-running transactions
- Monitor group commit effectiveness

**Poor commit performance:**
- Verify group commit is enabled
- Check disk fsync latency
- Consider SSD/NVMe storage

**Recovery takes too long:**
- More frequent checkpoints
- Validate WAL file isn't corrupted
- Check available memory for buffer pool

**WAL corruption:**
- Check disk health
- Verify filesystem integrity
- Review recent system crashes

## Future Enhancements

- [ ] **Incremental checkpoints** for large databases
- [ ] **WAL shipping** for replication
- [ ] **Parallel recovery** for faster startup
- [ ] **Online WAL compression** tuning
- [ ] **Cross-database transactions** (distributed WAL)
