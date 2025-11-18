# RFC 0006: Storage Manager

**Status**: Standards Track  
**Author**: ColibrìDB Team  
**Date**: 2025-11-18  
**TLA+ Spec**: `spec/Storage.tla`

## Abstract

This RFC defines the Storage Manager component, responsible for managing disk I/O operations, page allocation/deallocation, and integrating with the Buffer Manager for efficient caching.

## 1. Introduction

The Storage Manager provides high-level storage operations, coordinating with the Buffer Manager for page caching and with the Disk Manager for physical I/O. It manages storage areas (data, index, log, temp, system) and tracks free space.

## 2. Design Principles

### 2.1 Buffer Manager Integration

The Storage Manager integrates with the Buffer Manager when available:
- Uses buffer cache for page reads/writes
- Falls back to direct disk I/O if Buffer Manager unavailable
- Maintains WAL-before-data property through coordination

### 2.2 Storage Areas

Organizes storage into logical areas:
- **Data**: User data pages
- **Index**: Index pages
- **Log**: Log pages (separate from WAL)
- **Temp**: Temporary pages
- **System**: System catalog pages

### 2.3 Space Management

Tracks free space per page:
- Free space map: `[PageID -> FreeSpace]`
- Efficient allocation using free space map
- Automatic space management

## 3. Architecture

### 3.1 Component Overview

```
StorageManagerActor (Swift Actor)
├── pages: [PageID -> Page]
├── records: [RecordID -> Record]
├── freeSpaceMap: [PageID -> UInt64]
├── storageAreas: [StorageArea -> [PageID]]
├── metrics: StorageMetrics
├── diskManager: DiskManager
├── bufferManager: BufferManager? (optional)
├── compressionService: CompressionService
└── encryptionService: EncryptionService
```

### 3.2 Dependencies

- **DiskManager**: Physical I/O operations
- **BufferManager** (optional): Page caching
- **CompressionService**: Data compression
- **EncryptionService**: Data encryption

## 4. State Variables (TLA+ Mapping)

| Swift Variable | TLA+ Variable | Type | Description |
|----------------|---------------|------|-------------|
| `pages` | `pages` | `[PageID -> Page]` | Allocated pages |
| `records` | `records` | `[RecordID -> Record]` | Records |
| `freeSpaceMap` | `freeSpaceMap` | `[PageID -> UInt64]` | Free space per page |
| `storageAreas` | `storageAreas` | `[StorageArea -> [PageID]]` | Pages per area |
| `metrics` | `metrics` | `StorageMetrics` | Performance metrics |

## 5. API Specification

### 5.1 Initialization

```swift
public actor StorageManagerActor {
    public init(
        diskManager: DiskManager,
        compressionService: CompressionService,
        encryptionService: EncryptionService,
        bufferManager: BufferManager? = nil
    )
}
```

**Parameters**:
- `diskManager`: Disk manager for I/O operations
- `compressionService`: Compression service
- `encryptionService`: Encryption service
- `bufferManager`: Optional buffer manager for caching

### 5.2 Page Operations

#### 5.2.1 Allocate Page

```swift
public func allocatePage(area: StorageArea, size: UInt64) async throws -> PageID
```

**TLA+ Action**: `AllocatePage(area, size)`

**Behavior**:
1. Find free page in area with sufficient space
2. If no free page, create new page
3. Update `freeSpaceMap`
4. Add to `storageAreas`
5. Update metrics

**Preconditions**:
- `size > 0`

**Postconditions**:
- Page allocated
- Page in `pages` and `storageAreas`
- `freeSpaceMap` updated

**Returns**: Allocated `PageID`

#### 5.2.2 Deallocate Page

```swift
public func deallocatePage(pageId: PageID) async throws
```

**TLA+ Action**: `DeallocatePage(pageId)`

**Behavior**:
1. Check if page exists
2. Remove from `pages`
3. Remove from `freeSpaceMap`
4. Remove from `storageAreas`
5. Update metrics

**Preconditions**:
- Page exists

**Postconditions**:
- Page deallocated
- Page removed from all maps

#### 5.2.3 Read Page

```swift
public func readPage(pageId: PageID) async throws -> Data
```

**TLA+ Action**: `ReadPage(pageId)`

**Behavior**:
1. If `bufferManager` available:
   - Get page from buffer (pins automatically)
   - Unpin immediately after reading
   - Return page data
2. Otherwise:
   - Read directly from disk
   - Return data
3. Update metrics (I/O operations, latency)

**Preconditions**:
- Page exists

**Postconditions**:
- Page data returned
- Metrics updated

**Returns**: Page data as `Data`

#### 5.2.4 Write Page

```swift
public func writePage(pageId: PageID, data: Data) async throws
```

**TLA+ Action**: `WritePage(pageId, data)`

**Behavior**:
1. If `bufferManager` available:
   - If page in cache: update existing page
   - Otherwise: create new buffer page
   - Mark as dirty
   - Unpin after writing
2. Otherwise:
   - Write directly to disk
3. Update metrics (I/O operations, latency)

**Preconditions**:
- Page exists (if updating)
- `data.count > 0`

**Postconditions**:
- Page written (to buffer or disk)
- Metrics updated

### 5.3 Record Operations

#### 5.3.1 Read Record

```swift
public func readRecord(recordId: RecordID) async throws -> Record
```

**TLA+ Action**: `ReadRecord(recordId)`

**Behavior**:
1. Check if record exists
2. Return record
3. Update metrics

**Preconditions**:
- Record exists

**Postconditions**:
- Record returned
- Metrics updated

**Returns**: Record

#### 5.3.2 Write Record

```swift
public func writeRecord(recordId: RecordID, data: Data) async throws
```

**TLA+ Action**: `WriteRecord(recordId, data)`

**Behavior**:
1. Create record with provided data
2. Store in `records` map
3. Update metrics

**Postconditions**:
- Record stored
- Metrics updated

#### 5.3.3 Update Record

```swift
public func updateRecord(recordId: RecordID, data: Data) async throws
```

**TLA+ Action**: `UpdateRecord(recordId, data)`

**Behavior**:
1. Check if record exists
2. Update record data
3. Update timestamp
4. Update metrics

**Preconditions**:
- Record exists

**Postconditions**:
- Record updated
- Metrics updated

#### 5.3.4 Delete Record

```swift
public func deleteRecord(recordId: RecordID) async throws
```

**TLA+ Action**: `DeleteRecord(recordId)`

**Behavior**:
1. Check if record exists
2. Mark record as deleted
3. Update metrics

**Preconditions**:
- Record exists

**Postconditions**:
- Record marked deleted
- Metrics updated

### 5.4 Space Management

#### 5.4.1 Manage Free Space

```swift
public func manageFreeSpace() async throws
```

**TLA+ Action**: `ManageFreeSpace()`

**Behavior**:
1. Update `freeSpaceMap` for all pages
2. Calculate free space per page
3. Update metrics

**Postconditions**:
- `freeSpaceMap` updated
- Metrics updated

### 5.5 Query Operations

#### 5.5.1 Get Page Count

```swift
public func getPageCount() -> Int
```

**Returns**: Total number of pages

#### 5.5.2 Get Record Count

```swift
public func getRecordCount() -> Int
```

**Returns**: Total number of records

#### 5.5.3 Get Storage Metrics

```swift
public func getStorageMetrics() -> StorageMetrics
```

**Returns**: Storage performance metrics

**Metrics**:
- `totalPages`: Total pages
- `usedPages`: Used pages
- `freePages`: Free pages
- `totalRecords`: Total records
- `usedSpace`: Used space (bytes)
- `freeSpace`: Free space (bytes)
- `ioOperations`: Total I/O operations
- `averageLatency`: Average latency (ms)

## 6. Buffer Manager Integration

### 6.1 Cache-First Strategy

When `bufferManager` is available:

1. **Read Operations**:
   - Use buffer cache (automatic pin/unpin)
   - Fallback to disk if cache miss
   
2. **Write Operations**:
   - Write to buffer cache (marked dirty)
   - Buffer Manager handles flush coordination

3. **Benefits**:
   - Reduced disk I/O
   - Better performance
   - Automatic cache management

### 6.2 Fallback Strategy

When `bufferManager` is not available:

1. Direct disk I/O for all operations
2. No caching overhead
3. Simpler code path

## 7. Invariants (TLA+ Verification)

### 7.1 Data Integrity Invariant

```tla
Inv_DataIntegrity ==
    \A rid \in DOMAIN records:
        records[rid].pageId # nil =>
            records[rid].pageId \in DOMAIN pages
```

**Swift Implementation**:
```swift
public func checkDataIntegrityInvariant() -> Bool {
    for (_, record) in records where !record.isDeleted {
        if let pageId = record.pageId {
            guard pages[pageId] != nil else {
                return false
            }
        }
    }
    for (pageId, page) in pages {
        guard page.header.pageID == pageId else {
            return false
        }
    }
    return true
}
```

### 7.2 Space Management Invariant

```tla
Inv_SpaceManagement ==
    \A pid \in DOMAIN freeSpaceMap:
        pid \in DOMAIN pages /\
        freeSpaceMap[pid] <= PAGE_SIZE
```

**Swift Implementation**:
```swift
public func checkSpaceManagementInvariant() -> Bool {
    for (pageId, freeSpace) in freeSpaceMap {
        guard let page = pages[pageId] else {
            return false
        }
        let pageSize = UInt64(page.data.count)
        guard freeSpace <= pageSize else {
            return false
        }
    }
    return true
}
```

### 7.3 Performance Metrics Invariant

```tla
Inv_PerformanceMetrics ==
    metrics.totalPages >= 0 /\
    metrics.usedPages + metrics.freePages = metrics.totalPages
```

**Swift Implementation**:
```swift
public func checkPerformanceMetricsInvariant() -> Bool {
    guard metrics.totalPages >= 0,
          metrics.usedPages >= 0,
          metrics.freePages >= 0,
          metrics.totalRecords >= 0,
          metrics.ioOperations >= 0,
          metrics.averageLatency >= 0.0 else {
        return false
    }
    guard metrics.usedPages + metrics.freePages == metrics.totalPages else {
        return false
    }
    return true
}
```

## 8. Performance Characteristics

### 8.1 Latency Tracking

Exponential moving average for latency:
```swift
alpha = 0.1
averageLatency = alpha * latency + (1 - alpha) * averageLatency
```

**Target**: < 5ms average latency for cached operations

### 8.2 I/O Operations

Tracked per operation:
- Read operations
- Write operations
- Total I/O operations

## 9. Error Handling

### 9.1 Error Types

```swift
public enum StorageError: Error {
    case pageNotFound
    case recordNotFound
    case insufficientSpace
    case allocationFailed
    case deallocationFailed
    case readFailed
    case writeFailed
    case updateFailed
    case deleteFailed
}
```

### 9.2 Error Recovery

- **Page Not Found**: Return error, caller handles
- **Insufficient Space**: Try another area or fail
- **I/O Failed**: Retry or propagate error

## 10. Apple-First Optimizations

### 10.1 APFS Integration

- **Clones**: Efficient page allocation (future)
- **Compression**: Transparent compression
- **Snapshots**: Point-in-time backups

### 10.2 File System Operations

- **FileHandle**: Native Swift file operations
- **Async I/O**: Non-blocking operations
- **Memory-Mapped Files**: Future optimization

### 10.3 Performance

- **GCD**: Efficient task scheduling
- **Value Types**: Stack allocation
- **ARC**: Automatic memory management

## 11. Testing

### 11.1 Unit Tests

- Page allocation/deallocation
- Record operations
- Space management
- Buffer Manager integration
- Invariant verification

### 11.2 Integration Tests

- Storage + Buffer Manager
- Storage + WAL coordination
- Concurrent access
- Error scenarios

### 11.3 Performance Tests

- Latency measurements
- Throughput benchmarks
- Cache effectiveness
- I/O operation counts

## 12. References

- **RFC 0004**: Buffer Manager
- **RFC 0005**: Write-Ahead Logging
- **TLA+ Spec**: `spec/Storage.tla`

---

**Next**: See RFC 0019 for Transaction Manager details.

