# RFC 0004: Buffer Manager

**Status**: Standards Track  
**Author**: ColibrìDB Team  
**Date**: 2025-11-18  
**TLA+ Spec**: `spec/BufferPool.tla`

## Abstract

This RFC defines the Buffer Manager component, responsible for managing page caching, eviction policies, and coordination with the Write-Ahead Log (WAL) to ensure data durability and performance.

## 1. Introduction

The Buffer Manager is a critical component that caches database pages in memory to reduce disk I/O and improve performance. It implements multiple eviction policies (LRU, Clock, FIFO, Random) and maintains consistency with the WAL through the WAL-before-data property.

## 2. Design Principles

### 2.1 Apple-First Architecture

- **Swift Actor**: Thread-safe implementation using Swift actors
- **Async/Await**: Non-blocking I/O operations
- **Value Types**: Efficient data structures using Swift value types
- **ARC**: Automatic memory management

### 2.2 Key Properties

1. **Pin Count Correctness**: Pin counts accurately track page usage
2. **Dirty Page Consistency**: Dirty pages correctly tracked
3. **Eviction Policy Correctness**: Eviction policies correctly applied
4. **WAL Before Data**: Dirty pages only flushed after WAL flush

## 3. Architecture

### 3.1 Component Overview

```
BufferManager (Swift Actor)
├── Buffer Pool: [FrameIndex -> BufferPage]
├── Page Table: [PageID -> FrameIndex]
├── Pin Counts: [PageID -> Int]
├── Dirty Pages: Set<PageID>
├── LRU List: [PageID]
├── Clock Hand: Int
└── Metrics: BufferMetrics
```

### 3.2 Dependencies

- **DiskManager**: Reads and writes pages to disk
- **WAL**: Coordinates flushedLSN for WAL-before-data property

## 4. State Variables (TLA+ Mapping)

### 4.1 Core State

| Swift Variable | TLA+ Variable | Type | Description |
|----------------|---------------|------|-------------|
| `bufferPool` | `bufferPool` | `[FrameIndex -> Page]` | Pages cached in memory |
| `pageTable` | `pageTable` | `[PageID -> FrameIndex]` | Maps page IDs to frames |
| `pinCounts` | `pinCounts` | `[PageID -> Nat]` | Pin count per page |
| `dirtyPages` | `dirtyPages` | `Set(PageID)` | Set of dirty pages |
| `flushedLSN` | `flushedLSN` | `LSN` | Highest LSN flushed to disk |

### 4.2 Eviction State

| Swift Variable | TLA+ Variable | Type | Description |
|----------------|---------------|------|-------------|
| `lruList` | `lruOrder` | `Seq(PageID)` | LRU order (MRU at end) |
| `fifoList` | `fifoOrder` | `Seq(PageID)` | FIFO order |
| `referenceBits` | `referenceBit` | `[PageID -> BOOLEAN]` | Clock algorithm reference bits |
| `clockHand` | `clockHand` | `Nat` | Clock hand position |

### 4.3 Metrics

| Swift Variable | Type | Description |
|----------------|------|-------------|
| `metrics` | `BufferMetrics` | Performance metrics (hit rate, latency, etc.) |

## 5. API Specification

### 5.1 Initialization

```swift
public actor BufferManager {
    public init(
        diskManager: DiskManager,
        poolSize: Int? = nil,
        evictionPolicy: EvictionPolicy = .lru
    )
}
```

**Parameters**:
- `diskManager`: Disk manager for I/O operations
- `poolSize`: Maximum number of frames (default: 1000)
- `evictionPolicy`: Eviction policy (LRU, Clock, FIFO, Random)

### 5.2 Core Operations

#### 5.2.1 Get Page

```swift
public func getPage(pageId: PageID) async throws -> BufferPage
```

**TLA+ Action**: `GetPage(pageId)`

**Behavior**:
1. Check if page is in buffer (cache hit)
2. If hit: increment pin count, update LRU, set reference bit, return page
3. If miss: allocate frame, read from disk, pin page, update metrics, return page

**Preconditions**:
- `pageId` is valid

**Postconditions**:
- Page is in buffer and pinned
- Pin count > 0
- Metrics updated

**Errors**:
- `BufferError.frameAllocationFailed`: Cannot allocate frame
- `BufferError.evictionFailed`: Eviction failed

#### 5.2.2 Put Page

```swift
public func putPage(
    pageId: PageID,
    page: BufferPage,
    isDirty: Bool
) async throws
```

**TLA+ Action**: `PutPage(pageId, page, isDirty)`

**Behavior**:
1. Check if page is pinned
2. Update buffer pool entry
3. Mark page as dirty if `isDirty` is true
4. Update LRU order (move to MRU)

**Preconditions**:
- Page is in buffer
- Page is pinned (`pinCount[pageId] > 0`)

**Postconditions**:
- Page updated in buffer
- Page marked dirty if `isDirty`
- LRU order updated

**Errors**:
- `BufferError.pageNotPinned`: Page not pinned
- `BufferError.pageNotFound`: Page not in buffer

#### 5.2.3 Unpin Page

```swift
public func unpinPage(pageId: PageID) async throws
```

**TLA+ Action**: `UnpinPage(pageId)`

**Behavior**:
1. Decrement pin count
2. If pin count reaches 0, page is unpinned

**Preconditions**:
- Page is in buffer
- Page is pinned

**Postconditions**:
- Pin count decremented
- Page unpinned if count reaches 0

**Errors**:
- `BufferError.pageNotPinned`: Page not pinned
- `BufferError.pageNotFound`: Page not in buffer

#### 5.2.4 Flush Page

```swift
public func flushPage(pageId: PageID) async throws
```

**TLA+ Action**: `FlushPage(pageId)`

**Behavior**:
1. Check if page is dirty
2. Verify WAL-before-data: `page.lsn <= flushedLSN`
3. Write page to disk
4. Mark page as clean

**Preconditions**:
- Page is in buffer
- Page is dirty
- `page.lsn <= flushedLSN` (WAL-before-data)

**Postconditions**:
- Page written to disk
- Page marked clean
- `dirtyPages` updated

**Errors**:
- `BufferError.pageNotFound`: Page not in buffer
- `BufferError.flushFailed`: Flush failed

#### 5.2.5 Flush All

```swift
public func flushAll() async throws
```

**TLA+ Action**: `FlushAll()`

**Behavior**:
1. Copy `dirtyPages` set (avoid concurrent modification)
2. Flush each dirty page
3. All dirty pages written to disk

**Postconditions**:
- All dirty pages flushed
- All pages clean
- `dirtyPages` empty

**Errors**:
- `BufferError.flushFailed`: One or more flushes failed

### 5.3 Eviction Operations

#### 5.3.1 Allocate Frame

```swift
private func allocateFrame() async throws -> FrameIndex
```

**TLA+ Action**: `AllocateFrame()`

**Behavior**:
1. Check for free frame from eviction
2. If pool full, evict page
3. If pool not full, allocate new frame
4. Return frame index

**Postconditions**:
- Frame allocated
- Frame available for page

**Errors**:
- `BufferError.frameAllocationFailed`: Cannot allocate frame
- `BufferError.noPageToEvict`: All pages pinned

#### 5.3.2 Evict Page

```swift
private func evictPage() async throws -> FrameIndex
```

**TLA+ Action**: `EvictPage()`

**Behavior**:
1. Apply eviction policy to find candidate
2. Check if candidate is pinned
3. If dirty, flush page (with WAL check)
4. Remove page from buffer
5. Return frame index

**Eviction Policies**:
- **LRU**: Evict least recently used unpinned page
- **Clock**: Evict first unpinned page with reference bit = 0
- **FIFO**: Evict first-in unpinned page
- **Random**: Evict random unpinned page

**Preconditions**:
- At least one unpinned page exists

**Postconditions**:
- Page evicted
- Frame available

**Errors**:
- `BufferError.noPageToEvict`: All pages pinned
- `BufferError.pagePinned`: Candidate is pinned
- `BufferError.evictionFailed`: Eviction failed

### 5.4 WAL Coordination

#### 5.4.1 Update Flushed LSN

```swift
public func updateFlushedLSN(_ lsn: LSN) async
```

**TLA+ Action**: `UpdateFlushedLSN(lsn)`

**Behavior**:
1. Update `flushedLSN` if new LSN is higher
2. Enables WAL-before-data property

**Preconditions**:
- `lsn >= flushedLSN` (monotonic increase)

**Postconditions**:
- `flushedLSN` updated
- WAL-before-data maintained

#### 5.4.2 Get Flushed LSN

```swift
public func getFlushedLSN() -> LSN
```

**Returns**: Current `flushedLSN` value

### 5.5 Query Operations

#### 5.5.1 Is Page In Cache

```swift
public func isPageInCache(pageId: PageID) -> Bool
```

**Returns**: True if page is in buffer (without pinning)

#### 5.5.2 Get Page Query

```swift
public func getPageQuery(pageId: PageID) -> BufferPage?
```

**Returns**: Page if in cache, nil otherwise (non-pinning query)

### 5.6 Metrics

#### 5.6.1 Get Buffer Metrics

```swift
public func getBufferMetrics() -> BufferMetrics
```

**Returns**: Performance metrics

**Metrics**:
- `totalFrames`: Total buffer pool size
- `usedFrames`: Frames in use
- `freeFrames`: Free frames
- `dirtyFrames`: Dirty pages
- `pinnedFrames`: Pinned pages
- `hitRate`: Cache hit rate (0.0-1.0)
- `missRate`: Cache miss rate (0.0-1.0)
- `evictionCount`: Total evictions
- `averageLatency`: Average operation latency (ms)

## 6. Eviction Policies

### 6.1 LRU (Least Recently Used)

**Algorithm**:
1. Maintain ordered list of pages (MRU at end)
2. On access, move page to end (MRU)
3. On eviction, remove from front (LRU)

**Complexity**:
- Access: O(n) to move in list
- Eviction: O(1) to find LRU

**Use Case**: General-purpose workloads

### 6.2 Clock (Second-Chance)

**Algorithm**:
1. Maintain circular list with reference bits
2. On access, set reference bit to 1
3. On eviction, sweep clock hand:
   - If reference bit = 1: set to 0, move to next
   - If reference bit = 0: evict this page

**Complexity**:
- Access: O(1)
- Eviction: O(n) worst case (scan entire pool)

**Use Case**: Mixed read/write workloads

### 6.3 FIFO (First-In, First-Out)

**Algorithm**:
1. Maintain queue of pages in order added
2. On eviction, remove from front

**Complexity**:
- Access: O(1)
- Eviction: O(1)

**Use Case**: Sequential workloads

### 6.4 Random

**Algorithm**:
1. Select random unpinned page
2. Evict if not pinned

**Complexity**:
- Access: O(1)
- Eviction: O(n) to find random unpinned page

**Use Case**: Testing, uniform access patterns

## 7. Invariants (TLA+ Verification)

### 7.1 Pin Count Invariant

```tla
Inv_PinCount ==
    \A pid \in DOMAIN bufferPool:
        pinCounts[pid] > 0 <=> pageTable[pid] \in DOMAIN bufferPool
```

**Swift Implementation**:
```swift
public func checkPinCountInvariant() -> Bool {
    for (pageId, frameIndex) in pageTable {
        let page = bufferPool[frameIndex]!
        let pinCount = pinCounts[pageId] ?? 0
        guard pinCount > 0 else { return false }
    }
    return true
}
```

### 7.2 Dirty Page Consistency Invariant

```tla
Inv_DirtyPageConsistency ==
    \A pid \in dirtyPages:
        pid \in DOMAIN pageTable /\
        bufferPool[pageTable[pid]].isDirty = TRUE
```

**Swift Implementation**:
```swift
public func checkDirtyPageConsistencyInvariant() -> Bool {
    for pageId in dirtyPages {
        guard let frameIndex = pageTable[pageId],
              let page = bufferPool[frameIndex],
              page.isDirty else {
            return false
        }
    }
    return true
}
```

### 7.3 WAL Before Data Invariant

```tla
Inv_WALBeforeData ==
    \A pid \in dirtyPages:
        bufferPool[pageTable[pid]].lsn <= flushedLSN + 1
```

**Swift Implementation**:
```swift
public func checkWALBeforeDataInvariant() -> Bool {
    for pageId in dirtyPages {
        if let frameIndex = pageTable[pageId],
           let page = bufferPool[frameIndex] {
            if page.lsn > flushedLSN + 1 {
                return false
            }
        }
    }
    return true
}
```

### 7.4 No Duplicate Pages Invariant

```tla
Inv_NoDuplicatePages ==
    \A pid1, pid2 \in DOMAIN pageTable:
        pid1 # pid2 => pageTable[pid1] # pageTable[pid2]
```

**Swift Implementation**:
```swift
// Verified by data structure (Set-based pageTable)
```

### 7.5 Pool Size Invariant

```tla
Inv_PoolSize ==
    Len(bufferPool) <= poolSize
```

**Swift Implementation**:
```swift
public func checkPoolSizeInvariant() -> Bool {
    return bufferPool.count <= poolSize
}
```

## 8. Performance Characteristics

### 8.1 Cache Hit Rate

Target: > 95% hit rate for typical workloads

**Metrics**:
- `hitRate = hitCount / (hitCount + missCount)`
- Updated on each access

### 8.2 Latency

Target: < 1ms average latency for cache hits

**Metrics**:
- Exponential moving average: `avgLatency = alpha * latency + (1 - alpha) * avgLatency`
- Alpha = 0.1 (smoothing factor)

### 8.3 Eviction Rate

Tracked: Total evictions for monitoring

## 9. Error Handling

### 9.1 Error Types

```swift
public enum BufferError: Error {
    case pageNotFound
    case pageNotPinned
    case pagePinned
    case noPageToEvict
    case frameAllocationFailed
    case evictionFailed
    case flushFailed
}
```

### 9.2 Error Recovery

- **Page Not Found**: Return error, caller handles
- **Page Pinned**: Cannot evict, try another page
- **No Page To Evict**: All pages pinned, return error
- **Flush Failed**: Retry or abort operation

## 10. Testing

### 10.1 Unit Tests

- Cache hit/miss scenarios
- Eviction policy correctness
- Pin/unpin operations
- Dirty page tracking
- WAL coordination
- Invariant verification

### 10.2 Integration Tests

- Buffer + WAL coordination
- Buffer + Storage Manager integration
- Recovery scenarios
- Concurrent access

### 10.3 Performance Tests

- Hit rate under various workloads
- Latency measurements
- Eviction policy comparison
- Throughput benchmarks

## 11. Apple-First Optimizations

### 11.1 Swift Actor Performance

- Zero-cost message passing
- Compile-time safety
- Efficient actor isolation

### 11.2 Memory Management

- ARC for automatic cleanup
- Value types for stack allocation
- Buffer pool limits memory usage

### 11.3 Async I/O

- Non-blocking disk operations
- Structured concurrency
- Efficient task scheduling

## 12. References

- **RFC 0005**: Write-Ahead Logging (WAL)
- **RFC 0006**: Storage Manager
- **TLA+ Spec**: `spec/BufferPool.tla`
- **Gray & Putzolu, 1987**: "The Five-Minute Rule"
- **Corbató, 1968**: Clock Algorithm (Second-Chance)

---

**Next**: See RFC 0005 for Write-Ahead Logging details.

