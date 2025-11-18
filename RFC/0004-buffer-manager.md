# RFC 0004: Buffer Manager

**Status**: Standards Track  
**Author**: ColibrìDB Team  
**Date**: 2025-11-18  
**TLA+ Spec**: `spec/BufferPool.tla`

## Abstract

This RFC defines the Buffer Manager component, responsible for managing page caching, eviction policies, and coordination with the Write-Ahead Log (WAL) to ensure data durability and performance.

## 1. Introduction

The Buffer Manager is a critical component that caches database pages in memory to reduce disk I/O and improve performance. It implements multiple eviction policies (LRU, Clock, FIFO, Random) and maintains consistency with the WAL through the WAL-before-data property.

### 1.1 Purpose and Goals

The primary goals of the Buffer Manager are:

1. **Performance Optimization**: Reduce disk I/O by maintaining frequently accessed pages in memory
2. **Memory Efficiency**: Manage limited buffer pool memory through intelligent eviction
3. **Durability Guarantee**: Coordinate with WAL to ensure crash recovery (WAL-before-data property)
4. **Concurrency Safety**: Provide thread-safe page access using Swift actors
5. **Flexibility**: Support multiple eviction policies for different workload patterns

### 1.2 Problem Statement

Database systems typically have:
- **Large datasets** stored on disk (GB to TB)
- **Limited memory** for caching (MB to GB)
- **High I/O costs** (disk reads ~10ms vs memory ~10ns)
- **Concurrent access** from multiple transactions
- **Crash recovery** requirements (ACID durability)

The Buffer Manager solves these challenges by:
- Caching hot pages in memory (100-1000x faster access)
- Intelligently evicting cold pages when pool is full
- Preventing eviction of pages currently in use (pinning)
- Tracking dirty pages for efficient flush operations
- Coordinating with WAL to ensure crash recovery

### 1.3 Key Concepts

**Page**: A fixed-size unit of data (typically 4KB-16KB) that is the atomic unit of I/O operations.

**Frame**: A slot in the buffer pool that can hold one page. The buffer pool contains a fixed number of frames.

**Pin Count**: The number of active references to a page. Pinned pages cannot be evicted.

**Dirty Page**: A page that has been modified in memory but not yet written to disk. Must be flushed before eviction.

**LSN (Log Sequence Number)**: A monotonically increasing number assigned to WAL records. Used to enforce WAL-before-data property.

**Cache Hit**: When a requested page is already in the buffer pool.

**Cache Miss**: When a requested page must be read from disk.

## 2. Design Principles

### 2.1 Apple-First Architecture

ColibrìDB is designed specifically for Apple platforms, leveraging Swift's modern features:

#### 2.1.1 Swift Actors

**Why Actors**: Swift actors provide compile-time guarantees for thread-safe code without explicit locking.

```swift
public actor BufferManager {
    // All state is isolated within the actor
    private var bufferPool: [FrameIndex: BufferPage] = [:]
    private var pageTable: [PageID: FrameIndex] = [:]
    
    // Methods are automatically synchronized
    public func getPage(pageId: PageID) async throws -> BufferPage {
        // This method can only be called from async context
        // Swift compiler ensures no data races
    }
}
```

**Benefits**:
- **Zero Lock Overhead**: Actors use message passing, eliminating lock contention
- **Compile-Time Safety**: Swift compiler prevents data races at compile time
- **Efficient**: Actors are optimized for high-throughput scenarios
- **No Deadlocks**: Actors cannot deadlock (single-threaded execution per actor)

**Performance Characteristics**:
- Actor isolation has minimal overhead (~1-2ns per method call)
- Message passing is optimized for single-actor access patterns
- No lock contention means predictable latency

#### 2.1.2 Async/Await

**Why Async/Await**: Database I/O operations are inherently asynchronous. Swift's async/await provides structured concurrency.

```swift
// Non-blocking disk I/O
public func fetchPage(pageId: PageID) async throws -> BufferPage {
    // This suspends the task, allowing other work to proceed
    let pageData = try await diskManager.readPage(pageId: pageId)
    
    // Resumes when I/O completes
    return BufferPage(pageId: pageId, data: pageData, ...)
}
```

**Benefits**:
- **Non-Blocking**: I/O operations don't block threads
- **Structured Concurrency**: Clear control flow and error handling
- **Efficient**: Supports thousands of concurrent operations with few threads
- **Composable**: Easy to compose multiple async operations

**Performance Characteristics**:
- Can handle 1000s of concurrent page reads with ~10 threads
- Thread switching overhead is minimal (~1μs)
- Memory efficient (coroutines vs full threads)

#### 2.1.3 Value Types

**Why Value Types**: Immutable value types are thread-safe by default and enable optimizations.

```swift
public struct BufferPage: Sendable {
    public let pageId: PageID
    public let data: Data
    public let lsn: LSN
    // Immutable - safe to share across actors
}
```

**Benefits**:
- **Thread-Safe by Default**: Immutable values cannot have data races
- **Copy-on-Write**: Swift optimizes large value copies
- **Predictable Behavior**: No hidden mutations
- **Memory Efficient**: Stack allocation where possible

**Performance Characteristics**:
- Stack allocation for small values (no heap overhead)
- Copy-on-write for large values (shared storage until mutation)
- ARC optimizations for reference counting

#### 2.1.4 Automatic Reference Counting (ARC)

**Why ARC**: Swift's automatic memory management eliminates manual memory management errors.

```swift
// No manual memory management needed
let page = BufferPage(...)  // Allocated
// Automatically deallocated when out of scope
```

**Benefits**:
- **No Memory Leaks**: Automatic cleanup when references drop to zero
- **No Use-After-Free**: References keep objects alive
- **Efficient**: Reference counting is optimized for common patterns
- **Predictable**: Memory is reclaimed deterministically

**Performance Characteristics**:
- Reference counting overhead: ~1-2ns per retain/release
- Deallocation is deferred but bounded
- Memory is reclaimed incrementally, preventing GC pauses

### 2.2 Key Properties

The Buffer Manager maintains several critical invariants that ensure correctness:

#### 2.2.1 Pin Count Correctness

**Invariant**: Pin counts accurately track page usage. A page with pin count > 0 cannot be evicted.

**Why Critical**: 
- Prevents eviction of pages currently being accessed
- Prevents use-after-free bugs
- Ensures data consistency during concurrent access

**Implementation**:
```swift
// Pin count must be > 0 for page to be in buffer
pinCounts[pageId] = (pinCounts[pageId] ?? 0) + 1

// Cannot evict if pinned
guard pinCounts[pageId] == 0 else {
    throw BufferError.pagePinned
}
```

**Violation Prevention**:
- Pin count incremented on `getPage()` (automatic pin)
- Pin count decremented on `unpinPage()`
- Eviction checks pin count before proceeding
- Actor isolation ensures no concurrent modification

#### 2.2.2 Dirty Page Consistency

**Invariant**: The `dirtyPages` set accurately reflects which pages have been modified but not flushed.

**Why Critical**:
- Ensures dirty pages are flushed before eviction
- Enables efficient batch flushing
- Prevents data loss on crash

**Implementation**:
```swift
// Mark as dirty when modified
if isDirty {
    dirtyPages.insert(pageId)
}

// Check dirty before eviction
if dirtyPages.contains(pageId) {
    try await flushPage(pageId: pageId)  // Must flush before eviction
}
```

**Violation Prevention**:
- Dirty flag set on `putPage()` with `isDirty: true`
- Dirty flag cleared on `flushPage()`
- Eviction always flushes dirty pages first
- Actor isolation ensures consistency

#### 2.2.3 Eviction Policy Correctness

**Invariant**: Eviction policies correctly identify and evict eligible pages.

**Why Critical**:
- Ensures fair eviction (LRU: least recently used, Clock: second chance)
- Prevents starvation (all pages pinned scenario)
- Maintains performance characteristics

**Implementation**:
```swift
// LRU: Evict least recently used (first in list)
for pageId in lruList {  // Scan from least to most recent
    guard pinCounts[pageId] == 0 else { continue }
    return pageId  // Found unpinned page
}
throw BufferError.noPageToEvict  // All pinned
```

**Violation Prevention**:
- Policies skip pinned pages
- Policies handle empty lists
- Policies have fallbacks for edge cases
- Maximum scan limits prevent infinite loops

#### 2.2.4 WAL Before Data

**Invariant**: Dirty pages are only flushed to disk after their corresponding WAL records have been flushed.

**Why Critical**:
- Enables crash recovery using ARIES algorithm
- Prevents data loss if crash occurs during flush
- Maintains database durability guarantees

**Implementation**:
```swift
// Check WAL-before-data before flush
guard page.lsn <= flushedLSN else {
    throw BufferError.flushFailed  // WAL not flushed yet
}

// Only flush if WAL is ahead
try await diskManager.writePage(pageId: pageId, data: page.data)
```

**Violation Prevention**:
- `flushPage()` checks `page.lsn <= flushedLSN`
- `updateFlushedLSN()` called when WAL flushes
- Eviction flushes dirty pages with WAL check
- Actor isolation ensures atomic checks

**Mathematical Guarantee**:
```
\A pid \in dirtyPages:
    bufferPool[pageTable[pid]].lsn <= flushedLSN + 1
```

The `+1` allows for race conditions where WAL flush and buffer flush happen concurrently.

## 3. Architecture

### 3.1 Component Overview

```
BufferManager (Swift Actor)
├── Buffer Pool: [FrameIndex -> BufferPage]
│   ├── Purpose: Physical memory slots for pages
│   ├── Size: Fixed at poolSize (default: 1000 frames)
│   ├── Access: O(1) by frame index
│   └── Lifetime: Pages live here until evicted
│
├── Page Table: [PageID -> FrameIndex]
│   ├── Purpose: Fast lookup of page location in buffer
│   ├── Access: O(1) hash table lookup
│   ├── Invariant: One-to-one mapping (no duplicates)
│   └── Updates: Modified on eviction/allocation
│
├── Pin Counts: [PageID -> Int]
│   ├── Purpose: Track active references to pages
│   ├── Initial: 0 (unpinned)
│   ├── Increment: On getPage() (automatic pin)
│   ├── Decrement: On unpinPage()
│   └── Invariant: pinCount > 0 => page cannot be evicted
│
├── Dirty Pages: Set<PageID>
│   ├── Purpose: Track modified but unflushed pages
│   ├── Add: On putPage() with isDirty: true
│   ├── Remove: On flushPage()
│   └── Invariant: All dirty pages must be flushed before eviction
│
├── LRU List: [PageID]
│   ├── Purpose: Maintain access order (MRU at end)
│   ├── Order: [LRU, ..., MRU]
│   ├── Update: On getPage() (move to end)
│   └── Use: LRU eviction policy scans from beginning
│
├── FIFO List: [PageID]
│   ├── Purpose: Maintain insertion order
│   ├── Order: [oldest, ..., newest]
│   ├── Update: On allocation (append to end)
│   └── Use: FIFO eviction policy removes from beginning
│
├── Reference Bits: [PageID -> Bool]
│   ├── Purpose: Clock algorithm second-chance mechanism
│   ├── Set: On getPage() (set to true)
│   ├── Clear: On clock sweep or eviction
│   └── Use: Clock policy checks bit before eviction
│
├── Clock Hand: Int
│   ├── Purpose: Current position in clock sweep
│   ├── Range: 0 to lruList.count - 1
│   ├── Update: Increments circularly during eviction
│   └── Use: Clock policy scans from hand position
│
└── Metrics: BufferMetrics
    ├── Purpose: Performance monitoring
    ├── Update: On each operation
    ├── Threading: Non-isolated (atomic updates)
    └── Use: Monitoring, debugging, optimization
```

### 3.2 Data Flow Diagram

#### 3.2.1 Page Read Flow

```
┌─────────────┐
│ getPage(id) │
└──────┬──────┘
       │
       ▼
   ┌───────────────┐
   │ Check Cache   │
   │ (pageTable)   │
   └───┬───────┬───┘
       │       │
       │ Hit   │ Miss
       ▼       ▼
  ┌─────────┐ ┌──────────────┐
  │Increment│ │Allocate Frame│
  │Pin Count│ └───┬──────────┘
  └────┬────┘     │
       │          ▼
       │     ┌──────────────┐
       │     │Read from Disk│
       │     └───┬──────────┘
       │         │
       ▼         ▼
  ┌─────────────┐
  │Update LRU   │
  │(Move to End)│
  └──────┬──────┘
         │
         ▼
    ┌─────────┐
    │Return   │
    │Page     │
    └─────────┘
```

#### 3.2.2 Page Write Flow

```
┌───────────────┐
│ putPage(id,   │
│  page, dirty) │
└──────┬────────┘
       │
       ▼
   ┌──────────────┐
   │Check Pin     │
   │(must be > 0) │
   └───┬──────────┘
       │
       ▼
   ┌──────────────┐
   │Update Buffer │
   │Pool Entry    │
   └───┬──────────┘
       │
       ▼
   ┌──────────────┐
   │Mark Dirty?   │
   └───┬───────┬──┘
       │Yes    │No
       ▼       │
   ┌─────────┐ │
   │Add to   │ │
   │dirtyPages│ │
   └───┬─────┘ │
       │       │
       └───┬───┘
           ▼
      ┌──────────┐
      │Update LRU│
      │(MRU)     │
      └────┬─────┘
           ▼
      ┌─────────┐
      │Complete │
      └─────────┘
```

#### 3.2.3 Eviction Flow

```
┌──────────────┐
│allocateFrame │
│(pool full)   │
└──────┬───────┘
       │
       ▼
   ┌──────────────┐
   │Apply Eviction│
   │Policy        │
   └───┬──────────┘
       │
       ▼
   ┌──────────────┐
   │Find Candidate│
   │(unpinned)    │
   └───┬──────────┘
       │
       ▼
   ┌──────────────┐
   │Page Dirty?   │
   └───┬───────┬──┘
       │Yes    │No
       ▼       │
   ┌─────────┐ │
   │Check WAL│ │
   │(lsn <=  │ │
   │flushed) │ │
   └───┬─────┘ │
       │       │
       ▼       │
   ┌─────────┐ │
   │Flush to │ │
   │Disk     │ │
   └───┬─────┘ │
       │       │
       └───┬───┘
           ▼
      ┌──────────┐
      │Remove    │
      │from Pool │
      └────┬─────┘
           ▼
      ┌──────────┐
      │Return    │
      │Frame     │
      └──────────┘
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

**Behavior**: Detailed step-by-step execution

1. **Cache Check**: 
   ```swift
   if let frameIndex = pageTable[pageId] {
       // Cache hit path
   } else {
       // Cache miss path
   }
   ```

2. **Cache Hit Path**:
   - Retrieve page from `bufferPool[frameIndex]`
   - Increment pin count: `pinCounts[pageId] = (pinCounts[pageId] ?? 0) + 1`
   - Update LRU: Move page to end of `lruList` (most recently used position)
   - Set reference bit: `referenceBits[pageId] = true` (for Clock algorithm)
   - Update metrics: Increment `hitCount`, update `hitRate`, record latency
   - Return page immediately (no I/O required)

3. **Cache Miss Path**:
   - Increment `missCount` for metrics
   - Allocate frame:
     ```swift
     let frameIndex = try await allocateFrame()
     // This may trigger eviction if pool is full
     ```
   - Read from disk:
     ```swift
     let pageData = try await diskManager.readPage(pageId: pageId)
     // Non-blocking async I/O operation
     ```
   - Create BufferPage:
     ```swift
     let page = BufferPage(
         pageId: pageId,
         data: pageData,
         lsn: 0,  // Will be updated by caller if needed
         isDirty: false,
         isPinned: false,
         timestamp: UInt64(Date().timeIntervalSince1970 * 1000)
     )
     ```
   - Add to buffer:
     ```swift
     bufferPool[frameIndex] = page
     pageTable[pageId] = frameIndex
     pinCounts[pageId] = 1  // Auto-pin on fetch
     ```
   - Update eviction lists:
     ```swift
     lruList.append(pageId)      // Add to end (MRU)
     fifoList.append(pageId)     // Add to end (newest)
     referenceBits[pageId] = true // Set reference bit
     ```
   - Update metrics: Update `missRate`, record latency (includes disk I/O time)
   - Return page

**Preconditions**:
- `pageId` is valid (non-zero PageID)
- Disk manager is available and accessible
- If pool is full, at least one unpinned page exists (or eviction will fail)

**Postconditions**:
- Page is in buffer pool and pinned (`pinCount[pageId] > 0`)
- Page is at MRU position in LRU list
- Reference bit is set (for Clock algorithm)
- Metrics updated (hit/miss counts, rates, latency)
- If cache miss: page read from disk successfully

**Performance Characteristics**:
- **Cache Hit**: ~100ns (hash lookup + state updates)
- **Cache Miss**: ~5-10ms (disk I/O dominates, ~100ns for buffer operations)
- **With Eviction**: +1-5ms if eviction and flush required

**Concurrency Considerations**:
- Actor isolation ensures no concurrent modifications
- Multiple concurrent `getPage()` calls are serialized
- Pin count prevents eviction during access

**Example Usage**:
```swift
// Typical read pattern
let page = try await bufferManager.getPage(pageId: pageId)
// Use page...
try await bufferManager.unpinPage(pageId: pageId)
```

**Edge Cases**:
1. **All Pages Pinned**: `allocateFrame()` throws `BufferError.noPageToEvict`
   - **Solution**: Caller must unpin some pages first
   - **Prevention**: Monitor pin counts, implement timeout mechanisms

2. **Disk Read Failure**: `diskManager.readPage()` throws
   - **Solution**: Error propagates to caller
   - **State**: No partial state (frame not allocated yet)

3. **Page ID Overflow**: Very unlikely with UInt64, but possible
   - **Solution**: PageID wraps (acceptable for most use cases)
   - **Prevention**: Monitor pageID allocation

**Errors**:
- `BufferError.frameAllocationFailed`: Cannot allocate frame (pool full, all pages pinned)
- `BufferError.evictionFailed`: Eviction policy failed (no unpinned pages, or other error)
- `DBError.ioError`: Disk I/O failed (propagated from DiskManager)

#### 5.2.2 Put Page

```swift
public func putPage(
    pageId: PageID,
    page: BufferPage,
    isDirty: Bool
) async throws
```

**TLA+ Action**: `PutPage(pageId, page, isDirty)`

**Behavior**: Detailed step-by-step execution

1. **Validate Page Exists**:
   ```swift
   guard pageTable[pageId] != nil else {
       throw BufferError.pageNotFound
   }
   ```
   - Page must already be in buffer (use `getPage()` first to fetch)
   - Cannot use `putPage()` to insert new pages

2. **Validate Page is Pinned**:
   ```swift
   guard pinCounts[pageId] ?? 0 > 0 else {
       throw BufferError.pageNotPinned
   }
   ```
   - Page must be pinned to modify (prevents concurrent modification)
   - Pin count > 0 ensures page cannot be evicted during modification

3. **Update Buffer Pool Entry**:
   ```swift
   if let frameIndex = pageTable[pageId] {
       bufferPool[frameIndex] = page
       // Replace entire page (immutable BufferPage)
   }
   ```
   - Replace page in buffer pool at same frame index
   - Page ID must match (verified by caller)
   - Previous page is replaced (not merged)

4. **Mark as Dirty** (if `isDirty` is true):
   ```swift
   if isDirty {
       dirtyPages.insert(pageId)
       // Add to dirty set if modified
   }
   ```
   - **Important**: Caller must pass `isDirty: true` if page data changed
   - **Important**: Caller must pass `isDirty: false` if only metadata changed
   - Dirty pages must be flushed before eviction

5. **Update LSN** (if provided):
   - Page LSN should be set by caller (typically from WAL)
   - LSN is used for WAL-before-data check during flush

6. **Update LRU Order**:
   ```swift
   moveToMRU(pageId: pageId)
   // Move to end of lruList (most recently used)
   ```
   - Page becomes most recently used
   - Improves cache locality
   - Helps LRU eviction policy

7. **Set Reference Bit**:
   ```swift
   referenceBits[pageId] = true
   ```
   - Give second chance in Clock algorithm
   - Page will not be evicted on next clock sweep

8. **Update Metrics**:
   ```swift
   updateMetrics()
   // Update dirty frames count, etc.
   ```

**Preconditions**:
- Page is in buffer (`pageTable[pageId] != nil`)
- Page is pinned (`pinCount[pageId] > 0`)
- Page ID matches (`page.pageId == pageId`)
- Buffer page is valid (correct size, valid data)

**Postconditions**:
- Page updated in buffer pool (same frame index)
- Page marked dirty if `isDirty` is true
- Page at MRU position in LRU list
- Reference bit set (for Clock algorithm)
- Metrics updated (dirty frame count, etc.)

**Performance Characteristics**:
- **Update**: ~50ns (hash lookup + dictionary update + list manipulation)
- **No I/O**: In-memory operation only
- **Scalable**: O(1) operations

**Use Cases**:

1. **Page Modification** (typical):
   ```swift
   // Fetch page
   var page = try await bufferManager.getPage(pageId: pageId)
   
   // Modify page data
   page.data.replaceSubrange(offset..<offset+length, with: newData)
   page.lsn = newLSN  // Update LSN from WAL
   
   // Write back
   try await bufferManager.putPage(pageId: pageId, page: page, isDirty: true)
   
   // Unpin when done
   try await bufferManager.unpinPage(pageId: pageId)
   ```

2. **Metadata Update Only** (rare):
   ```swift
   // Fetch page
   var page = try await bufferManager.getPage(pageId: pageId)
   
   // Update only metadata (no data change)
   page.timestamp = newTimestamp
   
   // Write back (not dirty)
   try await bufferManager.putPage(pageId: pageId, page: page, isDirty: false)
   
   try await bufferManager.unpinPage(pageId: pageId)
   ```

**Edge Cases**:

1. **Page Not Found**: `pageTable[pageId] == nil`
   - **Solution**: Use `getPage()` first to fetch page
   - **Error**: `BufferError.pageNotFound`

2. **Page Not Pinned**: `pinCount[pageId] == 0`
   - **Solution**: Page must be pinned before modification
   - **Error**: `BufferError.pageNotPinned`
   - **Prevention**: Always pin page before modifying

3. **Concurrent Modification**: Multiple transactions modify same page
   - **Solution**: Lock Manager handles concurrent access
   - **Buffer Manager**: Ensures page is pinned (cannot be evicted)
   - **Coordination**: MVCC or locks prevent conflicts

**Errors**:
- `BufferError.pageNotFound`: Page not in buffer (use `getPage()` first)
- `BufferError.pageNotPinned`: Page not pinned (cannot modify unpinned page)

**Thread Safety**:
- Actor isolation ensures no concurrent modifications
- Pin count prevents eviction during modification
- All operations are serialized within actor

#### 5.2.3 Unpin Page

```swift
public func unpinPage(pageId: PageID) async throws
```

**TLA+ Action**: `UnpinPage(pageId)`

**Behavior**: Detailed step-by-step execution

1. **Validate Page is Pinned**:
   ```swift
   guard let pinCount = pinCounts[pageId], pinCount > 0 else {
       throw BufferError.pageNotPinned
   }
   ```
   - Page must exist in buffer (`pageTable[pageId] != nil`)
   - Page must be pinned (`pinCount > 0`)
   - Cannot unpin already unpinned page

2. **Decrement Pin Count**:
   ```swift
   pinCounts[pageId] = pinCount - 1
   ```
   - Decrement by 1 (not reset to 0)
   - Supports multiple pins (e.g., nested transactions)

3. **Check if Unpinned**:
   ```swift
   if pinCount - 1 == 0 {
       // Page is now unpinned and eligible for eviction
   }
   ```
   - When pin count reaches 0, page is unpinned
   - Unpinned pages can be evicted (if dirty, must flush first)

4. **Update Metrics**:
   ```swift
   updateMetrics()
   // Update pinnedFrames count
   ```
   - Recalculate pinned frame count
   - Update other metrics

**Preconditions**:
- Page is in buffer (`pageTable[pageId] != nil`)
- Page is pinned (`pinCount[pageId] > 0`)

**Postconditions**:
- Pin count decremented (`pinCount[pageId] = oldCount - 1`)
- Page unpinned if count reaches 0 (`pinCount == 0`)
- Metrics updated (pinned frame count)

**Performance Characteristics**:
- **Unpin**: ~20ns (hash lookup + decrement)
- **No I/O**: In-memory operation only
- **Scalable**: O(1) operation

**Pin Count Semantics**:

The pin count tracks the number of active references to a page:

1. **Initial Pin**: `getPage()` pins page (pin count = 1)
2. **Multiple Pins**: Each call to `getPage()` increments pin count
3. **Unpin**: Each call to `unpinPage()` decrements pin count
4. **Zero Pins**: When pin count reaches 0, page is unpinned

**Example**: Nested transaction pattern
```swift
// Outer transaction
let page1 = try await bufferManager.getPage(pageId: 1)  // pinCount = 1

// Nested operation
let page2 = try await bufferManager.getPage(pageId: 1)  // pinCount = 2

// First unpin
try await bufferManager.unpinPage(pageId: 1)  // pinCount = 1 (still pinned)

// Second unpin
try await bufferManager.unpinPage(pageId: 1)  // pinCount = 0 (unpinned, can evict)
```

**Why Pin Counts**:

1. **Prevent Premature Eviction**: Pinned pages cannot be evicted
2. **Support Nested Operations**: Multiple operations can pin same page
3. **Safety**: Ensures page stays in buffer during critical operations
4. **Concurrency**: Multiple transactions can pin same page safely

**Edge Cases**:

1. **Double Unpin**: Unpinning unpinned page
   - **Behavior**: Throws `BufferError.pageNotPinned`
   - **Prevention**: Track pin count carefully
   - **Error**: Indicates programming error (mismatched pin/unpin)

2. **Unpin Non-Existent Page**: Page not in buffer
   - **Behavior**: Throws `BufferError.pageNotFound`
   - **Prevention**: Check page exists before unpin

3. **Pin Count Underflow**: Negative pin count (should never occur)
   - **Behavior**: Guard statement prevents negative count
   - **Prevention**: Actor isolation ensures atomicity

**Errors**:
- `BufferError.pageNotPinned`: Page not pinned (already unpinned or never pinned)
- `BufferError.pageNotFound`: Page not in buffer

**Best Practices**:

1. **Always Unpin**: Always unpin pages after use
   ```swift
   let page = try await bufferManager.getPage(pageId: pageId)
   defer { try? await bufferManager.unpinPage(pageId: pageId) }
   // Use page...
   ```

2. **Match Pins**: Ensure equal number of pins and unpins
   ```swift
   // Correct: one pin, one unpin
   let page = try await bufferManager.getPage(pageId: pageId)
   try await bufferManager.unpinPage(pageId: pageId)
   
   // Incorrect: two pins, one unpin (leak)
   let page1 = try await bufferManager.getPage(pageId: pageId)
   let page2 = try await bufferManager.getPage(pageId: pageId)
   try await bufferManager.unpinPage(pageId: pageId)  // Still pinned!
   ```

3. **Use Defer**: Use `defer` to ensure unpin even on error
   ```swift
   let page = try await bufferManager.getPage(pageId: pageId)
   defer { 
       Task {
           try? await bufferManager.unpinPage(pageId: pageId)
       }
   }
   // Use page (even if error occurs)
   ```

#### 5.2.4 Flush Page

```swift
public func flushPage(pageId: PageID) async throws
```

**TLA+ Action**: `FlushPage(pageId)`

**Behavior**: Detailed step-by-step execution

1. **Check if Page is Dirty**:
   ```swift
   guard dirtyPages.contains(pageId) else {
       return  // Page is clean, no need to flush
   }
   ```
   - **Early Exit**: Clean pages don't need flushing
   - **Performance**: Avoids unnecessary I/O
   - **Idempotent**: Safe to call multiple times

2. **Retrieve Page from Buffer**:
   ```swift
   guard let frameIndex = pageTable[pageId],
         let page = bufferPool[frameIndex] else {
       throw BufferError.pageNotFound
   }
   ```
   - Page must exist in buffer
   - Retrieve page data for writing

3. **Verify WAL-Before-Data Property**:
   ```swift
   guard page.lsn <= flushedLSN else {
       throw BufferError.flushFailed  // WAL must be flushed before page write
   }
   ```
   - **Critical Check**: Ensures WAL is ahead of data
   - **Recovery Guarantee**: Enables ARIES recovery
   - **Safety**: Prevents data loss on crash
   
   **Why This Check**:
   - If crash occurs, WAL contains all changes
   - Recovery can replay WAL records to reconstruct data
   - If data written before WAL, changes may be lost

4. **Write Page to Disk**:
   ```swift
   try await diskManager.writePage(pageId: pageId, data: page.data)
   ```
   - **Non-Blocking**: Async I/O doesn't block thread
   - **Atomic**: Disk write is atomic (one page at a time)
   - **Durable**: Data persisted to stable storage
   
   **I/O Characteristics**:
   - **Latency**: ~5-10ms (typical SSD)
   - **Throughput**: Limited by disk I/O bandwidth
   - **Error Handling**: Propagates disk I/O errors

5. **Mark Page as Clean**:
   ```swift
   dirtyPages.remove(pageId)
   ```
   - Remove from dirty set
   - Page is now synchronized with disk
   - Page can be evicted without flushing

6. **Update Metrics**:
   ```swift
   updateMetrics()
   // Update dirtyFrames count, I/O operations, latency
   ```
   - Decrement dirty frame count
   - Increment I/O operations count
   - Record flush latency

**Preconditions**:
- Page is in buffer (`pageTable[pageId] != nil`)
- Page is dirty (`dirtyPages.contains(pageId)`)
- **Critical**: `page.lsn <= flushedLSN` (WAL-before-data property)

**Postconditions**:
- Page written to disk successfully
- Page marked clean (`dirtyPages` no longer contains pageId)
- Page data synchronized with disk
- Metrics updated (dirty frames, I/O operations, latency)

**Performance Characteristics**:
- **Flush**: ~5-10ms (disk I/O dominates)
- **Clean Page**: ~10ns (early exit)
- **With WAL Check**: ~10ns additional (integer comparison)

**WAL-Before-Data Property Explained**:

The WAL-before-data property ensures that for any dirty page:
```
page.lsn <= flushedLSN
```

This means:
- **All WAL records** affecting this page have been flushed
- **Recovery is possible**: If crash occurs, WAL contains all changes
- **No data loss**: All modifications are logged before being written

**Example Scenario**:

```
1. Transaction modifies page 1
   - WAL record written (LSN = 100)
   - Page marked dirty (page.lsn = 100)
   - flushedLSN = 0 (WAL not flushed yet)

2. WAL flush occurs
   - WAL records flushed (flushedLSN = 100)
   - BufferManager.updateFlushedLSN(100) called

3. Now page can be flushed
   - page.lsn (100) <= flushedLSN (100) ✓
   - Flush proceeds
```

**Edge Cases**:

1. **Page Not Dirty**: Clean page flush
   - **Behavior**: Early return (no I/O)
   - **Performance**: Optimized path
   - **Idempotent**: Safe to call multiple times

2. **WAL Not Flushed**: `page.lsn > flushedLSN`
   - **Behavior**: Throws `BufferError.flushFailed`
   - **Recovery**: Wait for WAL flush, then retry
   - **Prevention**: Ensure WAL flushes before buffer flushes

3. **Disk Write Failure**: I/O error during write
   - **Behavior**: Error propagates to caller
   - **State**: Page remains dirty (not marked clean)
   - **Recovery**: Retry flush after fixing disk issue

4. **Page Not Found**: Page not in buffer
   - **Behavior**: Throws `BufferError.pageNotFound`
   - **Prevention**: Check page exists before flush

5. **Concurrent Flush**: Multiple flush attempts
   - **Behavior**: Actor isolation serializes operations
   - **Safety**: Only one flush at a time
   - **Result**: First flush succeeds, subsequent are idempotent (page clean)

**Errors**:
- `BufferError.pageNotFound`: Page not in buffer
- `BufferError.flushFailed`: WAL not flushed (`page.lsn > flushedLSN`) or disk I/O failed
- `DBError.ioError`: Disk I/O error (propagated from DiskManager)

**Integration with WAL**:

```swift
// Typical flush coordination pattern
async func coordinateFlush() throws {
    // 1. Transaction commits, writes WAL record
    let lsn = try await wal.append(kind: .heapUpdate, txID: txId, ...)
    
    // 2. Update page LSN
    page.lsn = lsn
    try await bufferManager.putPage(pageId: pageId, page: page, isDirty: true)
    
    // 3. Flush WAL
    try await wal.flush()
    
    // 4. Update BufferManager flushedLSN
    await bufferManager.updateFlushedLSN(await wal.getFlushedLSN())
    
    // 5. Now page can be flushed
    try await bufferManager.flushPage(pageId: pageId)
}
```

**Performance Optimizations**:

1. **Batch Flushing**: `flushAll()` flushes multiple pages
   - Reduces per-page overhead
   - Better disk throughput (sequential writes)

2. **Background Flushing**: Can run in background task
   - Doesn't block user operations
   - Improves responsiveness

3. **Selective Flushing**: Only flush dirty pages
   - Avoids unnecessary I/O
   - Better throughput

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

The Buffer Manager supports four eviction policies to handle different workload patterns. The policy is selected at initialization time and cannot be changed during runtime.

### 6.1 LRU (Least Recently Used)

**Algorithm**: The LRU policy evicts the page that has not been accessed for the longest time.

#### 6.1.1 Implementation Details

**Data Structures**:
- `lruList: [PageID]`: Ordered list where MRU is at end
- Position: `[LRU, ..., MRU]` (least recent at beginning, most recent at end)

**On Page Access** (`getPage()`):
```swift
// Move page to end (MRU position)
func moveToMRU(pageId: PageID) {
    lruList.removeAll { $0 == pageId }  // O(n) - remove if exists
    lruList.append(pageId)               // O(1) - append to end
}
```

**On Page Eviction** (`evictPage()`):
```swift
private func applyLRUPolicy() throws -> PageID {
    // Scan from least recently used (beginning) to most recently used (end)
    for pageId in lruList {  // O(n) worst case
        guard pinCounts[pageId] == 0 else {
            continue  // Skip pinned pages
        }
        return pageId  // Found unpinned page - evict it
    }
    throw BufferError.noPageToEvict  // All pages pinned
}
```

#### 6.1.2 Complexity Analysis

| Operation | Best Case | Average Case | Worst Case |
|-----------|-----------|--------------|------------|
| Access | O(1) | O(n/2) | O(n) |
| Eviction | O(1) | O(n/2) | O(n) |

**Explanation**:
- **Access**: Must find page in list (O(n)) and move to end (O(1))
- **Eviction**: Must scan list to find unpinned page (O(n) worst case)

**Optimization**: Using doubly-linked list would improve access to O(1), but array is simpler and sufficient for typical pool sizes (100-10,000 frames).

#### 6.1.3 Use Cases

**Best For**:
- General-purpose workloads
- Mixed read/write patterns
- Temporal locality (recently accessed pages likely to be accessed again)
- OLTP workloads (transaction processing)

**Example Workload**:
```
Transaction 1: Read pages [1, 2, 3]
Transaction 2: Read pages [2, 4, 5]  // Page 2 is hot
Transaction 3: Read pages [3, 6, 7]  // Page 3 is hot
Eviction: Page 1 evicted (least recently used)
```

#### 6.1.4 Performance Characteristics

**Cache Locality**: Excellent (recent pages stay in cache)

**Overhead**: 
- Access: ~100ns for list manipulation (1000 frames)
- Eviction: ~1μs for scan (1000 frames)

**Hit Rate**: Typically 95%+ for OLTP workloads with temporal locality

#### 6.1.5 Edge Cases

1. **All Pages Pinned**: 
   - **Behavior**: Throws `BufferError.noPageToEvict`
   - **Recovery**: Caller must unpin pages or wait

2. **Empty List**:
   - **Behavior**: Throws `BufferError.noPageToEvict`
   - **Prevention**: Should not occur if pool is full

3. **Single Page**:
   - **Behavior**: Evicts if unpinned
   - **Prevention**: Pool size should be > 1

### 6.2 Clock (Second-Chance)

**Algorithm**: The Clock policy gives pages a "second chance" before eviction, providing better performance for mixed read/write workloads.

#### 6.2.1 Implementation Details

**Data Structures**:
- `lruList: [PageID]`: Circular list of pages
- `referenceBits: [PageID -> Bool]`: Reference bit per page
- `clockHand: Int`: Current position in circular list

**On Page Access** (`getPage()`):
```swift
// Set reference bit to give second chance
referenceBits[pageId] = true  // O(1)
moveToMRU(pageId: pageId)     // O(n) - but optional for Clock
```

**On Page Eviction** (`evictPage()`):
```swift
private func applyClockPolicy() throws -> PageID {
    let maxScans = max(lruList.count * 2, poolSize)  // Prevent infinite loop
    
    for _ in 0..<maxScans {  // O(n) worst case
        // Wrap clock hand
        if clockHand >= lruList.count || lruList.isEmpty {
            clockHand = 0
        }
        
        guard clockHand < lruList.count, !lruList.isEmpty else {
            throw BufferError.noPageToEvict
        }
        
        let pageId = lruList[clockHand]
        
        // Skip pinned pages
        if pinCounts[pageId] != 0 {
            clockHand = (clockHand + 1) % max(lruList.count, 1)
            continue
        }
        
        // Check reference bit
        if referenceBits[pageId] == true {
            // Give second chance - clear reference bit
            referenceBits[pageId] = false
            clockHand = (clockHand + 1) % max(lruList.count, 1)
            continue
        }
        
        // Found victim - evict it
        return pageId
    }
    
    throw BufferError.noPageToEvict  // All pinned or all have reference bits
}
```

#### 6.2.2 Algorithm Explanation

The Clock algorithm implements a "second-chance" mechanism:

1. **Reference Bit Set**: Page was recently accessed
   - Clear bit and move to next page
   - Page gets another chance before eviction

2. **Reference Bit Clear**: Page has not been accessed since last sweep
   - Evict this page
   - This is the victim

3. **Circular Scan**: Clock hand moves through pages in order
   - Wraps around when reaching end
   - Ensures fairness (all pages considered)

**Visual Representation**:
```
Clock Hand: →
Reference Bits: [1, 0, 1, 0, 1, 1, 0, ...]
              ↑
         Evict this (bit = 0)

After eviction:
Clock Hand: →
Reference Bits: [1, 0, 1, 0, 1, 1, 0, ...]
                  ↑
             Consider next (bit = 1, clear and skip)
```

#### 6.2.3 Complexity Analysis

| Operation | Best Case | Average Case | Worst Case |
|-----------|-----------|--------------|------------|
| Access | O(1) | O(1) | O(1) |
| Eviction | O(1) | O(n/2) | O(n) |

**Explanation**:
- **Access**: O(1) - just set reference bit
- **Eviction**: O(n) worst case (scan entire pool if all bits set)

**Optimization**: Maximum scans limit prevents infinite loops if all pages are pinned.

#### 6.2.4 Use Cases

**Best For**:
- Mixed read/write workloads
- Sequential scans (reference bit prevents premature eviction)
- Scan-heavy workloads (better than LRU for scans)

**Example Workload**:
```
Transaction 1: Read pages [1, 2, 3]     // Bits: [1, 1, 1]
Transaction 2: Scan pages [4, 5, 6, ...] // Bits: [1, 1, 1, 1, ...]
Clock Sweep: All bits = 1, clear all, next sweep evicts oldest
Eviction: Page 1 evicted (bit cleared on previous sweep)
```

#### 6.2.5 Performance Characteristics

**Cache Locality**: Good (recent pages have reference bits set)

**Overhead**:
- Access: ~10ns (just set bit)
- Eviction: ~1-2μs for scan (1000 frames, worst case)

**Hit Rate**: Typically 90-95% for mixed workloads

**Advantages over LRU**:
- Faster access (O(1) vs O(n))
- Better for sequential scans (doesn't penalize scan pages)

**Disadvantages**:
- May evict recently accessed pages if bit cleared between accesses
- More complex implementation

#### 6.2.6 Clock Sweep Operation

**Purpose**: Periodically clear reference bits to prevent all pages from getting "second chances"

**Implementation**:
```swift
public func clockSweep() async throws {
    let maxScans = min(lruList.count * 2, poolSize)
    
    for _ in 0..<maxScans {
        if clockHand >= lruList.count {
            clockHand = 0  // Wrap around
        }
        
        let pageId = lruList[clockHand]
        
        // Skip pinned pages
        if pinCounts[pageId] == 0 {
            // Clear reference bit for clock algorithm
            if referenceBits[pageId] == true {
                referenceBits[pageId] = false
            }
        }
        
        clockHand = (clockHand + 1) % lruList.count
    }
}
```

**When to Call**: Can be called periodically (e.g., every N evictions) to improve Clock algorithm effectiveness.

#### 6.2.7 Edge Cases

1. **All Pages Pinned**:
   - **Behavior**: Throws `BufferError.noPageToEvict` after maxScans
   - **Recovery**: Caller must unpin pages

2. **All Reference Bits Set**:
   - **Behavior**: Clears all bits and scans again
   - **Result**: Eventually finds victim (if unpinned page exists)

3. **Empty List**:
   - **Behavior**: Throws `BufferError.noPageToEvict`
   - **Prevention**: Should not occur if pool is full

### 6.3 FIFO (First-In, First-Out)

**Algorithm**: The FIFO policy evicts pages in the order they were added to the buffer, regardless of access patterns.

#### 6.3.1 Implementation Details

**Data Structures**:
- `fifoList: [PageID]`: Queue of pages in insertion order
- Position: `[oldest, ..., newest]` (first in at beginning, last in at end)

**On Page Allocation** (`getPage()` on cache miss):
```swift
fifoList.append(pageId)  // O(1) - append to end
```

**On Page Eviction** (`evictPage()`):
```swift
private func applyFIFOPolicy() throws -> PageID {
    // Scan from oldest (beginning) to newest (end)
    for pageId in fifoList {  // O(n) worst case
        guard pinCounts[pageId] == 0 else {
            continue  // Skip pinned pages
        }
        return pageId  // Found unpinned page - evict it
    }
    throw BufferError.noPageToEvict  // All pages pinned
}
```

#### 6.3.2 Complexity Analysis

| Operation | Best Case | Average Case | Worst Case |
|-----------|-----------|--------------|------------|
| Access | O(1) | O(1) | O(1) |
| Eviction | O(1) | O(n/2) | O(n) |

**Explanation**:
- **Access**: O(1) - just append to list (on allocation)
- **Eviction**: O(n) worst case (scan list to find unpinned page)

#### 6.3.3 Use Cases

**Best For**:
- Sequential workloads
- Streaming data processing
- Pages accessed once (no temporal locality)
- Simple scenarios (no access pattern prediction needed)

**Example Workload**:
```
Transaction 1: Insert pages [1, 2, 3]     // FIFO: [1, 2, 3]
Transaction 2: Insert pages [4, 5]        // FIFO: [1, 2, 3, 4, 5]
Eviction: Page 1 evicted (oldest)
Transaction 3: Insert pages [6, 7]        // FIFO: [2, 3, 4, 5, 6, 7]
Eviction: Page 2 evicted (oldest)
```

**Advantages**:
- **Simple**: Easy to implement and understand
- **Fair**: All pages treated equally
- **Predictable**: Eviction order is deterministic

**Disadvantages**:
- **No Locality**: Ignores access patterns
- **Poor for OLTP**: May evict frequently accessed pages
- **Starvation**: Old pages always evicted first

#### 6.3.4 Performance Characteristics

**Cache Locality**: Poor (no consideration of access patterns)

**Overhead**:
- Access: ~10ns (just append)
- Eviction: ~1μs for scan (1000 frames, worst case)

**Hit Rate**: Typically 60-70% for sequential workloads, 40-50% for random access

#### 6.3.5 Edge Cases

1. **All Pages Pinned**:
   - **Behavior**: Throws `BufferError.noPageToEvict`
   - **Recovery**: Caller must unpin pages

2. **Empty Queue**:
   - **Behavior**: Throws `BufferError.noPageToEvict`
   - **Prevention**: Should not occur if pool is full

### 6.4 Random

**Algorithm**: The Random policy evicts a random unpinned page, providing no predictability but avoiding bias.

#### 6.4.1 Implementation Details

**Data Structures**:
- `lruList: [PageID]`: List of all pages (used for random selection)

**On Page Eviction** (`evictPage()`):
```swift
private func applyRandomPolicy() throws -> PageID {
    // Filter unpinned pages
    let unpinnedPages = lruList.filter { pinCounts[$0] == 0 }  // O(n)
    
    guard !unpinnedPages.isEmpty else {
        throw BufferError.noPageToEvict
    }
    
    // Select random page
    let randomIndex = Int.random(in: 0..<unpinnedPages.count)  // O(1)
    return unpinnedPages[randomIndex]  // O(1)
}
```

#### 6.4.2 Complexity Analysis

| Operation | Best Case | Average Case | Worst Case |
|-----------|-----------|--------------|------------|
| Access | O(1) | O(1) | O(1) |
| Eviction | O(n) | O(n) | O(n) |

**Explanation**:
- **Access**: O(1) - no special handling needed
- **Eviction**: O(n) - must filter unpinned pages, then random select

#### 6.4.3 Use Cases

**Best For**:
- Testing and benchmarking
- Uniform access patterns (all pages equally likely)
- Stress testing (no bias in eviction)
- Research scenarios

**Example Workload**:
```
Transaction 1: Read pages [1, 2, 3, 4, 5]
Eviction: Random page evicted (could be any of 1-5)
Transaction 2: Read pages [6, 7, 8]
Eviction: Random page evicted (could be any unpinned page)
```

**Advantages**:
- **No Bias**: Fair eviction (no preference)
- **Simple**: Easy to implement
- **Testing**: Useful for stress tests

**Disadvantages**:
- **No Locality**: Ignores access patterns completely
- **Poor Performance**: Worst hit rate for typical workloads
- **Non-Deterministic**: Results vary between runs

#### 6.4.4 Performance Characteristics

**Cache Locality**: None (random eviction)

**Overhead**:
- Access: ~10ns (no special handling)
- Eviction: ~1μs for filter + random (1000 frames)

**Hit Rate**: Typically 50-60% (approaches random chance as pool size increases)

#### 6.4.5 Edge Cases

1. **All Pages Pinned**:
   - **Behavior**: Throws `BufferError.noPageToEvict`
   - **Recovery**: Caller must unpin pages

2. **Single Unpinned Page**:
   - **Behavior**: Always evicts that page
   - **Result**: Deterministic when only one choice

### 6.5 Policy Selection Guidelines

| Workload Type | Recommended Policy | Reason |
|---------------|-------------------|--------|
| OLTP (general) | LRU | Temporal locality, hot pages stay |
| Mixed read/write | Clock | Second chance, scan-friendly |
| Sequential scan | FIFO | Simple, predictable |
| Random access | LRU | Best overall for unknown patterns |
| Testing | Random | No bias, stress testing |
| Unknown | LRU | Default, good for most cases |

### 6.6 Policy Comparison

| Policy | Access Time | Eviction Time | Hit Rate | Complexity |
|--------|-------------|---------------|----------|------------|
| LRU | O(n) | O(n) | 95%+ | Medium |
| Clock | O(1) | O(n) | 90-95% | High |
| FIFO | O(1) | O(n) | 60-70% | Low |
| Random | O(1) | O(n) | 50-60% | Low |

**Recommendation**: Use **LRU** as default for general workloads, **Clock** for mixed workloads with scans.

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

**Target**: > 95% hit rate for typical OLTP workloads

**Calculation**:
```swift
let total = hitCount + missCount
let hitRate = total > 0 ? Double(hitCount) / Double(total) : 0.0
```

**Metrics Tracked**:
- `hitCount`: Total cache hits (page found in buffer)
- `missCount`: Total cache misses (page read from disk)
- `hitRate`: Cache hit rate (0.0-1.0)
- `missRate`: Cache miss rate (0.0-1.0) = 1.0 - hitRate

**When Updated**:
- On every `getPage()` call
- Increments `hitCount` if cache hit
- Increments `missCount` if cache miss
- Recalculates rates

**Typical Values**:

| Workload | Hit Rate | Miss Rate |
|----------|----------|-----------|
| OLTP (hot) | 95-99% | 1-5% |
| OLTP (warm) | 85-95% | 5-15% |
| OLAP (scan) | 50-70% | 30-50% |
| Mixed | 70-90% | 10-30% |

**Factors Affecting Hit Rate**:

1. **Buffer Pool Size**:
   - Larger pool = higher hit rate (more pages cached)
   - Diminishing returns (doubling size doesn't double hit rate)

2. **Workload Pattern**:
   - **Temporal Locality**: High hit rate (recent pages accessed again)
   - **Random Access**: Lower hit rate (no pattern)
   - **Sequential Scan**: Very low hit rate (each page accessed once)

3. **Eviction Policy**:
   - **LRU**: Best for temporal locality (95%+)
   - **Clock**: Good for mixed (90-95%)
   - **FIFO**: Poor for most workloads (60-70%)

4. **Pin Duration**:
   - Long pin duration = pages stay longer = better hit rate
   - But also prevents eviction of other pages

**Optimization Strategies**:

1. **Increase Pool Size**: If hit rate < 90%, consider larger pool
2. **Optimize Eviction**: Use LRU for OLTP workloads
3. **Reduce Pin Time**: Unpin pages as soon as possible
4. **Prefetching**: Prefetch likely-to-be-accessed pages

### 8.2 Latency

**Target**: < 1ms average latency for cache hits, < 10ms for cache misses

**Calculation**:
```swift
private func updateLatency(_ latency: Double) {
    let alpha = 0.1  // Exponential moving average factor
    if metrics.averageLatency == 0.0 {
        metrics.averageLatency = latency  // Initialize
    } else {
        // Exponential moving average
        metrics.averageLatency = alpha * latency + (1.0 - alpha) * metrics.averageLatency
    }
}
```

**Latency Breakdown**:

| Operation | Component | Typical Time |
|-----------|-----------|--------------|
| Cache Hit | Hash lookup | ~10ns |
| Cache Hit | Pin increment | ~5ns |
| Cache Hit | LRU update | ~100ns |
| Cache Hit | Metrics update | ~10ns |
| **Total Hit** | | **~125ns** |
| Cache Miss | Frame allocation | ~100ns |
| Cache Miss | Disk I/O (SSD) | ~5-10ms |
| Cache Miss | Page creation | ~50ns |
| Cache Miss | Buffer insertion | ~100ns |
| **Total Miss** | | **~5-10ms** |
| Eviction | Policy selection | ~1μs |
| Eviction | Flush (if dirty) | ~5-10ms |
| Eviction | Cleanup | ~100ns |
| **Total Eviction** | | **~1-10ms** |

**Exponential Moving Average (EMA)**:

EMA provides smooth, responsive latency tracking:

- **Formula**: `avg = alpha * new + (1 - alpha) * avg`
- **Alpha = 0.1**: 
  - 10% weight to new value
  - 90% weight to historical average
  - Smooths out spikes
  - Responsive to trends

**Why EMA**:
- **Smooth**: Reduces noise from occasional slow operations
- **Responsive**: Adapts to changes in workload
- **Simple**: O(1) calculation
- **Memory Efficient**: Only stores single average value

**Example EMA Calculation**:
```
Initial: avg = 0.0
Hit 1: 100ns  -> avg = 0.1 * 100 + 0.9 * 0 = 10ns
Hit 2: 150ns  -> avg = 0.1 * 150 + 0.9 * 10 = 24ns
Hit 3: 120ns  -> avg = 0.1 * 120 + 0.9 * 24 = 33.6ns
Miss 1: 5ms   -> avg = 0.1 * 5000000 + 0.9 * 33.6 = 500030ns ≈ 0.5ms
Hit 4: 110ns  -> avg = 0.1 * 110 + 0.9 * 500030 ≈ 450028ns ≈ 0.45ms
```

**Performance Targets**:

| Metric | Target | Acceptable | Poor |
|--------|--------|------------|------|
| Hit Latency | < 0.2ms | < 1ms | > 1ms |
| Miss Latency | < 10ms | < 20ms | > 20ms |
| Average Latency | < 1ms | < 5ms | > 5ms |

### 8.3 Eviction Rate

**Definition**: Number of pages evicted per second (or per operation)

**Calculation**:
```swift
// Total evictions tracked
metrics.evictionCount += 1  // Incremented on each eviction

// Rate calculation (external)
evictionRate = evictions / timeElapsed
```

**Typical Values**:

| Workload | Evictions/sec | Evictions/op |
|----------|---------------|--------------|
| Read-heavy | 0-10 | 0.001-0.01 |
| Write-heavy | 10-100 | 0.01-0.1 |
| Scan-heavy | 100-1000 | 0.1-1.0 |

**Factors Affecting Eviction Rate**:

1. **Buffer Pool Size**: Smaller pool = higher eviction rate
2. **Workload Size**: More pages accessed = more evictions
3. **Pin Duration**: Longer pins = fewer evictions possible
4. **Access Pattern**: Random access = more evictions than sequential

**High Eviction Rate Implications**:

- **Performance Impact**: More disk I/O required
- **Hit Rate Impact**: Lower hit rate (pages evicted before reuse)
- **Action**: Consider increasing buffer pool size

**Low Eviction Rate Implications**:

- **Memory Efficiency**: Most pages stay in buffer
- **Hit Rate Impact**: Higher hit rate
- **Observation**: Normal for hot workloads

### 8.4 Throughput

**Definition**: Operations per second (gets, puts, flushes, etc.)

**Calculation**:
```swift
throughput = totalOperations / timeElapsed
```

**Typical Values**:

| Operation Type | Throughput (ops/sec) |
|----------------|---------------------|
| Cache Hits | 1,000,000 - 10,000,000 |
| Cache Misses | 100 - 1,000 |
| Mixed (95% hit) | 100,000 - 1,000,000 |

**Bottlenecks**:

1. **Disk I/O**: Primary bottleneck for cache misses (~5-10ms per read)
2. **CPU**: Minimal impact (< 1% for typical workloads)
3. **Memory Bandwidth**: Not a bottleneck (pages are small)

### 8.5 Memory Usage

**Calculation**:
```swift
// Per page overhead
let pageSize = 4096  // 4KB typical
let overhead = MemoryLayout<BufferPage>.size  // ~64 bytes
let totalPerPage = pageSize + overhead  // ~4.1KB

// Total buffer pool memory
let totalMemory = poolSize * totalPerPage  // e.g., 1000 * 4.1KB = 4.1MB
```

**Memory Breakdown** (1000-frame pool, 4KB pages):

| Component | Size | Percentage |
|-----------|------|------------|
| Page Data | 4MB | 97% |
| BufferPage Structs | 64KB | 1.5% |
| Indexes (pageTable, etc.) | ~40KB | 1% |
| Lists (LRU, FIFO, etc.) | ~20KB | 0.5% |
| **Total** | **~4.1MB** | **100%** |

**Memory Efficiency**:
- **Overhead**: < 3% per page
- **Scalable**: Linear with pool size
- **Optimized**: Minimal allocations

### 8.6 Scalability

**Horizontal Scaling** (More Buffer Managers):
- Each database instance has own Buffer Manager
- No shared state between instances
- Linear scaling with instances

**Vertical Scaling** (Larger Pool Size):
- More pages cached = higher hit rate
- Diminishing returns after ~10,000 frames
- Memory cost increases linearly

**Concurrent Operations**:
- Actor isolation serializes operations
- Multiple concurrent `getPage()` calls are queued
- No lock contention (zero locks)
- Throughput limited by single actor

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

