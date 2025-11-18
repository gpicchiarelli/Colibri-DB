# RFC 0006: Storage Manager

**Status**: Standards Track  
**Author**: ColibrìDB Team  
**Date**: 2025-11-18  
**TLA+ Spec**: `spec/Storage.tla`

## Abstract

This RFC defines the Storage Manager component, responsible for managing disk I/O operations, page allocation/deallocation, and integrating with the Buffer Manager for efficient caching.

## 1. Introduction

The Storage Manager provides high-level storage operations, coordinating with the Buffer Manager for page caching and with the Disk Manager for physical I/O. It manages storage areas (data, index, log, temp, system) and tracks free space.

### 1.1 Purpose and Goals

The primary goals of the Storage Manager are:

1. **Abstraction Layer**: Provide high-level storage operations above raw disk I/O
2. **Buffer Integration**: Seamlessly integrate with Buffer Manager for efficient caching
3. **Space Management**: Track and manage free space efficiently across storage areas
4. **Data Organization**: Organize data into logical storage areas (data, index, log, temp, system)
5. **Performance Optimization**: Minimize disk I/O through intelligent caching and space management

### 1.2 Problem Statement

Database systems need to:

- **Manage Disk Space**: Allocate and deallocate pages efficiently
- **Organize Data**: Separate data types (user data, indexes, logs, temp, system)
- **Track Free Space**: Know where free space exists for allocation
- **Coordinate Caching**: Work with Buffer Manager without duplication
- **Handle I/O Efficiently**: Minimize disk operations through caching

The Storage Manager solves these challenges by:

- Providing high-level page allocation/deallocation APIs
- Organizing pages into logical storage areas
- Maintaining free space maps for efficient allocation
- Integrating with Buffer Manager for automatic caching
- Falling back to direct disk I/O when Buffer Manager unavailable

### 1.3 Key Concepts

**Storage Area**: Logical organization of pages by type:
- **Data**: User table data pages
- **Index**: Index structure pages
- **Log**: Transaction log pages (separate from WAL)
- **Temp**: Temporary pages (queries, sorts)
- **System**: System catalog and metadata pages

**Free Space Map**: Efficient data structure tracking available space per page:
- `[PageID -> FreeSpace]`: Maps page IDs to available bytes
- Enables fast allocation (find page with sufficient space)
- Updated on allocation/deallocation operations

**Page**: Fixed-size unit of storage (typically 4KB-16KB):
- Contains data or metadata
- Managed by Storage Manager
- Cached by Buffer Manager (if available)

**Record**: Variable-size data unit stored within pages:
- May span multiple pages (large records)
- Tracked by Storage Manager
- Referenced by RecordID

**Buffer Manager Integration**: Optional but recommended:
- When available: Uses buffer cache for reads/writes
- When unavailable: Falls back to direct disk I/O
- Benefits: Reduced disk I/O, better performance

### 1.4 Relationship to Other Components

```
Storage Manager
    ↓ uses
Buffer Manager (optional)
    ↓ uses
Disk Manager
    ↓ performs
Physical I/O
```

**With Buffer Manager** (recommended):
```
Read: StorageManager → BufferManager → DiskManager
Write: StorageManager → BufferManager (dirty) → later → DiskManager
```

**Without Buffer Manager** (fallback):
```
Read: StorageManager → DiskManager
Write: StorageManager → DiskManager
```

## 2. Design Principles

### 2.1 Buffer Manager Integration

The Storage Manager integrates with the Buffer Manager when available to provide efficient page caching.

#### 2.1.1 Cache-First Strategy

**When Buffer Manager is Available**:

**Read Operations**:
```swift
// StorageManager.readPage() with BufferManager
if let bufferManager = bufferManager {
    // 1. Get page from buffer (automatically pins)
    let bufferPage = try await bufferManager.getPage(pageId: pageId)
    
    // 2. Extract data
    let pageData = bufferPage.data
    
    // 3. Unpin immediately (StorageManager doesn't hold pins)
    try await bufferManager.unpinPage(pageId: pageId)
    
    return pageData
}
```

**Benefits**:
- **Cache Hit**: ~100ns if page in buffer (vs ~5-10ms disk read)
- **Automatic Caching**: Buffer Manager handles cache management
- **Transparent**: Storage Manager doesn't need to know cache state

**Write Operations**:
```swift
// StorageManager.writePage() with BufferManager
if let bufferManager = bufferManager {
    // Check if page exists in buffer
    if await bufferManager.isPageInCache(pageId: pageId) {
        // Update existing cached page
        let bufferPage = try await bufferManager.getPage(pageId: pageId)
        let updatedPage = BufferPage(
            pageId: pageId,
            data: data,
            lsn: bufferPage.lsn + 1,  // Increment LSN
            isDirty: true,
            isPinned: false,
            timestamp: UInt64(Date().timeIntervalSince1970 * 1000)
        )
        try await bufferManager.putPage(pageId: pageId, page: updatedPage, isDirty: true)
    } else {
        // Create new buffer page
        let bufferPage = BufferPage(...)
        try await bufferManager.putPage(pageId: pageId, page: bufferPage, isDirty: true)
    }
    
    // Unpin after writing
    try await bufferManager.unpinPage(pageId: pageId)
}
```

**Benefits**:
- **Write-Back Caching**: Writes go to buffer, flushed later
- **Batch Flushing**: Multiple writes can be flushed together
- **Durability**: Buffer Manager coordinates with WAL for durability

#### 2.1.2 Fallback Strategy

**When Buffer Manager is Not Available**:

**Read Operations**:
```swift
// Direct disk I/O fallback
return try await diskManager.readPage(pageId: pageId)
```

**Write Operations**:
```swift
// Direct disk write
try await diskManager.writePage(pageId: pageId, data: data)
```

**Use Cases**:
- Testing without buffer cache
- Embedded scenarios with limited memory
- Direct I/O for specific operations

**Performance Impact**:
- **No Caching**: Every read/write hits disk
- **Higher Latency**: ~5-10ms per operation (vs ~100ns cached)
- **Simple**: No cache coordination needed

### 2.2 Storage Areas

Organizes storage into logical areas for efficient management and isolation.

#### 2.2.1 Area Types

**Data Area** (`StorageArea.data`):
- **Purpose**: User table data pages
- **Characteristics**: Frequently accessed, large volume
- **Optimization**: High priority for caching
- **Example**: Table rows, user data

**Index Area** (`StorageArea.index`):
- **Purpose**: Index structure pages (B+Tree, Hash, etc.)
- **Characteristics**: Frequently accessed, moderate volume
- **Optimization**: High priority for caching
- **Example**: B+Tree nodes, hash buckets

**Log Area** (`StorageArea.log`):
- **Purpose**: Transaction log pages (separate from WAL)
- **Characteristics**: Sequential writes, large volume
- **Optimization**: Lower priority for caching (sequential access)
- **Example**: Transaction logs, audit logs

**Temp Area** (`StorageArea.temp`):
- **Purpose**: Temporary pages (queries, sorts, joins)
- **Characteristics**: Short-lived, moderate volume
- **Optimization**: Lower priority for caching (temporary)
- **Example**: Sort buffers, hash join tables

**System Area** (`StorageArea.system`):
- **Purpose**: System catalog and metadata pages
- **Characteristics**: Frequently accessed, small volume
- **Optimization**: High priority for caching (always accessed)
- **Example**: Catalog tables, metadata

#### 2.2.2 Area Management

**Storage Structure**:
```swift
storageAreas: [StorageArea -> [PageID]]
```

**Example**:
```swift
storageAreas = [
    .data: [1, 2, 3, 10, 11, 12],
    .index: [4, 5, 6],
    .log: [7, 8, 9],
    .temp: [13, 14],
    .system: [15, 16, 17]
]
```

**Benefits**:
- **Isolation**: Areas can have different policies (compression, encryption)
- **Optimization**: Area-specific caching strategies
- **Management**: Easy to query pages by area
- **Cleanup**: Easy to deallocate entire areas (e.g., temp)

### 2.3 Space Management

Tracks free space per page for efficient allocation.

#### 2.3.1 Free Space Map

**Data Structure**:
```swift
freeSpaceMap: [PageID -> UInt64]
```

**Purpose**: Track available bytes per page

**Example**:
```swift
freeSpaceMap = [
    PageID(1): 2048,  // 2KB free
    PageID(2): 0,     // Full
    PageID(3): 4096   // 4KB free (empty page)
]
```

#### 2.3.2 Allocation Strategy

**Find Free Page Algorithm**:
```swift
func findFreePage(area: StorageArea, size: UInt64) async throws -> PageID {
    // 1. Get pages in area
    guard let areaPages = storageAreas[area] else {
        // No pages in area, allocate new page
        return try await allocateNewPage(area: area)
    }
    
    // 2. Find page with sufficient free space
    for pageId in areaPages {
        if let freeSpace = freeSpaceMap[pageId],
           freeSpace >= size {
            return pageId  // Found page with enough space
        }
    }
    
    // 3. No page with sufficient space, allocate new
    return try await allocateNewPage(area: area)
}
```

**Optimization**: Can use priority queue or sorted map for O(log n) lookup instead of O(n).

#### 2.3.3 Free Space Updates

**On Allocation**:
```swift
// Allocate space from page
let oldFreeSpace = freeSpaceMap[pageId] ?? PAGE_SIZE
freeSpaceMap[pageId] = oldFreeSpace - allocatedSize
```

**On Deallocation**:
```swift
// Free space back to page
let oldFreeSpace = freeSpaceMap[pageId] ?? 0
freeSpaceMap[pageId] = oldFreeSpace + freedSize
```

**On Page Deallocation**:
```swift
// Remove page from free space map
freeSpaceMap.removeValue(forKey: pageId)
```

### 2.4 Apple-First Architecture

#### 2.4.1 Swift Actor Model

**Why Actors**: Thread-safe storage operations without explicit locking.

```swift
public actor StorageManagerActor {
    // All state isolated within actor
    private var pages: [PageID: Page] = [:]
    private var records: [RecordID: Record] = [:]
    
    // Methods automatically synchronized
    public func readPage(pageId: PageID) async throws -> Data {
        // Safe concurrent access
    }
}
```

**Benefits**:
- **Thread Safety**: No data races
- **No Locks**: Actors eliminate lock contention
- **Composable**: Easy to compose with other actors

#### 2.4.2 Async/Await

**Why Async/Await**: I/O operations are inherently asynchronous.

```swift
// Non-blocking page read
public func readPage(pageId: PageID) async throws -> Data {
    // Suspends task, allows other work
    let data = try await diskManager.readPage(pageId: pageId)
    // Resumes when I/O completes
    return data
}
```

**Benefits**:
- **Non-Blocking**: Threads not blocked on I/O
- **Concurrent**: Supports thousands of concurrent operations
- **Structured**: Clear error handling and control flow

#### 2.4.3 Value Types

**Why Value Types**: Immutable data structures are thread-safe by default.

```swift
public struct Page: Sendable {
    public let pageID: PageID
    public let data: Data
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
StorageManagerActor (Swift Actor)
├── pages: [PageID -> Page]
│   ├── Purpose: Allocated pages in memory
│   ├── Type: Dictionary mapping PageID to Page
│   ├── Lifetime: Pages exist until deallocated
│   └── Access: O(1) hash table lookup
│
├── records: [RecordID -> Record]
│   ├── Purpose: Variable-size records stored in pages
│   ├── Type: Dictionary mapping RecordID to Record
│   ├── Lifetime: Records exist until deleted
│   └── Access: O(1) hash table lookup
│
├── freeSpaceMap: [PageID -> UInt64]
│   ├── Purpose: Track free space per page
│   ├── Type: Dictionary mapping PageID to free bytes
│   ├── Updates: On allocation/deallocation
│   └── Use: Find pages with sufficient space
│
├── storageAreas: [StorageArea -> [PageID]]
│   ├── Purpose: Organize pages by area type
│   ├── Type: Dictionary mapping StorageArea to PageID list
│   ├── Areas: data, index, log, temp, system
│   └── Use: Area-specific operations and policies
│
├── metrics: StorageMetrics
│   ├── Purpose: Performance monitoring
│   ├── Updates: On each operation
│   └── Threading: Non-isolated (atomic updates)
│
├── diskManager: DiskManager
│   ├── Purpose: Physical disk I/O operations
│   ├── Used: When BufferManager unavailable or fallback
│   └── Operations: readPage, writePage
│
├── bufferManager: BufferManager? (optional)
│   ├── Purpose: Page caching for performance
│   ├── When Available: Used for all reads/writes
│   ├── When Unavailable: Falls back to direct disk I/O
│   └── Benefits: Reduced disk I/O, better performance
│
├── compressionService: CompressionService
│   ├── Purpose: Data compression/decompression
│   ├── Usage: Optional compression of page data
│   └── Benefits: Reduced storage space, I/O bandwidth
│
└── encryptionService: EncryptionService
    ├── Purpose: Data encryption/decryption
    ├── Usage: Optional encryption of sensitive pages
    └── Benefits: Data security, confidentiality
```

### 3.2 Data Flow Diagrams

#### 3.2.1 Page Read Flow (With Buffer Manager)

```
┌──────────────┐
│ readPage(id) │
└──────┬───────┘
       │
       ▼
   ┌──────────────────────┐
   │BufferManager         │
   │Available?            │
   └───┬──────────────┬───┘
       │Yes           │No
       ▼              ▼
  ┌──────────┐  ┌──────────────┐
  │Get from  │  │Read from     │
  │Buffer    │  │DiskManager   │
  │(pins)    │  └───┬──────────┘
  └───┬──────┘      │
      │             │
      ▼             ▼
  ┌──────────┐  ┌──────────┐
  │Extract   │  │Return    │
  │Data      │  │Data      │
  └───┬──────┘  └────┬─────┘
      │              │
      ▼              │
  ┌──────────┐       │
  │Unpin     │       │
  │Page      │       │
  └───┬──────┘       │
      │              │
      └──────┬───────┘
             ▼
        ┌─────────┐
        │Return   │
        │Data     │
        └─────────┘
```

#### 3.2.2 Page Write Flow (With Buffer Manager)

```
┌───────────────┐
│ writePage(id, │
│     data)     │
└──────┬────────┘
       │
       ▼
   ┌──────────────────────┐
   │BufferManager         │
   │Available?            │
   └───┬──────────────┬───┘
       │Yes           │No
       ▼              ▼
  ┌──────────┐  ┌──────────────┐
  │Page in   │  │Write to      │
  │Cache?    │  │DiskManager   │
  └───┬────┬─┘  └───┬──────────┘
      │Yes │No      │
      ▼    ▼        ▼
  ┌─────┐ ┌──────┐ ┌──────────┐
  │Update│ │Create│ │Return    │
  │Existing│ │New  │ │          │
  │Page   │ │Page │ │          │
  └───┬──┘ └───┬──┘ └──────────┘
      │        │
      ▼        ▼
  ┌──────────────┐
  │Put to Buffer │
  │(mark dirty)  │
  └───┬──────────┘
      │
      ▼
  ┌──────────┐
  │Unpin     │
  │Page      │
  └───┬──────┘
      │
      ▼
  ┌─────────┐
  │Complete │
  └─────────┘
```

#### 3.2.3 Page Allocation Flow

```
┌──────────────────┐
│ allocatePage(    │
│   area, size)    │
└──────┬───────────┘
       │
       ▼
   ┌───────────────┐
   │Find Free Page │
   │in Area        │
   └───┬───────────┘
       │
       ▼
   ┌───────────────┐
   │Free Page      │
   │Found?         │
   └───┬───────┬───┘
       │Yes    │No
       ▼       ▼
  ┌─────────┐ ┌──────────────┐
  │Use      │ │Allocate New  │
  │Existing │ │Page          │
  │Page     │ └───┬──────────┘
  └───┬─────┘     │
      │           ▼
      │      ┌──────────────┐
      │      │Create Page   │
      │      │Structure     │
      │      └───┬──────────┘
      │          │
      └──────┬───┘
             ▼
      ┌──────────────┐
      │Update Free   │
      │Space Map     │
      └───┬──────────┘
          │
          ▼
      ┌──────────────┐
      │Add to        │
      │Storage Area  │
      └───┬──────────┘
          │
          ▼
      ┌──────────────┐
      │Update        │
      │Metrics       │
      └───┬──────────┘
          │
          ▼
      ┌──────────────┐
      │Return        │
      │PageID        │
      └──────────────┘
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

**Behavior**: Detailed step-by-step execution

1. **Validate Size**:
   ```swift
   guard size > 0 else {
       throw StorageError.allocationFailed("Size must be > 0")
   }
   ```
   - Size must be positive
   - Typically size <= PAGE_SIZE (4KB-16KB)

2. **Find Free Page in Area**:
   ```swift
   let pageId = try await findFreePage(area: area, size: size)
   ```
   
   **Find Free Page Algorithm**:
   ```swift
   func findFreePage(area: StorageArea, size: UInt64) async throws -> PageID {
       // 1. Get pages in storage area
       guard let areaPages = storageAreas[area] else {
           // No pages in area yet, allocate new
           return try await allocateNewPage(area: area)
       }
       
       // 2. Search for page with sufficient free space
       for pageId in areaPages {
           if let freeSpace = freeSpaceMap[pageId],
              freeSpace >= size {
               // Found page with enough space
               return pageId
           }
       }
       
       // 3. No page with sufficient space, allocate new
       return try await allocateNewPage(area: area)
   }
   ```
   
   **Optimization**: If area has many pages, consider:
   - Sorting `freeSpaceMap` by free space (largest first)
   - Using priority queue for O(log n) lookup
   - Caching "best fit" pages per area

3. **Create or Update Page**:
   ```swift
   // If new page
   if !pages.keys.contains(pageId) {
       let page = Page(pageID: pageId)
       pages[pageId] = page
   }
   
   // If existing page, update free space
   let currentFreeSpace = freeSpaceMap[pageId] ?? PAGE_SIZE
   freeSpaceMap[pageId] = currentFreeSpace - size
   ```
   
   **Free Space Calculation**:
   - New page: `freeSpace = PAGE_SIZE - size`
   - Existing page: `freeSpace = oldFreeSpace - size`
   - Ensures: `freeSpace >= 0`

4. **Add to Storage Area** (if new page):
   ```swift
   if storageAreas[area] == nil {
       storageAreas[area] = []
   }
   if !storageAreas[area]!.contains(pageId) {
       storageAreas[area]!.append(pageId)
   }
   ```
   - Maintains list of pages per area
   - Enables area-specific operations

5. **Update Metrics**:
   ```swift
   updateMetrics()
   // Updates: totalPages, usedPages, freePages, usedSpace, freeSpace
   ```

**Preconditions**:
- `size > 0` (positive size required)
- `size <= PAGE_SIZE` (typically, but not enforced for multi-page allocations)
- Disk has space available (enforced by DiskManager)

**Postconditions**:
- Page allocated (`pages[pageId] != nil`)
- Page in storage area (`storageAreas[area]?.contains(pageId) == true`)
- Free space updated (`freeSpaceMap[pageId] = oldFreeSpace - size`)
- Metrics updated (totalPages, usedPages, etc.)

**Returns**: Allocated `PageID`

**Performance Characteristics**:
- **New Page**: ~1ms (disk allocation)
- **Existing Page**: ~100ns (hash lookup + update)
- **With Buffer Manager**: Same (allocation doesn't use buffer)

**Edge Cases**:

1. **No Free Space in Area**:
   - **Behavior**: Allocates new page
   - **Result**: New `PageID` returned

2. **Size > PAGE_SIZE**:
   - **Behavior**: Allocates new page (doesn't split across pages)
   - **Future**: Could support multi-page allocations

3. **Disk Full**:
   - **Behavior**: `DiskManager` throws error, propagates to caller
   - **Recovery**: Caller handles (may need VACUUM or disk expansion)

4. **Concurrent Allocation**:
   - **Behavior**: Actor isolation serializes operations
   - **Safety**: No race conditions

**Errors**:
- `StorageError.allocationFailed`: Cannot allocate page (disk full, invalid size, etc.)
- `DBError.ioError`: Disk I/O failed (propagated from DiskManager)

**Example Usage**:
```swift
// Allocate page in data area
let pageId = try await storageManager.allocatePage(area: .data, size: 1024)

// Use page for storing records
try await storageManager.writeRecord(recordId: recordId, data: recordData, pageId: pageId)
```

**Optimization Strategies**:

1. **Reuse Free Pages**: Prefer reusing pages with free space over allocating new
2. **Area-Specific Pools**: Maintain pools of free pages per area
3. **Batch Allocation**: Allocate multiple pages at once for bulk operations
4. **Pre-allocation**: Pre-allocate pages in background for fast allocation

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

**Behavior**: Detailed step-by-step execution

1. **Start Latency Tracking**:
   ```swift
   let startTime = Date()
   defer {
       let latency = Date().timeIntervalSince(startTime) * 1000  // ms
       metrics.ioOperations += 1
       updateAverageLatency(latency)
   }
   ```
   - Track operation latency for metrics
   - Update I/O operation count
   - Update average latency using exponential moving average

2. **Check if Buffer Manager Available**:
   ```swift
   if let bufferManager = bufferManager {
       // Use buffer cache path
   } else {
       // Direct disk I/O path
   }
   ```

3. **Buffer Manager Path** (if available):
   ```swift
   // 3a. Get page from buffer (automatically pins)
   let bufferPage = try await bufferManager.getPage(pageId: pageId)
   
   // 3b. Extract page data
   let pageData = bufferPage.data
   
   // 3c. Unpin immediately (StorageManager doesn't hold pins)
   try await bufferManager.unpinPage(pageId: pageId)
   
   // 3d. Return page data
   return pageData
   ```
   
   **Benefits**:
   - **Cache Hit**: ~100ns if page in buffer (vs ~5-10ms disk read)
   - **Automatic Caching**: Buffer Manager handles cache management
   - **No Pin Leaks**: Unpin immediately after use
   
   **Cache Miss Handling**:
   - Buffer Manager handles cache miss internally
   - Reads from disk automatically
   - Updates cache for future accesses

4. **Direct Disk I/O Path** (if Buffer Manager unavailable):
   ```swift
   // 4a. Read directly from disk
   let pageData = try await diskManager.readPage(pageId: pageId)
   
   // 4b. Return page data
   return pageData
   ```
   
   **Characteristics**:
   - **Always Disk I/O**: Every read hits disk (~5-10ms)
   - **No Caching**: No benefit from repeated accesses
   - **Simple**: No cache coordination needed

**Preconditions**:
- Page exists (`pages[pageId] != nil` or page on disk)
- If Buffer Manager used: Page accessible through buffer cache
- If direct I/O: Disk accessible and page on disk

**Postconditions**:
- Page data returned (`Data` containing page contents)
- Metrics updated (I/O operations incremented, latency recorded)
- If Buffer Manager used: Page pinned then unpinned (no leak)
- If direct I/O: Page read from disk

**Returns**: Page data as `Data`

**Performance Characteristics**:
- **With Buffer Manager (Cache Hit)**: ~100ns
- **With Buffer Manager (Cache Miss)**: ~5-10ms (disk I/O)
- **Without Buffer Manager**: ~5-10ms (always disk I/O)

**Latency Breakdown**:

| Component | With Buffer (Hit) | With Buffer (Miss) | Without Buffer |
|-----------|-------------------|-------------------|----------------|
| Buffer lookup | ~10ns | ~10ns | N/A |
| Pin/unpin | ~50ns | ~50ns | N/A |
| Disk I/O | N/A | ~5-10ms | ~5-10ms |
| Metrics update | ~10ns | ~10ns | ~10ns |
| **Total** | **~70ns** | **~5-10ms** | **~5-10ms** |

**Edge Cases**:

1. **Page Not Found**:
   - **Behavior**: `DiskManager` throws error or returns empty data
   - **Error**: `StorageError.pageNotFound` or `DBError.ioError`
   - **Recovery**: Check if page exists before reading

2. **Buffer Manager Error**:
   - **Behavior**: Error propagates to caller
   - **Recovery**: Could fallback to direct disk I/O (future enhancement)

3. **Disk I/O Error**:
   - **Behavior**: Error propagates to caller
   - **Error**: `DBError.ioError`
   - **Recovery**: Retry or handle disk issues

4. **Concurrent Reads**:
   - **Behavior**: Actor isolation serializes operations
   - **Safety**: No data races, but may serialize unnecessarily
   - **Optimization**: Buffer Manager handles concurrent cache access

**Example Usage**:
```swift
// Read page with Buffer Manager
let pageData = try await storageManager.readPage(pageId: pageId)

// Parse page data
let pageHeader = PageHeader(from: pageData)
let records = parseRecords(from: pageData)
```

**Best Practices**:

1. **Use Buffer Manager**: Always use Buffer Manager when available
   - Better performance (cache hits)
   - Automatic cache management
   - Reduced disk I/O

2. **Handle Errors**: Always handle I/O errors
   ```swift
   do {
       let pageData = try await storageManager.readPage(pageId: pageId)
       // Use page data
   } catch StorageError.pageNotFound {
       // Page doesn't exist
   } catch DBError.ioError {
       // Disk I/O failed
   }
   ```

3. **Monitor Metrics**: Track I/O operations and latency
   ```swift
   let metrics = await storageManager.getStorageMetrics()
   print("I/O Operations: \(metrics.ioOperations)")
   print("Average Latency: \(metrics.averageLatency)ms")
   ```

#### 5.2.4 Write Page

```swift
public func writePage(pageId: PageID, data: Data) async throws
```

**TLA+ Action**: `WritePage(pageId, data)`

**Behavior**: Detailed step-by-step execution

1. **Start Latency Tracking**:
   ```swift
   let startTime = Date()
   defer {
       let latency = Date().timeIntervalSince(startTime) * 1000  // ms
       metrics.ioOperations += 1
       updateAverageLatency(latency)
   }
   ```
   - Track operation latency
   - Update I/O operation count
   - Update average latency

2. **Validate Data**:
   ```swift
   guard data.count > 0 else {
       throw StorageError.writeFailed("Data cannot be empty")
   }
   ```
   - Data must be non-empty
   - Typically `data.count == PAGE_SIZE` (4KB-16KB)

3. **Check if Buffer Manager Available**:
   ```swift
   if let bufferManager = bufferManager {
       // Use buffer cache path (write-back)
   } else {
       // Direct disk write path
   }
   ```

4. **Buffer Manager Path** (if available):

   4a. **Check if Page in Cache**:
   ```swift
   if await bufferManager.isPageInCache(pageId: pageId) {
       // Update existing cached page
   } else {
       // Create new buffer page
   }
   ```

   4b. **Update Existing Page**:
   ```swift
   // Get existing page
   let bufferPage = try await bufferManager.getPage(pageId: pageId)
   
   // Create updated buffer page
   let updatedPage = BufferPage(
       pageId: pageId,
       data: data,
       lsn: bufferPage.lsn + 1,  // Increment LSN for modification
       isDirty: true,            // Mark as dirty
       isPinned: false,          // Will be pinned by putPage
       timestamp: UInt64(Date().timeIntervalSince1970 * 1000)
   )
   
   // Update page in buffer (marks as dirty)
   try await bufferManager.putPage(pageId: pageId, page: updatedPage, isDirty: true)
   
   // Unpin after writing
   try await bufferManager.unpinPage(pageId: pageId)
   ```
   
   **Why Increment LSN**:
   - LSN (Log Sequence Number) tracks page modifications
   - Incremented on each write for WAL coordination
   - Used for crash recovery (ARIES algorithm)

   4c. **Create New Buffer Page**:
   ```swift
   // Create new buffer page
   let bufferPage = BufferPage(
       pageId: pageId,
       data: data,
       lsn: 0,  // Will be updated by WAL
       isDirty: true,
       isPinned: false,
       timestamp: UInt64(Date().timeIntervalSince1970 * 1000)
   )
   
   // Put page into buffer (marks as dirty)
   try await bufferManager.putPage(pageId: pageId, page: bufferPage, isDirty: true)
   
   // Unpin after writing
   try await bufferManager.unpinPage(pageId: pageId)
   ```
   
   **Benefits of Write-Back Caching**:
   - **Delayed Writes**: Writes go to buffer, flushed later
   - **Batch Flushing**: Multiple writes can be flushed together
   - **Better Performance**: Avoids immediate disk I/O
   - **Durability**: Buffer Manager coordinates with WAL

5. **Direct Disk Write Path** (if Buffer Manager unavailable):
   ```swift
   // Write directly to disk
   try await diskManager.writePage(pageId: pageId, data: data)
   ```
   
   **Characteristics**:
   - **Immediate Write**: Every write hits disk (~5-10ms)
   - **No Caching**: No write-back benefits
   - **Simple**: No cache coordination needed

**Preconditions**:
- `data.count > 0` (non-empty data)
- Page exists (if updating, enforced by caller)
- If Buffer Manager used: Page can be pinned

**Postconditions**:
- Page written (to buffer if Buffer Manager available, to disk otherwise)
- If Buffer Manager used: Page marked dirty in buffer
- Metrics updated (I/O operations incremented, latency recorded)

**Performance Characteristics**:
- **With Buffer Manager**: ~50-100ns (in-memory operation)
- **Without Buffer Manager**: ~5-10ms (disk I/O)
- **With Flush**: +5-10ms (if flush required)

**Latency Breakdown**:

| Component | With Buffer | Without Buffer |
|-----------|-------------|----------------|
| Buffer lookup | ~10ns | N/A |
| Pin/unpin | ~50ns | N/A |
| Buffer update | ~50ns | N/A |
| Disk I/O | N/A (deferred) | ~5-10ms |
| Metrics update | ~10ns | ~10ns |
| **Total** | **~120ns** | **~5-10ms** |

**Edge Cases**:

1. **Empty Data**:
   - **Behavior**: Throws `StorageError.writeFailed`
   - **Prevention**: Validate data before calling

2. **Page Not in Buffer** (Buffer Manager path):
   - **Behavior**: Creates new buffer page
   - **Result**: Page added to cache

3. **Buffer Full** (Buffer Manager path):
   - **Behavior**: Buffer Manager handles eviction
   - **Result**: Page evicted if needed, new page cached

4. **Disk Full**:
   - **Behavior**: `DiskManager` throws error, propagates to caller
   - **Error**: `DBError.ioError`
   - **Recovery**: Handle disk space issues

5. **Write Failure**:
   - **Behavior**: Error propagates to caller
   - **State**: If Buffer Manager used, page may remain dirty in buffer
   - **Recovery**: Retry or handle error

**Example Usage**:
```swift
// Write page with Buffer Manager
let pageData = createPageData(records: records)
try await storageManager.writePage(pageId: pageId, data: pageData)

// Buffer Manager handles flushing later
// WAL coordinates durability
```

**Best Practices**:

1. **Use Buffer Manager**: Always use Buffer Manager when available
   - Write-back caching for better performance
   - Automatic flush coordination with WAL

2. **Update LSN**: If modifying pages, update LSN from WAL
   ```swift
   // Get LSN from WAL
   let lsn = try await wal.append(kind: .heapUpdate, ...)
   
   // Update page with LSN
   let updatedPage = BufferPage(..., lsn: lsn, ...)
   ```

3. **Handle Errors**: Always handle write errors
   ```swift
   do {
       try await storageManager.writePage(pageId: pageId, data: pageData)
   } catch StorageError.writeFailed {
       // Write failed
   } catch DBError.ioError {
       // Disk I/O failed
   }
   ```

**Write-Back vs Write-Through**:

**Write-Back** (current implementation):
- Writes go to buffer, flushed later
- Better performance (no immediate disk I/O)
- Requires WAL coordination for durability
- Risk: Data loss if crash before flush

**Write-Through** (alternative):
- Writes go to buffer and disk immediately
- Lower performance (always disk I/O)
- Better durability (no data loss risk)
- Not implemented (write-back is better for performance)

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

**Exponential Moving Average (EMA)** for latency tracking:

```swift
private func updateAverageLatency(_ latency: Double) {
    let alpha = 0.1  // Smoothing factor
    if metrics.averageLatency == 0.0 {
        metrics.averageLatency = latency  // Initialize
    } else {
        // Exponential moving average
        metrics.averageLatency = alpha * latency + (1.0 - alpha) * metrics.averageLatency
    }
}
```

**Why EMA**:
- **Smooth**: Reduces noise from occasional slow operations
- **Responsive**: Adapts to changes in workload
- **Simple**: O(1) calculation
- **Memory Efficient**: Only stores single average value

**Target**: < 5ms average latency for cached operations, < 10ms for direct I/O

**Typical Latency Values**:

| Operation | With Buffer (Hit) | With Buffer (Miss) | Without Buffer |
|-----------|-------------------|-------------------|----------------|
| Read | ~100ns | ~5-10ms | ~5-10ms |
| Write | ~100ns | ~5-10ms (deferred) | ~5-10ms |
| Allocate (new) | ~1ms | ~1ms | ~1ms |
| Allocate (reuse) | ~100ns | ~100ns | ~100ns |
| Deallocate | ~100ns | ~100ns | ~100ns |

**Factors Affecting Latency**:

1. **Buffer Manager Presence**:
   - With Buffer Manager: Cache hits ~100ns, misses ~5-10ms
   - Without Buffer Manager: Always ~5-10ms (disk I/O)

2. **Disk Type**:
   - **SSD**: ~5ms typical I/O latency
   - **HDD**: ~10ms typical I/O latency
   - **NVMe**: ~1ms typical I/O latency

3. **Workload Pattern**:
   - **Hot Pages**: High cache hit rate, low latency
   - **Cold Pages**: Low cache hit rate, high latency
   - **Sequential Access**: Better disk throughput, moderate latency

4. **Free Space Map Size**:
   - Small map: Fast lookup (~100ns)
   - Large map: Slower lookup (~1μs), but still acceptable

### 8.2 I/O Operations

**Tracked per operation**:
- **Read Operations**: Incremented on `readPage()`
- **Write Operations**: Incremented on `writePage()`
- **Total I/O Operations**: Sum of all I/O operations

**I/O Operation Counting**:
```swift
// On read operation
metrics.ioOperations += 1

// On write operation
metrics.ioOperations += 1
```

**Typical I/O Rates**:

| Workload | I/O Operations/sec |
|----------|-------------------|
| Read-heavy | 100 - 1,000 |
| Write-heavy | 10 - 100 |
| Mixed | 50 - 500 |

**I/O Optimization Strategies**:

1. **Buffer Manager Integration**:
   - Reduces disk I/O through caching
   - 100-1000x reduction in disk I/O for hot pages

2. **Batch Operations**:
   - Batch multiple operations together
   - Reduces per-operation overhead

3. **Prefetching**:
   - Prefetch likely-to-be-accessed pages
   - Improves cache hit rate

4. **Sequential Access**:
   - Optimize for sequential page access
   - Better disk throughput

### 8.3 Space Efficiency

**Memory Usage Breakdown** (Storage Manager overhead):

| Component | Size (1000 pages) | Percentage |
|-----------|-------------------|------------|
| `pages` Dictionary | ~64KB | 20% |
| `records` Dictionary | ~32KB | 10% |
| `freeSpaceMap` | ~16KB | 5% |
| `storageAreas` | ~8KB | 2.5% |
| `metrics` | ~64 bytes | <0.1% |
| **Total Overhead** | **~120KB** | **<1% of page data** |

**Disk Usage**:
- **Page Data**: Primary disk usage (pages * PAGE_SIZE)
- **Overhead**: Minimal (< 1% for metadata)
- **Efficiency**: > 99% space efficiency

### 8.4 Throughput

**Definition**: Operations per second (reads, writes, allocations)

**Calculation**:
```swift
throughput = totalOperations / timeElapsed
```

**Typical Throughput Values**:

| Operation Type | With Buffer | Without Buffer |
|----------------|-------------|----------------|
| Reads (cache hit) | 1,000,000 - 10,000,000 ops/sec | N/A |
| Reads (cache miss) | 100 - 1,000 ops/sec | 100 - 1,000 ops/sec |
| Writes | 1,000,000 - 10,000,000 ops/sec | 100 - 1,000 ops/sec |
| Allocations | 1,000 - 10,000 ops/sec | 1,000 - 10,000 ops/sec |

**Bottlenecks**:

1. **Disk I/O**: Primary bottleneck for cache misses (~5-10ms per operation)
2. **CPU**: Minimal impact (< 1% for typical workloads)
3. **Memory Bandwidth**: Not a bottleneck (pages are small)

### 8.5 Scalability

**Horizontal Scaling** (More Storage Managers):
- Each database instance has own Storage Manager
- No shared state between instances
- Linear scaling with instances

**Vertical Scaling** (Larger Databases):
- More pages = larger dictionaries
- O(1) lookup still efficient
- Memory scales linearly with pages

**Concurrent Operations**:
- Actor isolation serializes operations
- Multiple concurrent operations are queued
- No lock contention (zero locks)
- Throughput limited by single actor

### 8.6 Performance Targets

| Metric | Target | Acceptable | Poor |
|--------|--------|------------|------|
| Read Latency (cached) | < 0.2ms | < 1ms | > 1ms |
| Read Latency (disk) | < 10ms | < 20ms | > 20ms |
| Write Latency (cached) | < 0.2ms | < 1ms | > 1ms |
| Write Latency (disk) | < 10ms | < 20ms | > 20ms |
| Allocation Latency | < 1ms | < 5ms | > 5ms |
| Average Latency | < 5ms | < 10ms | > 10ms |
| I/O Operations/sec | > 100 | > 50 | < 50 |
| Cache Hit Rate | > 90% | > 70% | < 70% |

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

#### 11.1.1 Page Allocation Tests

**Test: Allocate New Page**:
```swift
func testAllocateNewPage() async throws {
    let storageManager = try createStorageManager()
    
    // Allocate page in data area
    let pageId = try await storageManager.allocatePage(area: .data, size: 1024)
    
    // Verify page allocated
    XCTAssertNotNil(pageId)
    let pageCount = await storageManager.getPageCount()
    XCTAssertEqual(pageCount, 1)
    
    // Verify page in storage area
    let pages = await storageManager.getPagesInArea(area: .data)
    XCTAssertEqual(pages.count, 1)
    XCTAssertTrue(pages.contains(pageId))
}
```

**Test: Reuse Existing Page**:
```swift
func testReuseExistingPage() async throws {
    let storageManager = try createStorageManager()
    
    // Allocate page
    let pageId1 = try await storageManager.allocatePage(area: .data, size: 2048)
    
    // Deallocate some space (simulate record deletion)
    // ... (would need deallocation method)
    
    // Allocate again (should reuse page if space available)
    let pageId2 = try await storageManager.allocatePage(area: .data, size: 1024)
    
    // May reuse pageId1 if free space available
    XCTAssertNotNil(pageId2)
}
```

**Test: Allocate Different Areas**:
```swift
func testAllocateDifferentAreas() async throws {
    let storageManager = try createStorageManager()
    
    // Allocate pages in different areas
    let dataPageId = try await storageManager.allocatePage(area: .data, size: 1024)
    let indexPageId = try await storageManager.allocatePage(area: .index, size: 2048)
    let tempPageId = try await storageManager.allocatePage(area: .temp, size: 512)
    
    // Verify pages in correct areas
    let dataPages = await storageManager.getPagesInArea(area: .data)
    XCTAssertTrue(dataPages.contains(dataPageId))
    
    let indexPages = await storageManager.getPagesInArea(area: .index)
    XCTAssertTrue(indexPages.contains(indexPageId))
    
    let tempPages = await storageManager.getPagesInArea(area: .temp)
    XCTAssertTrue(tempPages.contains(tempPageId))
}
```

#### 11.1.2 Page Deallocation Tests

**Test: Deallocate Page**:
```swift
func testDeallocatePage() async throws {
    let storageManager = try createStorageManager()
    
    // Allocate page
    let pageId = try await storageManager.allocatePage(area: .data, size: 1024)
    let initialCount = await storageManager.getPageCount()
    XCTAssertEqual(initialCount, 1)
    
    // Deallocate page
    try await storageManager.deallocatePage(pageId: pageId)
    
    // Verify page deallocated
    let finalCount = await storageManager.getPageCount()
    XCTAssertEqual(finalCount, 0)
    
    // Verify page removed from area
    let pages = await storageManager.getPagesInArea(area: .data)
    XCTAssertFalse(pages.contains(pageId))
}
```

#### 11.1.3 Read/Write Tests

**Test: Read Page with Buffer Manager**:
```swift
func testReadPageWithBufferManager() async throws {
    let bufferManager = try createBufferManager()
    let storageManager = try createStorageManager(bufferManager: bufferManager)
    
    // Allocate and write page
    let pageId = try await storageManager.allocatePage(area: .data, size: 4096)
    let testData = Data(repeating: 0x42, count: 4096)
    try await storageManager.writePage(pageId: pageId, data: testData)
    
    // Read page
    let readData = try await storageManager.readPage(pageId: pageId)
    
    // Verify data matches
    XCTAssertEqual(readData, testData)
}
```

**Test: Read Page without Buffer Manager**:
```swift
func testReadPageWithoutBufferManager() async throws {
    let storageManager = try createStorageManager(bufferManager: nil)
    
    // Allocate and write page
    let pageId = try await storageManager.allocatePage(area: .data, size: 4096)
    let testData = Data(repeating: 0x42, count: 4096)
    try await storageManager.writePage(pageId: pageId, data: testData)
    
    // Read page (direct disk I/O)
    let readData = try await storageManager.readPage(pageId: pageId)
    
    // Verify data matches
    XCTAssertEqual(readData, testData)
}
```

#### 11.1.4 Space Management Tests

**Test: Free Space Tracking**:
```swift
func testFreeSpaceTracking() async throws {
    let storageManager = try createStorageManager()
    
    // Allocate page
    let pageId = try await storageManager.allocatePage(area: .data, size: 2048)
    
    // Verify free space tracked
    let freeSpace = await storageManager.getFreeSpace(pageId: pageId)
    let pageSize = 4096  // Typical PAGE_SIZE
    XCTAssertEqual(freeSpace, pageSize - 2048)
}
```

#### 11.1.5 Invariant Verification Tests

**Test: Data Integrity Invariant**:
```swift
func testDataIntegrityInvariant() async throws {
    let storageManager = try createStorageManager()
    
    // Perform operations
    let pageId = try await storageManager.allocatePage(area: .data, size: 1024)
    // ... (add records, etc.)
    
    // Verify invariant holds
    let isValid = await storageManager.checkDataIntegrityInvariant()
    XCTAssertTrue(isValid)
}
```

**Test: Space Management Invariant**:
```swift
func testSpaceManagementInvariant() async throws {
    let storageManager = try createStorageManager()
    
    // Perform allocations
    for _ in 0..<100 {
        _ = try await storageManager.allocatePage(area: .data, size: 1024)
    }
    
    // Verify invariant holds
    let isValid = await storageManager.checkSpaceManagementInvariant()
    XCTAssertTrue(isValid)
}
```

### 11.2 Integration Tests

#### 11.2.1 Storage + Buffer Manager Integration

**Test: Cache Hit Scenario**:
```swift
func testCacheHitScenario() async throws {
    let bufferManager = try createBufferManager()
    let storageManager = try createStorageManager(bufferManager: bufferManager)
    
    // Allocate and write page
    let pageId = try await storageManager.allocatePage(area: .data, size: 4096)
    let testData = Data(repeating: 0x42, count: 4096)
    try await storageManager.writePage(pageId: pageId, data: testData)
    
    // Read page multiple times (should hit cache)
    for _ in 0..<10 {
        let readData = try await storageManager.readPage(pageId: pageId)
        XCTAssertEqual(readData, testData)
    }
    
    // Verify cache hit rate high
    let bufferMetrics = await bufferManager.getBufferMetrics()
    XCTAssertGreaterThan(bufferMetrics.hitRate, 0.9)
}
```

**Test: Cache Miss Scenario**:
```swift
func testCacheMissScenario() async throws {
    let bufferManager = try createBufferManager(poolSize: 10)  // Small pool
    let storageManager = try createStorageManager(bufferManager: bufferManager)
    
    // Allocate many pages (more than pool size)
    var pageIds: [PageID] = []
    for _ in 0..<20 {
        let pageId = try await storageManager.allocatePage(area: .data, size: 4096)
        pageIds.append(pageId)
    }
    
    // Read first page (may be evicted)
    _ = try await storageManager.readPage(pageId: pageIds[0])
    
    // Verify cache miss rate increases
    let bufferMetrics = await bufferManager.getBufferMetrics()
    // (Expected behavior: some cache misses)
}
```

#### 11.2.2 Storage + WAL Coordination

**Test: WAL Before Data**:
```swift
func testWALBeforeData() async throws {
    let wal = try createWAL()
    let bufferManager = try createBufferManager()
    let storageManager = try createStorageManager(bufferManager: bufferManager)
    
    // Write WAL record
    let lsn = try await wal.append(kind: .heapUpdate, txID: 1, pageID: 1, ...)
    
    // Update page with LSN
    let pageId = try await storageManager.allocatePage(area: .data, size: 4096)
    let pageData = createPageData(lsn: lsn)
    try await storageManager.writePage(pageId: pageId, data: pageData)
    
    // Flush WAL
    try await wal.flush()
    
    // Update buffer manager flushedLSN
    await bufferManager.updateFlushedLSN(await wal.getFlushedLSN())
    
    // Now page can be flushed
    try await bufferManager.flushPage(pageId: pageId)
    
    // Verify page flushed successfully
    let bufferMetrics = await bufferManager.getBufferMetrics()
    XCTAssertEqual(bufferMetrics.dirtyFrames, 0)
}
```

#### 11.2.3 Concurrent Access Tests

**Test: Concurrent Reads**:
```swift
func testConcurrentReads() async throws {
    let storageManager = try createStorageManager()
    
    // Allocate and write page
    let pageId = try await storageManager.allocatePage(area: .data, size: 4096)
    let testData = Data(repeating: 0x42, count: 4096)
    try await storageManager.writePage(pageId: pageId, data: testData)
    
    // Concurrent reads
    await withTaskGroup(of: Data.self) { group in
        for _ in 0..<100 {
            group.addTask {
                try! await storageManager.readPage(pageId: pageId)
            }
        }
        
        // Verify all reads succeed
        var count = 0
        for await data in group {
            XCTAssertEqual(data, testData)
            count += 1
        }
        XCTAssertEqual(count, 100)
    }
}
```

#### 11.2.4 Error Scenario Tests

**Test: Page Not Found**:
```swift
func testPageNotFound() async throws {
    let storageManager = try createStorageManager()
    
    // Try to read non-existent page
    do {
        _ = try await storageManager.readPage(pageId: PageID(9999))
        XCTFail("Should have thrown error")
    } catch StorageError.pageNotFound {
        // Expected
    }
}
```

**Test: Disk Full**:
```swift
func testDiskFull() async throws {
    // Create storage manager with limited disk
    let diskManager = try createLimitedDiskManager(maxPages: 10)
    let storageManager = try createStorageManager(diskManager: diskManager)
    
    // Allocate until disk full
    var pageIds: [PageID] = []
    do {
        for _ in 0..<20 {
            let pageId = try await storageManager.allocatePage(area: .data, size: 4096)
            pageIds.append(pageId)
        }
        XCTFail("Should have thrown error")
    } catch StorageError.allocationFailed {
        // Expected when disk full
    }
}
```

### 11.3 Performance Tests

#### 11.3.1 Latency Measurements

**Test: Read Latency with Buffer Manager**:
```swift
func testReadLatencyWithBufferManager() async throws {
    let bufferManager = try createBufferManager()
    let storageManager = try createStorageManager(bufferManager: bufferManager)
    
    // Allocate and write page
    let pageId = try await storageManager.allocatePage(area: .data, size: 4096)
    let testData = Data(repeating: 0x42, count: 4096)
    try await storageManager.writePage(pageId: pageId, data: testData)
    
    // Measure read latency
    var latencies: [Double] = []
    for _ in 0..<1000 {
        let start = Date()
        _ = try await storageManager.readPage(pageId: pageId)
        let latency = Date().timeIntervalSince(start) * 1000  // ms
        latencies.append(latency)
    }
    
    // Calculate statistics
    let averageLatency = latencies.reduce(0, +) / Double(latencies.count)
    print("Average read latency: \(averageLatency)ms")
    
    // Verify latency within target (< 1ms for cache hits)
    XCTAssertLessThan(averageLatency, 1.0)
}
```

#### 11.3.2 Throughput Benchmarks

**Test: Write Throughput**:
```swift
func testWriteThroughput() async throws {
    let bufferManager = try createBufferManager()
    let storageManager = try createStorageManager(bufferManager: bufferManager)
    
    // Measure write throughput
    let start = Date()
    var pageIds: [PageID] = []
    for i in 0..<1000 {
        let pageId = try await storageManager.allocatePage(area: .data, size: 4096)
        let testData = Data(repeating: UInt8(i % 256), count: 4096)
        try await storageManager.writePage(pageId: pageId, data: testData)
        pageIds.append(pageId)
    }
    let elapsed = Date().timeIntervalSince(start)
    
    let throughput = Double(1000) / elapsed
    print("Write throughput: \(throughput) ops/sec")
    
    // Verify throughput > target (> 1000 ops/sec)
    XCTAssertGreaterThan(throughput, 1000.0)
}
```

#### 11.3.3 Cache Effectiveness Tests

**Test: Cache Hit Rate**:
```swift
func testCacheHitRate() async throws {
    let bufferManager = try createBufferManager(poolSize: 100)
    let storageManager = try createStorageManager(bufferManager: bufferManager)
    
    // Allocate pages (fit in cache)
    var pageIds: [PageID] = []
    for _ in 0..<50 {
        let pageId = try await storageManager.allocatePage(area: .data, size: 4096)
        let testData = Data(repeating: 0x42, count: 4096)
        try await storageManager.writePage(pageId: pageId, data: testData)
        pageIds.append(pageId)
    }
    
    // Read pages multiple times (should hit cache)
    for _ in 0..<10 {
        for pageId in pageIds {
            _ = try await storageManager.readPage(pageId: pageId)
        }
    }
    
    // Verify high cache hit rate
    let bufferMetrics = await bufferManager.getBufferMetrics()
    print("Cache hit rate: \(bufferMetrics.hitRate)")
    XCTAssertGreaterThan(bufferMetrics.hitRate, 0.95)
}
```

### 11.4 Stress Tests

**Test: High Concurrency**:
```swift
func testHighConcurrency() async throws {
    let storageManager = try createStorageManager()
    
    // High concurrency operations
    await withTaskGroup(of: Void.self) { group in
        for i in 0..<1000 {
            group.addTask {
                do {
                    let pageId = try await storageManager.allocatePage(area: .data, size: 4096)
                    let testData = Data(repeating: UInt8(i % 256), count: 4096)
                    try await storageManager.writePage(pageId: pageId, data: testData)
                    _ = try await storageManager.readPage(pageId: pageId)
                } catch {
                    XCTFail("Operation failed: \(error)")
                }
            }
        }
    }
    
    // Verify invariants still hold
    let isValid = await storageManager.checkDataIntegrityInvariant()
    XCTAssertTrue(isValid)
}
```

**Test: Long Running Operations**:
```swift
func testLongRunningOperations() async throws {
    let storageManager = try createStorageManager()
    
    // Run operations for extended period
    let start = Date()
    var operations = 0
    while Date().timeIntervalSince(start) < 10.0 {  // 10 seconds
        let pageId = try await storageManager.allocatePage(area: .data, size: 4096)
        let testData = Data(repeating: 0x42, count: 4096)
        try await storageManager.writePage(pageId: pageId, data: testData)
        _ = try await storageManager.readPage(pageId: pageId)
        operations += 1
    }
    
    print("Operations completed: \(operations)")
    XCTAssertGreaterThan(operations, 1000)
}
```

## 12. References

- **RFC 0004**: Buffer Manager
- **RFC 0005**: Write-Ahead Logging
- **TLA+ Spec**: `spec/Storage.tla`

---

**Next**: See RFC 0019 for Transaction Manager details.

