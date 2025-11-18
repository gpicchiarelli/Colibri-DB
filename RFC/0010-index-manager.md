# RFC 0010: Index Manager

**Status**: Standards Track  
**Author**: ColibrìDB Team  
**Date**: 2025-11-18  
**TLA+ Spec**: `spec/Index.tla`

## Abstract

This RFC defines the Index Manager component, responsible for creating, managing, and querying database indexes to enable efficient data access patterns and improve query performance.

## 1. Introduction

The Index Manager provides high-level index operations, coordinating with the Storage Manager for persistence and with the Buffer Manager for efficient page caching. It manages index structures (B+Tree, Hash, ART, LSM) and tracks index metadata and performance metrics.

### 1.1 Purpose and Goals

The primary goals of the Index Manager are:

1. **Index Creation**: Create indexes on tables and columns
2. **Index Maintenance**: Maintain index consistency during data modifications
3. **Query Performance**: Provide efficient lookup and range scan operations
4. **Multiple Index Types**: Support different index types (B+Tree, Hash, etc.)
5. **Performance Monitoring**: Track index performance metrics

### 1.2 Problem Statement

Database systems need to:

- **Fast Lookups**: Find data quickly by key
- **Range Scans**: Efficiently scan ranges of keys
- **Multiple Indexes**: Support multiple indexes per table
- **Index Types**: Different index types for different use cases
- **Maintenance**: Keep indexes consistent during data modifications

The Index Manager solves these challenges by:

- Providing high-level index creation/drop APIs
- Maintaining index structures automatically
- Integrating with Buffer Manager for efficient caching
- Supporting multiple index types (B+Tree, Hash, ART, LSM)
- Tracking performance metrics for optimization

### 1.3 Key Concepts

**Index**: Data structure for efficient data access:
- **Primary Key**: Unique index on primary key
- **Secondary Index**: Non-unique index on other columns
- **Unique Index**: Index enforcing uniqueness constraint

**Index Type**: Different index structures:
- **B+Tree**: Balanced tree for range queries
- **Hash**: Hash table for equality queries
- **ART**: Adaptive Radix Tree for string keys
- **LSM**: Log-Structured Merge Tree for write-heavy workloads

**Index Entry**: Entry in index:
- **Key**: Search key
- **Value**: Pointer to data (PageID, Offset)
- **Metadata**: Timestamp, deletion flag

**Index Metadata**: Index configuration:
- **Index Type**: B+Tree, Hash, etc.
- **Unique**: Whether index enforces uniqueness
- **Columns**: Columns indexed
- **Properties**: Index-specific properties

**Index Metrics**: Performance metrics:
- **Hit Rate**: Cache hit rate
- **Miss Rate**: Cache miss rate
- **Scan Count**: Number of scans
- **Insert/Update/Delete Counts**: Modification counts

### 1.4 Relationship to Other Components

```
Index Manager
    ↓ uses
Storage Manager
    ↓ uses
Buffer Manager (optional)
    ↓ uses
Disk Manager
    ↓ performs
Physical I/O
```

**Index Manager → Storage Manager**:
- Allocates pages for index structures
- Reads/writes index pages
- Manages index persistence

**Index Manager → Buffer Manager**:
- Uses buffer cache for index pages
- Prefetches pages for range scans
- Ensures pages in cache for lookups

**Index Manager ← Query Optimizer**:
- Query optimizer uses indexes for query planning
- Chooses optimal index for queries
- Estimates index scan costs

## 2. Design Principles

### 2.1 Buffer Manager Integration

The Index Manager integrates with the Buffer Manager for efficient page caching.

#### 2.1.1 Cache-First Strategy

**When Buffer Manager is Available**:

**Lookup Operations**:
```swift
// IndexManager.lookupEntry() with BufferManager
if entry.pageId > 0 {
    // Prefetch page into buffer cache
    _ = await bufferManager.getPageQuery(pageId: PageID(entry.pageId))
}
```

**Benefits**:
- **Cache Hit**: ~100ns if page in buffer (vs ~5-10ms disk read)
- **Prefetching**: Prefetches pages for found entries
- **Automatic Caching**: Buffer Manager handles cache management

**Range Scan Operations**:
```swift
// IndexManager.rangeScan() with BufferManager
let entries = index.entries.filter { ... }

// Prefetch pages for found entries
let pageIds = Set(entries.map { PageID($0.pageId) })
for pageId in pageIds {
    // Prefetch page into buffer cache
    _ = await bufferManager.getPageQuery(pageId: pageId)
}
```

**Benefits**:
- **Prefetching**: Prefetches pages for range scan results
- **Better Performance**: Pages ready for sequential access
- **Cache Efficiency**: Improves cache hit rate

### 2.2 Index Types

Organizes indexes by type for efficient management.

#### 2.2.1 B+Tree Index

**Purpose**: Balanced tree for range queries

**Characteristics**:
- **Range Queries**: Efficient range scans
- **Sorted**: Keys sorted in order
- **Balanced**: O(log n) lookup complexity

**Use Cases**:
- Primary keys
- Secondary keys with range queries
- Ordered data access

#### 2.2.2 Hash Index

**Purpose**: Hash table for equality queries

**Characteristics**:
- **Equality Queries**: O(1) lookup complexity
- **No Range Queries**: Not suitable for range scans
- **Fast**: Very fast for exact matches

**Use Cases**:
- Primary keys (if no range queries)
- Equality queries only
- Fast lookups

#### 2.2.3 ART Index

**Purpose**: Adaptive Radix Tree for string keys

**Characteristics**:
- **String Keys**: Optimized for string keys
- **Prefix Compression**: Efficient memory usage
- **Range Queries**: Supports range scans

**Use Cases**:
- String primary keys
- Text search
- Prefix queries

#### 2.2.4 LSM Index

**Purpose**: Log-Structured Merge Tree for write-heavy workloads

**Characteristics**:
- **Write-Optimized**: Optimized for writes
- **Append-Only**: Write-append operations
- **Compaction**: Periodic compaction

**Use Cases**:
- Write-heavy workloads
- Append-only workloads
- High write throughput

### 2.3 Index Maintenance

Tracks index consistency during data modifications.

#### 2.3.1 Insert Maintenance

**On Insert**:
```swift
// Insert entry into index
index.entries.append(entry)

// If entry has pageId, ensure page is in buffer
if entry.pageId > 0 {
    _ = await bufferManager.getPageQuery(pageId: PageID(entry.pageId))
}
```

#### 2.3.2 Update Maintenance

**On Update**:
```swift
// Update entry in index
if let index = indexes[indexId] {
    // Find and update entry
    if let entryIndex = index.entries.firstIndex(where: { $0.key == key }) {
        index.entries[entryIndex] = updatedEntry
    }
}
```

#### 2.3.3 Delete Maintenance

**On Delete**:
```swift
// Mark entry as deleted
if let entryIndex = index.entries.firstIndex(where: { $0.key == key }) {
    index.entries[entryIndex].isDeleted = true
}
```

### 2.4 Apple-First Architecture

#### 2.4.1 Swift Actor Model

**Why Actors**: Thread-safe index operations without explicit locking.

```swift
public actor IndexManagerActor {
    // All state isolated within actor
    private var indexes: [IndexID: Index] = [:]
    private var indexMetadata: [IndexID: IndexMetadata] = [:]
    
    // Methods automatically synchronized
    public func createIndex(metadata: IndexMetadata) async throws -> IndexID {
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
// Non-blocking index lookup
public func lookupEntry(indexId: IndexID, key: String) async throws -> [IndexEntry] {
    // Suspends task, allows other work
    let entries = performLookup(indexId: indexId, key: key)
    // Resumes when lookup completes
    return entries
}
```

**Benefits**:
- **Non-Blocking**: Threads not blocked on I/O
- **Concurrent**: Supports thousands of concurrent operations
- **Structured**: Clear error handling and control flow

#### 2.4.3 Value Types

**Why Value Types**: Immutable data structures are thread-safe by default.

```swift
public struct IndexEntry: Sendable {
    public let entryId: String
    public let indexId: IndexID
    public let key: String
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
IndexManagerActor (Swift Actor)
├── indexes: [IndexID -> Index]
│   ├── Purpose: Index structures
│   ├── Type: Dictionary mapping IndexID to Index
│   ├── Lifetime: Indexes exist until dropped
│   └── Access: O(1) hash table lookup
│
├── indexMetadata: [IndexID -> IndexMetadata]
│   ├── Purpose: Index configuration
│   ├── Type: Dictionary mapping IndexID to metadata
│   ├── Updates: On index creation/drop
│   └── Use: Index type, uniqueness, columns
│
├── indexMetrics: [IndexID -> IndexMetrics]
│   ├── Purpose: Performance monitoring
│   ├── Type: Dictionary mapping IndexID to metrics
│   ├── Updates: On each operation
│   └── Use: Hit rate, miss rate, operation counts
│
├── indexCache: [IndexID -> [IndexEntry]]
│   ├── Purpose: In-memory index cache
│   ├── Type: Dictionary mapping IndexID to entry list
│   ├── Lifetime: Exists while index in memory
│   └── Use: Fast lookup without disk I/O
│
├── storageManager: StorageManager
│   ├── Purpose: Page allocation and I/O
│   ├── Used: For index persistence
│   └── Operations: allocatePage, readPage, writePage
│
└── bufferManager: BufferManager
    ├── Purpose: Page caching
    ├── Used: For efficient page access
    └── Operations: getPageQuery, prefetch pages
```

### 3.2 Data Flow Diagrams

#### 3.2.1 Index Creation Flow

```
┌──────────────────┐
│ createIndex(     │
│   metadata)      │
└──────┬───────────┘
       │
       ▼
   ┌───────────────┐
   │Allocate Index │
   │Pages          │
   └───┬───────────┘
       │
       ▼
   ┌───────────────┐
   │Create Index   │
   │Structure      │
   └───┬───────────┘
       │
       ▼
   ┌───────────────┐
   │Store          │
   │Metadata       │
   └───┬───────────┘
       │
       ▼
   ┌───────────────┐
   │Initialize     │
   │Metrics        │
   └───┬───────────┘
       │
       ▼
   ┌───────────────┐
   │Return         │
   │IndexID        │
   └───────────────┘
```

#### 3.2.2 Index Lookup Flow

```
┌──────────────────┐
│ lookupEntry(     │
│   indexId, key)  │
└──────┬───────────┘
       │
       ▼
   ┌───────────────┐
   │Get Index      │
   └───┬───────────┘
       │
       ▼
   ┌───────────────┐
   │Lookup Entry   │
   │in Index       │
   └───┬───────────┘
       │
       ▼
   ┌───────────────┐
   │Prefetch Pages │
   │for Entries    │
   └───┬───────────┘
       │
       ▼
   ┌───────────────┐
   │Update         │
   │Metrics        │
   └───┬───────────┘
       │
       ▼
   ┌───────────────┐
   │Return         │
   │Entries        │
   └───────────────┘
```

#### 3.2.3 Index Range Scan Flow

```
┌──────────────────┐
│ rangeScan(    │
│   indexId, start,   │
│   end)           │
└──────┬───────────┘
       │
       ▼
   ┌───────────────┐
   │Get Index      │
   └───┬───────────┘
       │
       ▼
   ┌───────────────┐
   │Filter Entries │
   │by Range       │
   └───┬───────────┘
       │
       ▼
   ┌───────────────┐
   │Prefetch Pages │
   │for Entries    │
   └───┬───────────┘
       │
       ▼
   ┌───────────────┐
   │Update         │
   │Metrics        │
   └───┬───────────┘
       │
       ▼
   ┌───────────────┐
   │Return         │
   │Entries        │
   └───────────────┘
```

### 3.3 Dependencies

- **Storage Manager**: Page allocation and I/O operations
- **Buffer Manager**: Page caching for performance

## 4. State Variables (TLA+ Mapping)

| Swift Variable | TLA+ Variable | Type | Description |
|----------------|---------------|------|-------------|
| `indexes` | `indexes` | `[IndexID -> Index]` | Index structures |
| `indexMetadata` | `indexMetadata` | `[IndexID -> IndexMetadata]` | Index configuration |
| `indexMetrics` | `indexMetrics` | `[IndexID -> IndexMetrics]` | Performance metrics |
| `indexCache` | `indexCache` | `[IndexID -> [IndexEntry]]` | In-memory cache |

## 5. API Specification

### 5.1 Initialization

```swift
public actor IndexManagerActor {
    public init(
        storageManager: StorageManager,
        bufferManager: BufferManager
    )
}
```

**Parameters**:
- `storageManager`: Storage manager for page I/O
- `bufferManager`: Buffer manager for page caching

### 5.2 Index Operations

#### 5.2.1 Create Index

```swift
public func createIndex(metadata: IndexMetadata) async throws -> IndexID
```

**TLA+ Action**: `CreateIndex(metadata)`

**Behavior**: Detailed step-by-step execution

1. **Validate Metadata**:
   ```swift
   guard !metadata.indexName.isEmpty else {
       throw IndexError.invalidMetadata("Index name cannot be empty")
   }
   ```
   - Index name must be non-empty
   - Index type must be valid

2. **Allocate Index Pages**:
   ```swift
   let pageId = try await storageManager.allocatePage(area: .index, size: PAGE_SIZE)
   ```
   - **Index Area**: Allocate pages in index area
   - **Page Size**: Standard page size (4KB-16KB)

3. **Create Index Structure**:
   ```swift
   let index = Index(
       indexId: IndexID(0), // Generate new ID
       indexType: metadata.indexType,
       entries: [],
       isUnique: metadata.unique,
       isPrimary: false,
       isClustered: false,
       fillFactor: 0.8,
       lastModified: UInt64(Date().timeIntervalSince1970 * 1000)
   )
   ```
   - **Index Type**: B+Tree, Hash, ART, LSM
   - **Unique**: Whether index enforces uniqueness
   - **Entries**: Empty initially (will be populated)

4. **Generate Index ID**:
   ```swift
   let indexId = generateIndexID()
   index.indexId = indexId
   ```
   - **Unique ID**: Monotonically increasing sequence
   - **Atomic**: Single actor ensures no race conditions

5. **Store Index**:
   ```swift
   indexes[indexId] = index
   indexMetadata[indexId] = metadata
   ```
   - **Index Map**: Store index structure
   - **Metadata Map**: Store index configuration

6. **Initialize Metrics**:
   ```swift
   indexMetrics[indexId] = IndexMetrics(
       indexId: indexId,
       entryCount: 0,
       size: 0,
       height: 0,
       leafCount: 0,
       internalCount: 0,
       averageKeySize: 0.0,
       averageValueSize: 0.0,
       hitRate: 0.0,
       missRate: 0.0,
       scanCount: 0,
       insertCount: 0,
       updateCount: 0,
       deleteCount: 0
   )
   ```
   - **Initial State**: All metrics initialized to zero
   - **Tracking**: Metrics updated on each operation

7. **Initialize Cache**:
   ```swift
   indexCache[indexId] = []
   ```
   - **In-Memory Cache**: Empty initially
   - **Cache**: Will be populated on lookups

8. **Return Index ID**:
   ```swift
   return indexId
   ```

**Preconditions**:
- `metadata.indexName` is non-empty
- `metadata.indexType` is valid
- Storage manager available

**Postconditions**:
- Index created (`indexes[indexId] != nil`)
- Index metadata stored (`indexMetadata[indexId] != nil`)
- Index metrics initialized (`indexMetrics[indexId] != nil`)
- Index pages allocated

**Returns**: Index ID (`IndexID`)

**Performance Characteristics**:
- **Create**: ~1ms (page allocation dominates)
- **Scalable**: O(1) operation

**Example Usage**:
```swift
// Create B+Tree index
let metadata = IndexMetadata(
    indexName: "users_email_idx",
    indexType: .bTree,
    unique: true,
    columns: ["email"]
)
let indexId = try await indexManager.createIndex(metadata: metadata)
```

**Edge Cases**:

1. **Duplicate Index Name**:
   - **Behavior**: Throws `IndexError.duplicateIndex`
   - **Prevention**: Check for existing index with same name

2. **Invalid Index Type**:
   - **Behavior**: Throws `IndexError.invalidIndexType`
   - **Prevention**: Validate index type before creation

3. **Storage Allocation Failure**:
   - **Behavior**: `StorageManager` throws error, propagates to caller
   - **Recovery**: Handle disk space issues

#### 5.2.2 Drop Index

```swift
public func dropIndex(indexId: IndexID) async throws
```

**TLA+ Action**: `DropIndex(indexId)`

**Behavior**: Detailed step-by-step execution

1. **Validate Index**:
   ```swift
   guard indexes[indexId] != nil else {
       throw IndexError.indexNotFound
   }
   ```
   - Index must exist
   - Cannot drop non-existent index

2. **Deallocate Index Pages**:
   ```swift
   // Get index pages
   let index = indexes[indexId]!
   // Deallocate pages (implementation depends on index structure)
   try await storageManager.deallocatePage(pageId: index.rootPageId)
   ```
   - **Page Cleanup**: Deallocate all index pages
   - **Memory**: Free memory used by index

3. **Remove Index**:
   ```swift
   indexes.removeValue(forKey: indexId)
   indexMetadata.removeValue(forKey: indexId)
   indexMetrics.removeValue(forKey: indexId)
   indexCache.removeValue(forKey: indexId)
   ```
   - **Cleanup**: Remove index from all maps
   - **Memory**: Free memory used by index

**Preconditions**:
- Index exists (`indexes[indexId] != nil`)

**Postconditions**:
- Index dropped (`indexes[indexId] == nil`)
- Index metadata removed (`indexMetadata[indexId] == nil`)
- Index metrics removed (`indexMetrics[indexId] == nil`)
- Index pages deallocated

**Performance Characteristics**:
- **Drop**: ~1ms (page deallocation dominates)
- **Scalable**: O(1) operation

#### 5.2.3 Insert Entry

```swift
public func insertEntry(indexId: IndexID, entry: IndexEntry) async throws
```

**TLA+ Action**: `InsertEntry(indexId, entry)`

**Behavior**: Detailed step-by-step execution

1. **Validate Index**:
   ```swift
   guard var index = indexes[indexId] else {
       throw IndexError.indexNotFound
   }
   ```
   - Index must exist
   - Cannot insert into non-existent index

2. **Check Uniqueness** (if unique index):
   ```swift
   if index.isUnique {
       let existingEntry = index.entries.first { $0.key == entry.key && !$0.isDeleted }
       if existingEntry != nil {
           throw IndexError.duplicateKey
       }
   }
   ```
   - **Unique Constraint**: Check for duplicate keys
   - **Conflict**: Throw error if duplicate found

3. **Insert Entry**:
   ```swift
   index.entries.append(entry)
   index.lastModified = UInt64(Date().timeIntervalSince1970 * 1000)
   indexes[indexId] = index
   ```
   - **Entry Addition**: Add entry to index
   - **Timestamp**: Update last modified time

4. **Update Cache**:
   ```swift
   if indexCache[indexId] == nil {
       indexCache[indexId] = []
   }
   indexCache[indexId]?.append(entry)
   ```
   - **Cache Update**: Add entry to cache
   - **Performance**: Improves lookup performance

5. **Prefetch Page** (if entry has pageId):
   ```swift
   if entry.pageId > 0 {
       // Touch the page to ensure it's in buffer cache
       _ = await bufferManager.getPageQuery(pageId: PageID(entry.pageId))
   }
   ```
   - **Buffer Integration**: Ensure page in buffer cache
   - **Performance**: Prefetches page for future access

6. **Update Metrics**:
   ```swift
   updateMetrics(indexId: indexId)
   // Increments: entryCount, insertCount
   ```
   - **Metrics Update**: Update performance metrics
   - **Tracking**: Tracks index usage

**Preconditions**:
- Index exists (`indexes[indexId] != nil`)
- Entry key is valid (non-empty)
- If unique index: key not already exists

**Postconditions**:
- Entry inserted (`index.entries.contains(entry)`)
- Cache updated (`indexCache[indexId]?.contains(entry) == true`)
- Metrics updated (entryCount, insertCount incremented)

**Performance Characteristics**:
- **Insert**: ~100ns-1μs (depends on index type)
  - B+Tree: ~1μs (tree traversal)
  - Hash: ~100ns (hash lookup)
- **Scalable**: O(log n) for B+Tree, O(1) for Hash

**Example Usage**:
```swift
// Insert entry into index
let entry = IndexEntry(
    entryId: UUID().uuidString,
    indexId: indexId,
    key: "user@example.com",
    value: "user123",
    pageId: 12345,
    offset: 1024,
    isDeleted: false,
    timestamp: UInt64(Date().timeIntervalSince1970 * 1000)
)
try await indexManager.insertEntry(indexId: indexId, entry: entry)
```

**Edge Cases**:

1. **Index Not Found**:
   - **Behavior**: Throws `IndexError.indexNotFound`
   - **Prevention**: Ensure index exists before insert

2. **Duplicate Key** (unique index):
   - **Behavior**: Throws `IndexError.duplicateKey`
   - **Prevention**: Check uniqueness before insert

3. **Invalid Entry**:
   - **Behavior**: Throws `IndexError.invalidEntry`
   - **Prevention**: Validate entry before insert

#### 5.2.4 Lookup Entry

```swift
public func lookupEntry(indexId: IndexID, key: String) async throws -> [IndexEntry]
```

**TLA+ Action**: `LookupEntry(indexId, key)`

**Behavior**: Detailed step-by-step execution

1. **Validate Index**:
   ```swift
   guard let index = indexes[indexId] else {
       throw IndexError.indexNotFound
   }
   ```
   - Index must exist
   - Cannot lookup in non-existent index

2. **Lookup Entries**:
   ```swift
   let entries = index.entries.filter { $0.key == key && !$0.isDeleted }
   ```
   - **Key Match**: Find entries matching key
   - **Not Deleted**: Exclude deleted entries
   - **Multiple Entries**: Can return multiple entries (non-unique index)

3. **Prefetch Pages**:
   ```swift
   let pageIds = Set(entries.map { PageID($0.pageId) })
   for pageId in pageIds {
       // Prefetch page into buffer cache
       _ = await bufferManager.getPageQuery(pageId: pageId)
   }
   ```
   - **Prefetching**: Prefetch pages for found entries
   - **Performance**: Improves subsequent access
   - **Buffer Integration**: Uses Buffer Manager for caching

4. **Update Metrics**:
   ```swift
   updateMetrics(indexId: indexId)
   // Updates: hitRate, missRate, scanCount
   ```
   - **Metrics Update**: Update performance metrics
   - **Tracking**: Tracks index usage

5. **Return Entries**:
   ```swift
   return entries
   ```

**Preconditions**:
- Index exists (`indexes[indexId] != nil`)
- Key is valid (non-empty)

**Postconditions**:
- Entries returned (may be empty if key not found)
- Pages prefetched (if entries found)
- Metrics updated (hitRate, missRate, scanCount)

**Returns**: Array of `IndexEntry` (may be empty)

**Performance Characteristics**:
- **Lookup**: ~100ns-1μs (depends on index type)
  - B+Tree: ~1μs (tree traversal)
  - Hash: ~100ns (hash lookup)
- **Scalable**: O(log n) for B+Tree, O(1) for Hash

**Example Usage**:
```swift
// Lookup entries by key
let entries = try await indexManager.lookupEntry(indexId: indexId, key: "user@example.com")

// Use entries to access data
for entry in entries {
    let pageData = try await storageManager.readPage(pageId: PageID(entry.pageId))
    // Access data at entry.offset
}
```

**Edge Cases**:

1. **Index Not Found**:
   - **Behavior**: Throws `IndexError.indexNotFound`
   - **Prevention**: Ensure index exists before lookup

2. **Key Not Found**:
   - **Behavior**: Returns empty array
   - **Correctness**: Valid behavior (key may not exist)

3. **Multiple Entries** (non-unique index):
   - **Behavior**: Returns all entries matching key
   - **Correctness**: Valid behavior for non-unique indexes

#### 5.2.5 Range Scan

```swift
public func rangeScan(indexId: IndexID, startKey: String, endKey: String) async throws -> [IndexEntry]
```

**TLA+ Action**: `RangeScan(indexId, startKey, endKey)`

**Behavior**: Detailed step-by-step execution

1. **Validate Index**:
   ```swift
   guard let index = indexes[indexId] else {
       throw IndexError.indexNotFound
   }
   ```
   - Index must exist
   - Cannot scan non-existent index

2. **Filter Entries by Range**:
   ```swift
   let entries = index.entries.filter { entry in
       entry.key >= startKey &&
       entry.key <= endKey &&
       !entry.isDeleted
   }
   ```
   - **Range Filter**: Filter entries in range
   - **Not Deleted**: Exclude deleted entries
   - **Sorted**: Entries should be sorted (for B+Tree)

3. **Sort Entries** (if not sorted):
   ```swift
   let sortedEntries = entries.sorted { $0.key < $1.key }
   ```
   - **Ordering**: Ensure entries are sorted
   - **Range Scan**: Efficient range scan requires sorted entries

4. **Prefetch Pages**:
   ```swift
   let pageIds = Set(sortedEntries.map { PageID($0.pageId) })
   for pageId in pageIds {
       // Prefetch page into buffer cache
       _ = await bufferManager.getPageQuery(pageId: pageId)
   }
   ```
   - **Prefetching**: Prefetch pages for found entries
   - **Performance**: Improves subsequent access
   - **Buffer Integration**: Uses Buffer Manager for caching

5. **Update Metrics**:
   ```swift
   updateMetrics(indexId: indexId)
   // Updates: scanCount, hitRate, missRate
   ```
   - **Metrics Update**: Update performance metrics
   - **Tracking**: Tracks index usage

6. **Return Entries**:
   ```swift
   return sortedEntries
   ```

**Preconditions**:
- Index exists (`indexes[indexId] != nil`)
- `startKey <= endKey` (valid range)

**Postconditions**:
- Entries returned (may be empty if range empty)
- Entries sorted by key
- Pages prefetched (if entries found)
- Metrics updated (scanCount, hitRate, missRate)

**Returns**: Sorted array of `IndexEntry` (may be empty)

**Performance Characteristics**:
- **Range Scan**: ~1μs-10ms (depends on range size and index type)
  - B+Tree: ~1μs-1ms (efficient range scan)
  - Hash: ~10ms (must scan all entries)
- **Scalable**: O(log n + k) for B+Tree, O(n) for Hash (where k = range size)

**Example Usage**:
```swift
// Range scan entries
let entries = try await indexManager.rangeScan(
    indexId: indexId,
    startKey: "a",
    endKey: "z"
)

// Process entries in range
for entry in entries {
    // Process entry
}
```

**Edge Cases**:

1. **Index Not Found**:
   - **Behavior**: Throws `IndexError.indexNotFound`
   - **Prevention**: Ensure index exists before scan

2. **Invalid Range** (`startKey > endKey`):
   - **Behavior**: Returns empty array
   - **Correctness**: Valid behavior (empty range)

3. **Empty Range**:
   - **Behavior**: Returns empty array
   - **Correctness**: Valid behavior (no entries in range)

4. **Hash Index Range Scan**:
   - **Behavior**: Must scan all entries (inefficient)
   - **Recommendation**: Use B+Tree for range queries

## 6. Invariants (TLA+ Verification)

### 6.1 Index Consistency Invariant

```tla
Inv_IndexConsistency ==
    \A indexId \in DOMAIN indexes:
        indexId \in DOMAIN indexMetadata /\
        indexId \in DOMAIN indexMetrics
```

**Swift Implementation**:
```swift
public func checkIndexConsistencyInvariant() -> Bool {
    for (indexId, index) in indexes {
        // Check metadata exists
        guard indexMetadata[indexId] != nil else {
            return false
        }
        // Check metrics exists
        guard indexMetrics[indexId] != nil else {
            return false
        }
        // Check index entries match metadata
        if let metadata = indexMetadata[indexId] {
            if index.indexType != metadata.indexType {
                return false
            }
            if index.isUnique != metadata.unique {
                return false
            }
        }
    }
    return true
}
```

### 6.2 Data Integrity Invariant

```tla
Inv_DataIntegrity ==
    \A indexId \in DOMAIN indexes:
        \A entry \in indexes[indexId].entries:
            ~entry.isDeleted =>
                entry.pageId > 0 /\
                entry.offset >= 0
```

**Swift Implementation**:
```swift
public func checkDataIntegrityInvariant() -> Bool {
    for (_, index) in indexes {
        for entry in index.entries where !entry.isDeleted {
            // Check entry has valid pageId and offset
            guard entry.pageId > 0, entry.offset >= 0 else {
                return false
            }
        }
    }
    return true
}
```

### 6.3 Performance Metrics Invariant

```tla
Inv_PerformanceMetrics ==
    \A indexId \in DOMAIN indexMetrics:
        indexMetrics[indexId].hitRate >= 0 /\
        indexMetrics[indexId].hitRate <= 1 /\
        indexMetrics[indexId].missRate >= 0 /\
        indexMetrics[indexId].missRate <= 1 /\
        indexMetrics[indexId].hitRate + indexMetrics[indexId].missRate = 1
```

**Swift Implementation**:
```swift
public func checkPerformanceMetricsInvariant() -> Bool {
    for (_, metrics) in indexMetrics {
        guard metrics.hitRate >= 0.0,
              metrics.hitRate <= 1.0,
              metrics.missRate >= 0.0,
              metrics.missRate <= 1.0,
              abs(metrics.hitRate + metrics.missRate - 1.0) < 0.01 else {
            return false
        }
    }
    return true
}
```

## 7. Performance Characteristics

### 7.1 Index Creation

**Operation**: `createIndex()`

**Complexity**: O(1)

**Latency**: ~1ms

**Factors**:
- Page allocation overhead
- Metadata storage

### 7.2 Lookup Operation

**Operation**: `lookupEntry()`

**Complexity**: 
- B+Tree: O(log n)
- Hash: O(1)

**Latency**:
- B+Tree: ~1μs
- Hash: ~100ns

**Factors**:
- Index type
- Index size
- Cache hit rate

### 7.3 Range Scan Operation

**Operation**: `rangeScan()`

**Complexity**: 
- B+Tree: O(log n + k) where k = range size
- Hash: O(n)

**Latency**:
- B+Tree: ~1μs-1ms
- Hash: ~10ms

**Factors**:
- Index type
- Range size
- Cache hit rate

### 7.4 Insert Operation

**Operation**: `insertEntry()`

**Complexity**: 
- B+Tree: O(log n)
- Hash: O(1)

**Latency**:
- B+Tree: ~1μs
- Hash: ~100ns

**Factors**:
- Index type
- Index size
- Uniqueness check

## 8. Error Handling

### 8.1 Error Types

```swift
public enum IndexError: Error {
    case indexNotFound
    case duplicateIndex
    case duplicateKey
    case invalidIndexType
    case invalidEntry
    case indexCreationFailed
    case indexDropFailed
}
```

### 8.2 Error Recovery

- **Index Not Found**: Return error, caller handles
- **Duplicate Key**: Return error (unique constraint)
- **Index Creation Failed**: Cleanup partial state, retry

## 9. Testing

### 9.1 Unit Tests

- Index creation/drop
- Entry insert/update/delete
- Lookup operations
- Range scan operations
- Uniqueness constraints
- Invariant verification

### 9.2 Integration Tests

- Index + Storage Manager
- Index + Buffer Manager
- Concurrent access
- Error scenarios

### 9.3 Performance Tests

- Lookup latency
- Range scan latency
- Insert throughput
- Cache hit rate
- Memory usage

## 10. Apple-First Optimizations

### 10.1 Swift Actors

- **Actor Isolation**: Thread-safe index operations
- **No Locks**: Eliminates lock contention
- **Composable**: Easy to compose with other actors

### 10.2 Async/Await

- **Non-Blocking**: Index operations don't block threads
- **Concurrent**: Supports thousands of concurrent operations
- **Structured**: Clear error handling and control flow

### 10.3 Value Types

- **Immutable Entries**: Entry struct is immutable
- **Copy-on-Write**: Efficient memory usage
- **Thread Safety**: Immutable values are thread-safe

### 10.4 Buffer Manager Integration

- **Prefetching**: Prefetches pages for lookups and range scans
- **Cache Efficiency**: Improves cache hit rate
- **Performance**: Reduces disk I/O

## 11. References

- **RFC 0004**: Buffer Manager
- **RFC 0006**: Storage Manager
- **TLA+ Spec**: `spec/Index.tla`

---

**Next**: See RFC 0025 for Query Optimizer details.
