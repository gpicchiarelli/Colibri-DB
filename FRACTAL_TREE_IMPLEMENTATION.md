# Fractal Tree Index - Advanced Implementation

**Issue #55**: ⚡ Performance: Fractal Tree Index Incomplete - Missing Advanced Features

## Overview

This document describes the complete implementation of the advanced Fractal Tree Index for ColibrìDB, addressing all requirements from issue #55.

## Architecture

### Message Buffering System

The Fractal Tree Index implements a multi-level message buffering system that defers expensive tree modifications:

```
Level 0 (Top)     [Buffer: 256 entries]  ← Fast writes here
     ↓
Level 1           [Buffer: 512 entries]  ← Flush from Level 0
     ↓
Level 2 (Bottom)  [Buffer: 1024 entries] ← Final flush to base data
     ↓
Base Data         [Sorted key-value store]
```

**Key Features:**
- Exponential buffer capacity per level (configurable)
- Automatic flush when buffer is full
- Message types: insert, delete, bulkInsert, bulkDelete

### Hierarchical Merge Operations

Three merge strategies are available:

1. **Lazy Merge** (default)
   - Merges only when buffer is full
   - Best for write-heavy workloads
   - Minimizes merge overhead

2. **Eager Merge**
   - Merges immediately on every operation
   - Best for read-heavy workloads
   - Keeps data fresh for queries

3. **Adaptive Merge**
   - Adjusts based on buffer fill ratio (70% threshold)
   - Balances read and write performance
   - Self-tuning based on workload

### Partitioning

Horizontal partitioning for scalability:

```swift
Partition 0: [Keys with hash % N == 0]
Partition 1: [Keys with hash % N == 1]
...
Partition N-1: [Keys with hash % N == N-1]
```

**Benefits:**
- Parallel query execution
- Reduced lock contention
- Better cache locality
- Scalability to large datasets

### Compression

Optional compression at lower levels:

- Level 0: No compression (hot data)
- Level 1+: Compression enabled (cold data)
- Reduces memory footprint
- Transparent to users

## API Reference

### Configuration

```swift
public struct Configuration {
    var bufferCapacity: Int = 256
    var levelCount: Int = 3
    var partitionCount: Int = 1
    var compressionEnabled: Bool = true
    var autoCompactionThreshold: Int = 1000
    var bulkOperationBatchSize: Int = 100
    var mergeStrategy: MergeStrategy = .lazy
}
```

### Basic Operations

```swift
// Create index
var index = FractalTreeIndex<String, RID>()

// Insert
try index.insert("key", ref)

// Search
let results = try index.searchEquals("key")

// Range query
let rangeResults = try index.range("a", "z")

// Delete
try index.remove("key", ref)
```

### Bulk Operations

```swift
// Bulk insert
try index.bulkInsert(
    keys: ["a", "b", "c"],
    refs: [1, 2, 3]
)

// Bulk delete
try index.bulkDelete(
    keys: ["a", "b"],
    refs: [1, 2]
)

// Bulk update (delete + insert)
try index.bulkUpdate(
    keys: ["a", "b"],
    oldRefs: [1, 2],
    newRefs: [10, 20]
)
```

### Optimization

```swift
// Manual optimization
try index.optimize()

// Automatic optimization (every N operations)
config.autoCompactionThreshold = 1000
```

### Statistics & Diagnostics

```swift
// Get detailed statistics
let stats = index.getStatistics()
print("Total inserts: \(stats.totalInserts)")
print("Total merges: \(stats.totalMerges)")
print("Avg merge time: \(stats.avgMergeTime)s")

// Memory estimation
let memory = index.estimateMemoryUsage()
print("Estimated memory: \(memory) bytes")
```

## Performance Characteristics

### Time Complexity

| Operation | Best Case | Average Case | Worst Case |
|-----------|-----------|--------------|------------|
| Insert    | O(1)      | O(log N)     | O(N)       |
| Search    | O(log L)  | O(L * log N) | O(N)       |
| Range     | O(L + K)  | O(L * N)     | O(N * M)   |
| Delete    | O(1)      | O(log N)     | O(N)       |
| Bulk Insert | O(B)   | O(B * log N) | O(B * N)   |

Where:
- N = number of keys
- L = number of levels
- K = number of results
- M = number of messages
- B = batch size

### Space Complexity

| Component | Space |
|-----------|-------|
| Buffers   | O(L * B) |
| Base Data | O(N) |
| Partitions | O(P * N) |
| Total     | O(L * B + P * N) |

Where:
- L = number of levels
- B = buffer capacity per level
- N = number of keys
- P = number of partitions

### Memory Optimization

The implementation includes several memory optimizations:

1. **Lazy Materialization**: Data is only materialized when needed for queries
2. **Buffer Reuse**: Buffers maintain capacity after clearing
3. **Compression**: Optional compression for lower levels
4. **Dead Entry Removal**: Automatic cleanup during compaction

## Testing

Comprehensive test suite in `Tests/ColibriCoreTests/FractalTreeIndexTests.swift`:

- ✅ Basic operations (insert, search, delete, range)
- ✅ Bulk operations (insert, delete, update)
- ✅ Buffer management and automatic flushing
- ✅ Hierarchical merge operations
- ✅ Optimization and compaction
- ✅ Statistics and diagnostics
- ✅ Partitioning
- ✅ All merge strategies (lazy, eager, adaptive)
- ✅ Stress tests with large datasets
- ✅ Duplicate value handling

## Integration

The Fractal Tree Index integrates seamlessly with existing ColibrìDB components:

### Index Catalog

```swift
// In IndexCatalog.swift
case .fractal:
    let ft = FractalTreeIndex<String, RID>()
    return .fractal(ft)
```

### SQL Support

```sql
CREATE INDEX idx_name ON table_name (column) USING Fractal;
```

### Query Planner

The index is automatically selected by the query planner when appropriate:

- Range queries with selective predicates
- Bulk insert/delete operations
- Write-heavy workloads
- Workloads with deferred writes

## Configuration Recommendations

### Write-Heavy Workload

```swift
var config = Configuration()
config.mergeStrategy = .lazy
config.bufferCapacity = 512
config.levelCount = 4
config.autoCompactionThreshold = 5000
```

### Read-Heavy Workload

```swift
var config = Configuration()
config.mergeStrategy = .eager
config.bufferCapacity = 128
config.levelCount = 2
config.autoCompactionThreshold = 1000
```

### Balanced Workload

```swift
var config = Configuration()
config.mergeStrategy = .adaptive
config.bufferCapacity = 256
config.levelCount = 3
config.autoCompactionThreshold = 2000
```

### Large Dataset

```swift
var config = Configuration()
config.partitionCount = 4
config.bufferCapacity = 1024
config.levelCount = 5
config.compressionEnabled = true
```

## Future Enhancements

Potential improvements for future versions:

1. **Persistent Storage**: Write buffers and base data to disk
2. **Concurrent Access**: Lock-free or fine-grained locking
3. **Bloom Filters**: Skip unnecessary level checks
4. **Adaptive Partitioning**: Dynamic partition rebalancing
5. **Incremental Compaction**: Spread compaction over time
6. **Range Partitioning**: Partition by key ranges instead of hash

## References

- Original Paper: [Cache-Oblivious Streaming B-trees](https://en.wikipedia.org/wiki/Fractal_tree_index)
- Tokutek (now Percona): [Fractal Tree Indexing](https://www.percona.com/doc/percona-server/5.7/tokudb/tokudb_fractal_tree_indexing.html)
- Issue #55: https://github.com/gpicchiarelli/Colibri-DB/issues/55

## Contributors

- Implementation: AI Assistant (Claude)
- Review: Giacomo Picchiarelli
- Testing: Automated test suite

---

**Status**: ✅ Complete
**Date**: October 18, 2025
**Version**: 1.0

