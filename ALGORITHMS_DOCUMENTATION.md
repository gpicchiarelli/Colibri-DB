# Algorithms Documentation

Complete documentation of complex algorithms in Colibrì-DB.

---

## 📖 Table of Contents

1. [MVCC Visibility Rules](#mvcc-visibility-rules)
2. [Lock Manager & Deadlock Detection](#lock-manager--deadlock-detection)
3. [WAL Recovery (ARIES)](#wal-recovery-aries)
4. [Buffer Pool Eviction (LRU)](#buffer-pool-eviction-lru)
5. [Query Planning & Optimization](#query-planning--optimization)
6. [Group Commit Batching](#group-commit-batching)
7. [B+Tree Index Operations](#btree-index-operations)

---

## MVCC Visibility Rules

**File**: `Sources/ColibriCore/Concurrency/MVCC/MVCCManager.swift`

### Algorithm Overview

Multi-Version Concurrency Control (MVCC) allows multiple transactions to access the same data concurrently without blocking by maintaining multiple versions of each row.

### Visibility Rules

```swift
// Rule 1: Row created by transaction T
if row.createdBy == tid {
    return VISIBLE  // Always see your own changes
}

// Rule 2: Row created by committed transaction before snapshot
if row.createdBy < snapshotCutoff && committedTIDs.contains(row.createdBy) {
    // Rule 2a: Not deleted
    if row.deletedBy == nil {
        return VISIBLE
    }
    // Rule 2b: Deleted by uncommitted or later transaction
    if row.deletedBy > tid || !committedTIDs.contains(row.deletedBy) {
        return VISIBLE
    }
}

// Rule 3: All other cases
return INVISIBLE
```

### Data Structures

```swift
private var tableVersions: [String: [RID: [Version]]] = [:]
private(set) var activeTIDs: Set<UInt64> = []
private(set) var committedTIDs: Set<UInt64> = [0]
private(set) var abortedTIDs: Set<UInt64> = []
```

### Performance Characteristics

- **begin()**: O(1) - Adds TID to active set
- **commit()**: O(1) - Moves TID to committed set
- **visibleRows()**: O(n) where n = number of versions
- **Space**: O(v * r) where v = versions, r = rows

### Isolation Levels

| Level | Snapshot Point | Re-reads See |
|-------|---------------|--------------|
| Read Committed | Per statement | Latest committed |
| Repeatable Read | Transaction start | Same snapshot |
| Serializable | Transaction start | Same + conflict detection |

---

## Lock Manager & Deadlock Detection

**File**: `Sources/ColibriCore/Concurrency/LockManager.swift`

### Lock Types

```swift
public enum LockMode {
    case shared    // S: Multiple readers
    case exclusive // X: Single writer
}
```

### Compatibility Matrix

|     | S | X |
|-----|---|---|
| **S** | ✅ | ❌ |
| **X** | ❌ | ❌ |

### Deadlock Detection Algorithm

**Algorithm**: Depth-First Search (DFS) on Wait-For Graph

```
1. Build wait-for graph:
   - Nodes: Transactions (TIDs)
   - Edges: TID1 → TID2 if TID1 waits for lock held by TID2

2. Perform DFS from requesting transaction:
   - If cycle detected → DEADLOCK
   - Else → SAFE

3. On deadlock:
   - Abort youngest transaction in cycle
   - Retry lock acquisition
```

### Deadlock Detection Code

```swift
private func detectDeadlock(startingFrom start: UInt64) -> String? {
    guard start != 0 else { return nil }
    
    var graph: [UInt64: Set<UInt64>] = [:]
    
    // Build wait-for graph
    for (resource, state) in locks {
        if let holder = state.holder {
            for waiter in state.waiters {
                graph[waiter, default: []].insert(holder)
            }
        }
    }
    
    // DFS to detect cycle
    var visited: Set<UInt64> = []
    var recStack: Set<UInt64> = []
    
    func hasCycle(_ node: UInt64) -> String? {
        if recStack.contains(node) {
            return "Deadlock: \(node)"
        }
        if visited.contains(node) {
            return nil
        }
        
        visited.insert(node)
        recStack.insert(node)
        
        for neighbor in graph[node, default: []] {
            if let cycle = hasCycle(neighbor) {
                return cycle
            }
        }
        
        recStack.remove(node)
        return nil
    }
    
    return hasCycle(start)
}
```

### Performance Characteristics

- **lock()**: O(1) if no contention, O(V+E) for deadlock detection
- **unlock()**: O(1)
- **Deadlock Detection**: O(V+E) where V=transactions, E=wait edges
- **Space**: O(L) where L=number of locks

### Lock Striping Optimization

```swift
// Uses 64 lock stripes to reduce contention
let stripeId = resource.hash() % 64
let stripe = stripes[stripeId]
```

**Benefit**: Reduces lock contention by 64x for independent resources

---

## WAL Recovery (ARIES)

**File**: `Sources/ColibriCore/Engine/Database+GlobalWALRecovery.swift`

### ARIES Algorithm

**Algorithm for Recovery and Isolation Exploiting Semantics**

### Three Phases

#### 1. Analysis Phase

```
Goal: Identify transactions and dirty pages

For each record in WAL:
    - BEGIN: Add to ATT (Active Transaction Table)
    - COMMIT/ABORT: Remove from ATT
    - UPDATE: Add page to DPT (Dirty Page Table)
    
Output:
    - ATT: List of uncommitted transactions
    - DPT: List of dirty pages
    - Checkpoint LSN
```

#### 2. REDO Phase

```
Goal: Replay all operations to restore state

Start from: oldest DPT entry LSN
For each record:
    - If page in DPT and LSN > page.recLSN:
        Apply operation (INSERT, DELETE, UPDATE)
    - Update page LSN
    
Note: Redo everything, even aborted transactions
```

#### 3. UNDO Phase

```
Goal: Rollback uncommitted transactions

For each TID in ATT (reverse order):
    - Follow undo chain (prevLSN links)
    - For each operation:
        * INSERT → DELETE
        * DELETE → INSERT
        * Write CLR (Compensation Log Record)
    - Mark transaction as aborted
```

### Code Structure

```swift
public func recoverFromWAL() throws {
    // Phase 1: Analysis
    var att: Set<UInt64> = []          // Active transactions
    var dpt: [UInt64: UInt64] = [:]    // Dirty pages
    
    for record in walRecords {
        switch record.type {
        case .begin: att.insert(tid)
        case .commit: att.remove(tid)
        case .insertRow, .deleteRow: dpt[pageId] = lsn
        }
    }
    
    // Phase 2: REDO
    for record in walRecords {
        if shouldRedo(record, dpt: dpt) {
            applyOperation(record)
        }
    }
    
    // Phase 3: UNDO
    for tid in att {
        undoTransaction(tid)
    }
}
```

### Performance Characteristics

- **Analysis**: O(n) where n = WAL records
- **REDO**: O(n)
- **UNDO**: O(m * k) where m = uncommitted transactions, k = operations per transaction
- **Total**: O(n + m*k)

---

## Buffer Pool Eviction (LRU)

**File**: `Sources/ColibriCore/Storage/Buffer/LRUBufferPool.swift`

### LRU Algorithm

**Least Recently Used (LRU)**: Evict the page that hasn't been accessed for the longest time.

### Data Structures

```swift
// Doubly-linked list for LRU ordering
private var lruHead: Node?
private var lruTail: Node?

// Hash map for O(1) access
private var pages: [PageId: Node] = [:]

private class Node {
    let pageId: PageId
    var page: Page
    var lastAccess: Date
    var prev: Node?
    var next: Node?
}
```

### Operations

#### Get Page (O(1))

```
1. Check if page in cache
2. If found:
   - Move to head of LRU list
   - Update lastAccess
   - Return page
3. If not found:
   - Load from disk
   - Add to head of LRU list
   - Evict if necessary
```

#### Eviction (O(1))

```
1. Check if pool is full
2. If full:
   - Take page from tail (least recently used)
   - Flush if dirty
   - Remove from list and map
3. Add new page to head
```

### Code

```swift
public func getPage(_ pageId: PageId) throws -> Page {
    lock.lock()
    defer { lock.unlock() }
    
    // Hit: Move to head
    if let node = pages[pageId] {
        moveToHead(node)
        return node.page
    }
    
    // Miss: Load and possibly evict
    let page = try loadFromDisk(pageId)
    
    if pages.count >= maxPages {
        evictLRU()  // Remove tail
    }
    
    addToHead(pageId, page)
    return page
}

private func evictLRU() {
    guard let tail = lruTail else { return }
    
    if tail.page.isDirty {
        try? flushToDisk(tail.page)
    }
    
    removeNode(tail)
    pages.removeValue(forKey: tail.pageId)
}
```

### Performance Characteristics

- **getPage()**: O(1) average
- **evict()**: O(1)
- **flush()**: O(1)
- **Space**: O(maxPages)

### Enhancements

- **Clock Sweep**: Alternative to LRU with better cache behavior
- **2Q Algorithm**: Two queues for better hit rate
- **Adaptive**: Adjust size based on workload

---

## Query Planning & Optimization

**File**: `Sources/ColibriCore/Query/Planner/CostModel.swift`

### Cost-Based Optimization

Query planner chooses execution plan with lowest estimated cost.

### Cost Model

```
Cost = I/O Cost + CPU Cost + Network Cost

I/O Cost = Pages Read * PAGE_READ_COST
CPU Cost = Rows Processed * ROW_PROCESS_COST  
Network Cost = Bytes Sent * NETWORK_COST
```

### Query Planning Algorithm

```
1. Parse SQL → AST
2. Generate logical plan (relational algebra)
3. Generate physical plan alternatives:
   - Sequential scan
   - Index scan (if applicable)
   - Hash join vs Nested loop join
   - Sort vs Hash aggregate
4. Estimate cost for each alternative
5. Choose plan with minimum cost
6. Execute chosen plan
```

### Example

```sql
SELECT * FROM users WHERE age > 25
```

**Alternative Plans:**

| Plan | Operations | Cost | Chosen |
|------|-----------|------|--------|
| SeqScan(users) + Filter | Read all pages | 1000 | ❌ |
| IndexScan(age_idx) | Read index pages | 50 | ✅ |

### Cost Estimation Formulas

```swift
// Sequential Scan
cost = tablePages * PAGE_READ_COST + 
       estimatedRows * ROW_PROCESS_COST

// Index Scan
cost = indexPages * PAGE_READ_COST +
       indexLookups * INDEX_LOOKUP_COST +
       dataPages * PAGE_READ_COST

// Join
cost = outerCost + 
       (outerRows * innerCost)  // Nested loop
    OR
       (outerCost + innerCost + buildHashCost)  // Hash join
```

### Selectivity Estimation

```swift
// Equality predicate: column = value
selectivity = 1.0 / distinctValues

// Range predicate: column > value
selectivity = (maxValue - value) / (maxValue - minValue)

// Combined predicates (AND)
selectivity = selectivity1 * selectivity2

// Combined predicates (OR)
selectivity = selectivity1 + selectivity2 - (selectivity1 * selectivity2)
```

### Performance Characteristics

- **Planning**: O(n * m) where n = tables, m = indexes
- **Estimation**: O(1) with cached statistics
- **Execution**: Depends on chosen plan

---

## Group Commit Batching

**File**: `Sources/ColibriCore/Concurrency/GroupCommit/GroupCommitCoordinator.swift`

### Algorithm Overview

Group Commit batches multiple transaction commits into a single fsync() to reduce I/O overhead.

### How It Works

```
┌─────────┐
│ Thread 1│  TX1: Write → Submit commit ─┐
└─────────┘                               │
┌─────────┐                               │
│ Thread 2│  TX2: Write → Submit commit ─┤
└─────────┘                               ├─→ Queue
┌─────────┐                               │
│ Thread 3│  TX3: Write → Submit commit ─┤
└─────────┘                               │
┌─────────┐                               │
│ Thread 4│  TX4: Write → Submit commit ─┘
└─────────┘                               
                                          ↓
                    ┌────────────────────────────┐
                    │ GroupCommitCoordinator     │
                    │ - Waits for minBatchSize   │
                    │ - OR maxWaitTime timeout   │
                    └────────────────────────────┘
                                          ↓
                    ┌────────────────────────────┐
                    │ Batch Flush                │
                    │ fsync(max_LSN)             │
                    │ ONE disk sync for all 4 TX │
                    └────────────────────────────┘
                                          ↓
                    Notify all transactions complete
                    ↙     ↓      ↓      ↘
                  TX1   TX2    TX3    TX4
                  ✅    ✅     ✅     ✅
```

### Algorithm Pseudocode

```
Coordinator Thread:
  while not stopped:
    wait for:
      - pendingCommits.count >= minBatchSize
      - OR timeout (maxWaitTimeMs)
    
    batch = take up to maxBatchSize commits
    maxLSN = max(batch.map { $0.targetLSN })
    
    fsync(WAL up to maxLSN)
    
    for commit in batch:
      commit.completion(.success())
    
    update metrics

Transaction Thread:
  submitCommit(tid, targetLSN) {
    request = CommitRequest(tid, targetLSN, completion)
    pendingCommits.append(request)
    
    if pendingCommits.count >= minBatchSize:
      signal coordinator
    
    wait for completion callback
  }
```

### Configuration Parameters

```swift
struct Configuration {
    maxBatchSize: Int = 64        // Max transactions per batch
    maxWaitTimeMs: Double = 2.0   // Max wait time
    minBatchSize: Int = 4         // Min for immediate trigger
}
```

### Performance Model

```
Without Group Commit:
  N transactions × fsync_time = N × 10ms = N×10ms

With Group Commit (batch of B):
  N transactions / B batches × fsync_time = (N/B) × 10ms

Speedup = N×10ms / ((N/B)×10ms) = B

Example: B=10 → 10x speedup!
```

### Trade-offs

**Pros:**
- ✅ Massive throughput improvement (5-10x)
- ✅ Reduced I/O operations (10-25x fewer fsyncs)
- ✅ Better disk utilization

**Cons:**
- ⚠️ Slight latency increase (+1-2ms for batching)
- ⚠️ Complexity in error handling
- ⚠️ Requires concurrent workload for max benefit

---

## B+Tree Index Operations

**File**: `Sources/ColibriCore/Storage/Index/BPlusTree/FileBPlusTreeIndex.swift`

### B+Tree Structure

```
                    [Root: Internal Node]
                   /          |          \
         [Internal]      [Internal]      [Internal]
         /    |    \      /   |   \       /   |   \
    [Leaf] [Leaf] [Leaf] ... ... ... [Leaf] [Leaf] [Leaf]
       ↓      ↓      ↓                    ↓      ↓      ↓
     RIDs   RIDs   RIDs                 RIDs   RIDs   RIDs
```

### Key Properties

- **Order M**: Max M children per internal node
- **Balanced**: All leaves at same depth
- **Sorted**: Keys in sorted order
- **Leaf Links**: Leaves linked for range scans

### Insert Algorithm

```
1. Search tree to find leaf L for key K
2. If L has room:
   - Insert K into L
   - Done
3. If L is full:
   - Split L into L and L'
   - Redistribute keys evenly
   - Promote middle key to parent
   - Recursively split parent if needed
4. If root splits:
   - Create new root
   - Tree height increases
```

### Search Algorithm

```
search(key):
  node = root
  
  while node is internal:
    i = findChild(node, key)
    node = node.children[i]
  
  # node is leaf
  for (k, rid) in node.entries:
    if k == key:
      return rid
  
  return nil
```

### Delete Algorithm

```
delete(key):
  1. Find leaf L containing key
  2. Remove key from L
  3. If L underflows:
     - Try to redistribute from sibling
     - If sibling also minimal, merge with sibling
     - Recursively fix parent
  4. If root becomes empty:
     - Make only child the new root
     - Tree height decreases
```

### Range Scan

```
scan(startKey, endKey):
  leaf = findLeaf(startKey)
  
  while leaf != nil:
    for (key, rid) in leaf.entries:
      if key >= startKey and key <= endKey:
        yield rid
      if key > endKey:
        return
    
    leaf = leaf.nextLeaf  # Follow leaf links
```

### Performance Characteristics

- **Search**: O(log_M n)
- **Insert**: O(log_M n) + O(M) for split
- **Delete**: O(log_M n) + O(M) for merge
- **Range Scan**: O(log_M n + k) where k = results
- **Space**: O(n)

### Optimization: Bulk Loading

```
bulkLoad(sortedKeys):
  1. Sort all keys (if not sorted)
  2. Build leaves bottom-up
  3. Build internal nodes layer by layer
  4. Much faster than repeated inserts
  
Performance: O(n) instead of O(n log n)
```

---

## Performance Summary Table

| Algorithm | Time Complexity | Space | Notes |
|-----------|----------------|-------|-------|
| **MVCC Visibility** | O(n) | O(v×r) | n=versions |
| **Lock Acquire** | O(1) - O(V+E) | O(L) | With deadlock check |
| **WAL Recovery** | O(n + m×k) | O(T+P) | ARIES phases |
| **Buffer Pool Get** | O(1) | O(maxPages) | LRU |
| **Group Commit** | O(B log B) | O(B) | Sort for batch |
| **B+Tree Search** | O(log n) | O(n) | Balanced tree |
| **Query Planning** | O(n×m) | O(P) | Cost-based |

Where:
- n = records/pages
- v = versions, r = rows  
- V = transactions, E = wait edges
- L = locks, T = active transactions, P = dirty pages
- B = batch size, m = tables, k = operations
- M = B+Tree order

---

## 🎓 Algorithm Design Principles

### 1. **Correctness First**
All algorithms maintain ACID properties:
- ✅ Atomicity via WAL
- ✅ Consistency via constraints
- ✅ Isolation via MVCC
- ✅ Durability via fsync

### 2. **Performance Second**
Optimizations applied where safe:
- ✅ Group Commit for throughput
- ✅ LRU for cache hit rate
- ✅ Cost-based planning for query efficiency
- ✅ Lock striping for concurrency

### 3. **Simplicity Third**
Prefer simple, proven algorithms:
- ✅ ARIES for recovery (industry standard)
- ✅ LRU for eviction (simple, effective)
- ✅ B+Tree for indexing (balanced, predictable)
- ✅ DFS for deadlock (straightforward)

---

## 📚 References

- **ARIES**: Mohan et al., "ARIES: A Transaction Recovery Method"
- **MVCC**: Bernstein & Goodman, "Multiversion Concurrency Control"
- **B+Trees**: Comer, "The Ubiquitous B-Tree"
- **Group Commit**: Gray & Reuter, "Transaction Processing"
- **Deadlock Detection**: Knapp, "Deadlock Detection in Distributed Databases"

---

**Last Updated**: October 18, 2025  
**Status**: Complete  
**Coverage**: 7 major algorithms documented

