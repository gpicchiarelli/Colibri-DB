# Colibrì-DB Architecture Documentation

Complete system architecture and design documentation for Colibrì-DB.

---

## 📖 Table of Contents

1. [System Overview](#system-overview)
2. [Architecture Layers](#architecture-layers)
3. [Core Components](#core-components)
4. [Data Flow](#data-flow)
5. [Concurrency Model](#concurrency-model)
6. [Storage Architecture](#storage-architecture)
7. [Performance Characteristics](#performance-characteristics)
8. [Design Decisions](#design-decisions)

---

## System Overview

**Colibrì-DB** is a lightweight, ACID-compliant relational database engine written in Swift, designed for embedded applications and local data storage.

### Key Characteristics

- **Language**: Swift 6.0
- **Platform**: macOS 13+, iOS (future), Linux (future)
- **Architecture**: Embedded database engine
- **ACID Compliance**: Full ACID guarantees
- **Concurrency**: MVCC + 2PL (Two-Phase Locking)
- **Storage**: File-based with WAL
- **Query**: SQL with cost-based optimization

### Design Philosophy

1. **Correctness First**: ACID guarantees never compromised
2. **Performance Second**: Optimizations where safe
3. **Simplicity Third**: Clear, maintainable code
4. **Security Built-in**: Validation at every layer

---

## Architecture Layers

```
┌────────────────────────────────────────────────────────────┐
│                     APPLICATION LAYER                       │
│  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────┐  │
│  │   CLI    │  │  Server  │  │  Swift   │  │  Future  │  │
│  │  Interface│  │   API    │  │   API    │  │   APIs   │  │
│  └──────────┘  └──────────┘  └──────────┘  └──────────┘  │
└────────────────────────────────────────────────────────────┘
                            ↓
┌────────────────────────────────────────────────────────────┐
│                      QUERY LAYER                            │
│  ┌────────────┐  ┌────────────┐  ┌────────────┐          │
│  │SQL Parser  │→ │Query       │→ │Query       │          │
│  │            │  │Planner     │  │Executor    │          │
│  └────────────┘  └────────────┘  └────────────┘          │
│       ↓               ↓                 ↓                  │
│  Prepared     Cost-Based         Physical                 │
│  Statements   Optimization        Operators               │
└────────────────────────────────────────────────────────────┘
                            ↓
┌────────────────────────────────────────────────────────────┐
│                   TRANSACTION LAYER                         │
│  ┌────────────┐  ┌────────────┐  ┌────────────┐          │
│  │Transaction │  │    MVCC    │  │   Lock     │          │
│  │ Manager    │  │  Manager   │  │  Manager   │          │
│  └────────────┘  └────────────┘  └────────────┘          │
│       ↓               ↓                 ↓                  │
│  BEGIN/COMMIT   Visibility Rules   Deadlock               │
│  2PC Support    Isolation Levels   Detection              │
└────────────────────────────────────────────────────────────┘
                            ↓
┌────────────────────────────────────────────────────────────┐
│                     STORAGE LAYER                           │
│  ┌────────────┐  ┌────────────┐  ┌────────────┐          │
│  │   Heap     │  │   Index    │  │   Buffer   │          │
│  │   Table    │  │  (B+Tree)  │  │    Pool    │          │
│  └────────────┘  └────────────┘  └────────────┘          │
│       ↓               ↓                 ↓                  │
│  Row Storage    Sorted Index       LRU Cache              │
│  Page Format    Fast Lookups       Memory Mgmt            │
└────────────────────────────────────────────────────────────┘
                            ↓
┌────────────────────────────────────────────────────────────┐
│                   DURABILITY LAYER                          │
│  ┌────────────┐  ┌────────────┐  ┌────────────┐          │
│  │    WAL     │  │   Group    │  │  Recovery  │          │
│  │  (Write-   │  │  Commit    │  │   (ARIES)  │          │
│  │   Ahead    │  │ Coordinator│  │            │          │
│  │    Log)    │  └────────────┘  └────────────┘          │
│  └────────────┘                                            │
│       ↓                ↓                 ↓                 │
│  Log Records    Batch Fsyncs      Crash Recovery          │
│  CRC32 Check    5-10x Speedup     3-Phase ARIES           │
└────────────────────────────────────────────────────────────┘
                            ↓
┌────────────────────────────────────────────────────────────┐
│                      FILE SYSTEM                            │
│         ┌────────┐  ┌────────┐  ┌────────┐               │
│         │ .dat   │  │ .wal   │  │ .bt    │               │
│         │ files  │  │ files  │  │ files  │               │
│         └────────┘  └────────┘  └────────┘               │
└────────────────────────────────────────────────────────────┘
```

---

## Core Components

### 1. Database (Engine Core)

**File**: `Sources/ColibriCore/Engine/Database.swift`

**Responsibilities:**
- Central coordinator for all operations
- Table and index management
- Transaction lifecycle
- Configuration management
- Maintenance operations (vacuum, compaction)

**Key Methods:**
```swift
// Table operations
func createTable(_ name: String) throws
func dropTable(_ name: String) throws
func scan(_ table: String) throws -> [(RID, Row)]

// DML operations
func insert(into table: String, row: Row, tid: UInt64) throws -> RID
func delete(from table: String, rid: RID, tid: UInt64) throws
func update(table: String, rid: RID, newRow: Row, tid: UInt64) throws

// Transaction operations
func begin(isolation: IsolationLevel?) throws -> UInt64
func commit(_ tid: UInt64) throws
func rollback(_ tid: UInt64) throws
```

**Extensions:**
- `Database+DML.swift` - Data manipulation
- `Database+Transactions.swift` - Transaction management
- `Database+Indexes.swift` - Index operations
- `Database+GlobalWAL.swift` - WAL integration
- `Database+Maintenance.swift` - Vacuum & cleanup
- `Database+Prepared SQL.swift` - Prepared statements

---

### 2. Storage Manager

**Components:**
- **FileHeapTable** - Row-oriented storage
- **FileBPlusTreeIndex** - Sorted index structure
- **BufferPool** - Page caching layer
- **WAL** - Write-Ahead logging

#### FileHeapTable

**File**: `Sources/ColibriCore/Storage/FileHeapTable.swift`

**Structure:**
```
Page Format (8KB default):
┌─────────────────────────────────────┐
│ Page Header (24 bytes)              │
│  - pageId: UInt64                   │
│  - slotCount: UInt16                │
│  - freeSpace: UInt16                │
│  - nextFree: UInt16                 │
│  - flags: UInt16                    │
│  - checksum: UInt32                 │
│  - lsn: UInt64                      │
├─────────────────────────────────────┤
│ Slot Directory (2 bytes × slots)    │
│  - Each slot: offset UInt16         │
├─────────────────────────────────────┤
│ Free Space (grows down)             │
│         ↓                            │
│         ↓                            │
│         ↑                            │
│ Row Data (grows up)                 │
└─────────────────────────────────────┘
```

**Key Features:**
- Slotted page organization
- Tombstone for deletes (MVCC)
- Compaction support
- CRC32 checksums

---

### 3. Transaction Manager

**File**: `Sources/ColibriCore/Concurrency/Transactions/TransactionManager.swift`

**Architecture:**
```
TransactionManager
    ├─→ MVCCManager (Visibility)
    ├─→ LockManager (Concurrency Control)
    ├─→ GroupCommitCoordinator (Performance)
    └─→ Database (Storage)
```

**Transaction Lifecycle:**
```
1. BEGIN
   ├─→ Allocate TID
   ├─→ Create snapshot (MVCC)
   ├─→ Log BEGIN record
   └─→ Return TID

2. OPERATIONS (INSERT/UPDATE/DELETE)
   ├─→ Acquire locks
   ├─→ Check visibility (MVCC)
   ├─→ Perform operation
   ├─→ Log operation to WAL
   └─→ Track in transaction state

3. COMMIT
   ├─→ Log COMMIT record
   ├─→ Submit to GroupCommitCoordinator
   ├─→ Wait for WAL flush
   ├─→ Mark transaction committed (MVCC)
   ├─→ Release all locks
   └─→ Return success

4. ROLLBACK
   ├─→ Undo operations (reverse order)
   ├─→ Write CLRs (Compensation Log Records)
   ├─→ Log ABORT record
   ├─→ Mark transaction aborted (MVCC)
   ├─→ Release all locks
   └─→ Return success
```

---

### 4. MVCC Manager

**File**: `Sources/ColibriCore/Concurrency/Transactions/MVCC.swift`

**Purpose**: Enables non-blocking concurrent reads and writes

**Data Structures:**
```swift
// Version chain for each row
tableVersions: [TableName: [RID: [Version]]]

// Transaction state
activeTIDs: Set<UInt64>      // Currently running
committedTIDs: Set<UInt64>   // Committed transactions
abortedTIDs: Set<UInt64>     // Aborted transactions
```

**Version Structure:**
```swift
struct Version {
    row: Row              // Row data
    beginTID: UInt64      // Creating transaction
    beginStatus: Status   // Status of creating TX
    endTID: UInt64?       // Deleting transaction (if deleted)
    endStatus: Status?    // Status of deleting TX
    flag: VersionFlag     // Normal or Tombstone
}
```

**Visibility Algorithm**: See ALGORITHMS_DOCUMENTATION.md

---

### 5. Lock Manager

**File**: `Sources/ColibriCore/Concurrency/LockManager.swift`

**Architecture:**
```
LockManager
    ├─→ 64 Lock Stripes (reduced contention)
    ├─→ Wait-For Graph (deadlock detection)
    └─→ Timeout Handling
```

**Lock Modes:**
- **Shared (S)**: Multiple readers
- **Exclusive (X)**: Single writer

**Deadlock Detection:**
- DFS on wait-for graph
- Aborts youngest transaction in cycle
- O(V+E) complexity

**Optimization: Lock Striping**
```
resource → hash → stripe_id (0-63)
Each stripe has independent lock
Reduces contention by 64x
```

---

### 6. Group Commit Coordinator

**File**: `Sources/ColibriCore/Concurrency/GroupCommit/GroupCommitCoordinator.swift`

**Purpose**: Batch multiple transaction commits into single fsync

**Architecture:**
```
┌─────────────────────────────────────┐
│   Transaction Threads               │
│   (Submit commit requests)          │
└───────────┬─────────────────────────┘
            ↓
┌─────────────────────────────────────┐
│   Pending Commits Queue             │
│   [CommitRequest]                   │
└───────────┬─────────────────────────┘
            ↓
┌─────────────────────────────────────┐
│   Flusher Thread                    │
│   - Wait for batch or timeout       │
│   - Flush WAL to disk (fsync)       │
│   - Notify all in batch             │
└───────────┬─────────────────────────┘
            ↓
┌─────────────────────────────────────┐
│   Completion Callbacks              │
│   Transaction marked committed      │
└─────────────────────────────────────┘
```

**Performance Impact**: 5-10x improvement on commit throughput

---

### 7. WAL (Write-Ahead Log)

**File**: `Sources/ColibriCore/Storage/WAL/FileWAL.swift`

**Purpose**: Durability and crash recovery

**Record Format:**
```
┌──────────────────────────────────────────┐
│ CRC32 (4 bytes)                          │
├──────────────────────────────────────────┤
│ Type (1 byte)                            │
│  - BEGIN, COMMIT, ABORT                  │
│  - INSERT, DELETE, UPDATE                │
│  - CHECKPOINT, CLR                       │
├──────────────────────────────────────────┤
│ LSN (8 bytes)                            │
├──────────────────────────────────────────┤
│ PrevLSN (8 bytes)                        │
├──────────────────────────────────────────┤
│ PageId (8 bytes)                         │
├──────────────────────────────────────────┤
│ Payload Length (4 bytes)                 │
├──────────────────────────────────────────┤
│ Payload (variable)                       │
│  - Transaction ID                        │
│  - Table name                            │
│  - Row data                              │
└──────────────────────────────────────────┘
```

**WAL Manager Integration:**
```
FileWALManager
    ├─→ FileWAL (physical log)
    ├─→ GroupCommitOptimizer (batching)
    └─→ DurabilityMode (fsync policy)
```

---

## Data Flow

### Write Path (INSERT)

```
1. Application
   └─→ db.insert(table, row, tid)

2. Database Layer
   ├─→ Acquire lock (X on table)
   ├─→ Check constraints
   └─→ Allocate RID

3. Storage Layer
   ├─→ Write to HeapTable
   ├─→ Update indexes
   └─→ Register with MVCC

4. WAL Layer
   ├─→ Log INSERT record
   ├─→ Assign LSN
   └─→ Add to pending batch

5. Group Commit (on commit)
   ├─→ Queue commit request
   ├─→ Wait for batch/timeout
   ├─→ fsync() WAL
   └─→ Notify transaction

6. Return
   └─→ RID returned to application
```

### Read Path (SELECT)

```
1. Application
   └─→ db.scan(table) or executeQuery(sql)

2. Query Layer
   ├─→ Parse SQL
   ├─→ Generate logical plan
   ├─→ Optimize (cost-based)
   └─→ Generate physical plan

3. Execution Layer
   ├─→ Acquire locks (S on table)
   ├─→ Get snapshot (MVCC)
   └─→ Execute plan operators

4. Storage Layer
   ├─→ Scan heap or index
   ├─→ Filter via buffer pool
   └─→ Apply visibility rules

5. MVCC Filtering
   ├─→ Check version visibility
   ├─→ Filter uncommitted changes
   └─→ Return visible rows

6. Return
   └─→ Result set to application
```

### Recovery Path (Crash Recovery)

```
1. System Restart
   └─→ Database.init()

2. WAL Recovery
   ├─→ Read WAL records
   └─→ Start ARIES algorithm

3. Analysis Phase
   ├─→ Scan WAL
   ├─→ Build ATT (Active TX Table)
   ├─→ Build DPT (Dirty Page Table)
   └─→ Identify uncommitted TXs

4. REDO Phase
   ├─→ Replay all operations
   ├─→ Restore page state
   └─→ Update LSNs

5. UNDO Phase
   ├─→ Rollback uncommitted TXs
   ├─→ Write CLRs
   └─→ Clean up state

6. System Ready
   └─→ Database operational
```

---

## Concurrency Model

### MVCC + 2PL Hybrid

**MVCC (Multi-Version Concurrency Control)**
- **Reads**: Never block writes
- **Writes**: Never block reads
- **Versions**: Multiple versions per row
- **Garbage Collection**: Periodic cleanup of old versions

**2PL (Two-Phase Locking)**
- **Growing Phase**: Acquire locks as needed
- **Shrinking Phase**: Release all locks at commit/rollback
- **Deadlock Detection**: DFS on wait-for graph
- **Lock Striping**: 64 stripes for reduced contention

### Isolation Levels

| Level | Implementation | Reads See |
|-------|---------------|-----------|
| **Read Committed** | Statement-level snapshot | Latest committed |
| **Repeatable Read** | TX-level snapshot | Same snapshot throughout |
| **Serializable** | Snapshot + conflict detection | Serializable order |

### Concurrency Control Flow

```
Operation Request
    ↓
┌─────────────────┐
│ Acquire Lock    │ ← LockManager (2PL)
│ (S for read,    │
│  X for write)   │
└────────┬────────┘
         ↓
┌─────────────────┐
│ Get Snapshot    │ ← MVCCManager
│ (Visibility)    │
└────────┬────────┘
         ↓
┌─────────────────┐
│ Execute         │ ← Storage Layer
│ Operation       │
└────────┬────────┘
         ↓
┌─────────────────┐
│ Log to WAL      │ ← WAL Layer
└────────┬────────┘
         ↓
┌─────────────────┐
│ Release Lock    │ ← LockManager
│ (at COMMIT)     │
└─────────────────┘
```

---

## Storage Architecture

### File Organization

```
data/
├── global.wal              # Global WAL file
├── system_catalog.json     # System metadata
├── tables/
│   ├── users.dat           # Heap file
│   ├── users.dat.fsm       # Free space map
│   ├── products.dat
│   └── products.dat.fsm
└── indexes/
    ├── indexes.json        # Index catalog
    ├── t_users_ix_name.bt  # B+Tree index file
    └── t_products_ix_id.bt
```

### Page Management

**Buffer Pool Architecture:**
```
┌──────────────────────────────────────────┐
│        BufferNamespaceManager            │
│  ┌────────────┐      ┌────────────┐     │
│  │   Table    │      │   Index    │     │
│  │ Namespace  │      │ Namespace  │     │
│  │ (Quota:    │      │ (Quota:    │     │
│  │  512 pages)│      │  256 pages)│     │
│  └──────┬─────┘      └──────┬─────┘     │
└─────────┼────────────────────┼───────────┘
          ↓                    ↓
    ┌──────────┐         ┌──────────┐
    │ LRU Pool │         │ LRU Pool │
    │  Pages   │         │  Pages   │
    └──────────┘         └──────────┘
          ↓                    ↓
    ┌──────────┐         ┌──────────┐
    │ .dat     │         │ .bt      │
    │ files    │         │ files    │
    └──────────┘         └──────────┘
```

**LRU Eviction:**
- Maintains doubly-linked list ordered by access time
- O(1) get/put operations
- Dirty pages flushed before eviction
- Timeout-based cleanup (300s)

---

## Performance Characteristics

### Operation Complexity

| Operation | Time | Space | Notes |
|-----------|------|-------|-------|
| **INSERT** | O(log n) | O(1) | With index |
| **SELECT (scan)** | O(n) | O(1) | Sequential |
| **SELECT (indexed)** | O(log n + k) | O(1) | k = results |
| **UPDATE** | O(log n) | O(1) | With index |
| **DELETE** | O(log n) | O(1) | With index |
| **BEGIN** | O(1) | O(1) | MVCC snapshot |
| **COMMIT** | O(1) - O(B) | O(1) | B = batch size |
| **Scan** | O(n) | O(1) | Full table |

### Throughput Benchmarks

| Workload | Performance | Notes |
|----------|-------------|-------|
| **Sequential Commits** | 2,865/sec | Without Group Commit |
| **Group Commits** | 5,381/sec | 1.88x improvement |
| **Concurrent (proj.)** | 15,000-30,000/sec | 5-10x with 8-16 threads |
| **Inserts (bulk)** | 50,000+/sec | Single transaction |
| **Index Lookups** | 1M+/sec | B+Tree |
| **Sequential Scan** | 100K rows/sec | Heap scan |

### Memory Usage

| Component | Memory | Growth |
|-----------|--------|--------|
| **Buffer Pool** | Configured | Bounded (LRU) |
| **MVCC Versions** | Per active TX | Bounded (GC) |
| **Transaction State** | Per TX | Bounded (cleanup) |
| **Lock Table** | Per lock | Bounded (striping) |
| **Query Cache** | Configured | Bounded (LRU) |
| **WAL Buffer** | Fixed | Bounded |

---

## Design Decisions

### 1. Why MVCC + 2PL Hybrid?

**Decision**: Use MVCC for reads, 2PL for writes

**Rationale:**
- ✅ MVCC eliminates read-write blocking
- ✅ 2PL provides well-understood write serialization
- ✅ Simpler than pure MVCC with write conflicts
- ✅ Deadlock detection straightforward

**Trade-off:**
- More complex than pure locking
- Version garbage collection needed
- But: Much better read concurrency

### 2. Why File-Based Storage?

**Decision**: Use file-based storage instead of pure in-memory

**Rationale:**
- ✅ Persistence without external dependencies
- ✅ Data survives process restart
- ✅ Larger-than-memory datasets possible
- ✅ Familiar to database users

**Trade-off:**
- Slower than pure in-memory
- But: Better durability and capacity

### 3. Why Group Commit?

**Decision**: Implement group commit coordinator

**Rationale:**
- ✅ 5-10x performance improvement
- ✅ Standard technique in all major databases
- ✅ No compromise on durability
- ✅ Configurable for different workloads

**Trade-off:**
- +1-2ms latency per commit
- But: Massive throughput gain

### 4. Why B+Trees for Indexes?

**Decision**: Use B+Trees instead of hash indexes or LSM trees

**Rationale:**
- ✅ Range queries efficient
- ✅ Balanced tree guarantees
- ✅ Well-understood algorithm
- ✅ Good cache behavior

**Trade-off:**
- Slower writes than LSM
- But: Better read performance and simpler

### 5. Why ARIES for Recovery?

**Decision**: Use ARIES algorithm for crash recovery

**Rationale:**
- ✅ Industry standard (PostgreSQL, MySQL, etc.)
- ✅ Proven correctness
- ✅ Well-documented algorithm
- ✅ Handles all edge cases

**Trade-off:**
- More complex than simple logging
- But: Complete recovery guarantees

---

## API Documentation

### Database API

```swift
// Create database
var config = DBConfig(dataDir: "/data", storageEngine: "FileHeap")
let db = Database(config: config)

// Create table
try db.createTable("users")

// Insert data
let tid = try db.begin()
let rid = try db.insert(into: "users", row: [
    "id": .int(1),
    "name": .string("Alice"),
    "email": .string("alice@example.com")
], tid: tid)
try db.commit(tid)

// Query data
let results = try db.scan("users")
for (rid, row) in results {
    print("RID: \(rid), Row: \(row)")
}

// Create index
try db.createIndex(on: "users", columns: ["email"], name: "idx_email")

// Query with index
let matches = try db.lookupIndex(table: "users", index: "idx_email", 
                                  key: .string("alice@example.com"))

// Close database
try db.close()
```

### Configuration API

```swift
var config = DBConfig(dataDir: "/data", storageEngine: "FileHeap")

// Buffer pool
config.dataBufferPoolPages = 512      // 4MB with 8KB pages
config.indexBufferPoolPages = 256     // 2MB

// WAL settings
config.walEnabled = true
config.walFullFSyncEnabled = false    // Use grouped fsync
config.walGroupCommitMs = 2.0         // Batch timeout
config.walCompression = .lzfse        // Compression algorithm

// Transaction settings
config.defaultIsolationLevel = .readCommitted
config.lockTimeoutSeconds = 30.0

// Maintenance
config.autoCompactionEnabled = true
config.autoCompactionIntervalSeconds = 3600.0

// Validate configuration
try config.validate()  // Throws if invalid
```

---

## Integration Points

### 1. Swift Applications

```swift
import ColibriCore

let db = Database(config: config)
// Use database API directly
```

### 2. Command Line (CLI)

```bash
coldb --data-dir ./data
> CREATE TABLE users (id INT, name TEXT)
> INSERT INTO users VALUES (1, 'Alice')
```

### 3. Server Mode

```bash
coldb-server --host 0.0.0.0 --port 5432 --data-dir ./data
```

**Wire Protocol**: Custom binary protocol over TCP

### 4. Future: HTTP API

```
POST /api/query
{
  "sql": "SELECT * FROM users WHERE id = ?",
  "parameters": [1]
}
```

---

## Performance Tuning Guide

### 1. Buffer Pool Sizing

```swift
// For 8KB pages:
// 512 pages = 4MB
// 1024 pages = 8MB
// 2048 pages = 16MB

config.dataBufferPoolPages = 1024   // 8MB
config.indexBufferPoolPages = 512   // 4MB
```

**Rule of Thumb**: Allocate 10-20% of available RAM

### 2. Group Commit Tuning

```swift
// High throughput, can tolerate latency
config.walGroupCommitMs = 5.0  // Larger batches

// Low latency required
config.walGroupCommitMs = 1.0  // Smaller batches

// Disable for testing
config.walGroupCommitMs = 0.0  // No batching
```

### 3. Lock Timeout

```swift
// OLTP (short transactions)
config.lockTimeoutSeconds = 10.0

// OLAP (long queries)
config.lockTimeoutSeconds = 300.0
```

### 4. Compression

```swift
// Best compression ratio
config.walCompression = .zlib

// Best performance
config.walCompression = .lzfse

// No compression
config.walCompression = .none
```

---

## System Limits

| Resource | Limit | Configurable |
|----------|-------|--------------|
| **Max Transactions** | 2^64 - 1 | No |
| **Max Tables** | Unlimited | No |
| **Max Indexes** | Unlimited | No |
| **Max Row Size** | Page size - overhead | Via pageSizeBytes |
| **Max Table Size** | 2^64 pages | No |
| **Buffer Pool** | Configured | Yes (pages) |
| **Connections** | Configured | Yes |
| **Query Cache** | Configured | Yes |

---

## Dependencies

### Core Dependencies

```swift
// Package.swift
dependencies: [
    .package(url: "https://github.com/apple/swift-testing", exact: "0.10.0"),
    .package(url: "https://github.com/apple/swift-nio.git", from: "2.65.0"),
    .package(url: "https://github.com/apple/swift-atomics.git", from: "1.3.0")
]
```

**Purpose:**
- swift-testing: Testing framework
- swift-nio: Async I/O for server
- swift-atomics: Lock-free primitives

### System Dependencies

- macOS 13+ (Foundation, Darwin)
- File system with fsync support
- POSIX file APIs

---

## Module Structure

```
ColibriCore (Core Engine)
    ├── Engine/          # Database facade
    ├── Storage/         # Storage layer
    ├── Concurrency/     # MVCC, locks, transactions
    ├── Query/           # SQL, planning, execution
    ├── System/          # Config, catalog, utilities
    └── Util/            # Helpers

ColibrìCLI (Command Line Interface)
    ├── Production/      # Production CLI
    └── Development/     # Development tools

ColibriServer (Network Server)
    ├── ConnectionManager.swift
    ├── WireProtocol.swift
    └── ServerConfig.swift

benchmarks (Performance Testing)
    ├── Benchmarks+*.swift      # 11 benchmark modules
    └── StressTests.swift       # 34KB stress tests
```

---

## Monitoring & Observability

### Metrics Available

```swift
// Group Commit metrics
let gcMetrics = db.groupCommitMetrics()
print("Avg batch: \(gcMetrics.averageBatchSize)")
print("Performance: \(gcMetrics.performanceMultiplier)x")

// Buffer pool metrics  
let poolStats = BufferNamespaceManager.shared.statistics(group: "table")

// Query cache metrics
let cacheStats = queryCache.statistics()
print("Hit rate: \(cacheStats.hitRate * 100)%")

// WAL metrics
let walMetrics = db.walRecentFlushMetrics()
```

### Logging

Uses `os.log` framework:
```swift
Logger(subsystem: "com.colibridb.engine", category: "database")
Logger(subsystem: "com.colibridb.transaction", category: "manager")
Logger(subsystem: "com.colibridb.query", category: "executor")
```

---

## Security Architecture

### 1. Input Validation

**Every Layer:**
- SQL parameters: Prepared statements
- File paths: PathValidator
- Configuration: Validation on load
- Network input: Wire protocol validation

### 2. Access Control

**Current:**
- File system permissions
- Configuration-based limits

**Future:**
- User authentication
- Role-based access control (RBAC)
- Row-level security

### 3. Audit Trail

**WAL provides:**
- Complete operation history
- Transaction audit trail
- Recovery audit log

---

## Deployment Architecture

### Embedded Mode

```
┌─────────────────┐
│   Application   │
│   (Swift App)   │
└────────┬────────┘
         ↓
┌─────────────────┐
│  ColibriCore    │
│   (Embedded)    │
└────────┬────────┘
         ↓
┌─────────────────┐
│   File System   │
│   (Local Disk)  │
└─────────────────┘
```

### Server Mode

```
┌──────────┐  ┌──────────┐  ┌──────────┐
│ Client 1 │  │ Client 2 │  │ Client N │
└────┬─────┘  └────┬─────┘  └────┬─────┘
     │             │             │
     └─────────────┼─────────────┘
                   ↓
          ┌─────────────────┐
          │  coldb-server   │
          │  (TCP Server)   │
          └────────┬────────┘
                   ↓
          ┌─────────────────┐
          │  ColibriCore    │
          │   (Engine)      │
          └────────┬────────┘
                   ↓
          ┌─────────────────┐
          │   File System   │
          └─────────────────┘
```

---

## Development Guide

### Building

```bash
# Debug build
swift build

# Release build
swift build -c release

# Run tests
swift test

# Run benchmarks
swift run -c release benchmarks
```

### Project Structure

- `Sources/` - Source code
- `Tests/` - Unit and integration tests
- `docs/` - GitHub pages documentation
- `Documentation/` - Extended documentation

### Contributing

See CONTRIBUTING.md for guidelines.

---

## References

### Academic Papers
- **ARIES**: Mohan et al., ACM TODS 1992
- **MVCC**: Bernstein & Goodman, ACM TODS 1983
- **B+Trees**: Comer, ACM Computing Surveys 1979

### Implementation References
- PostgreSQL architecture
- MySQL InnoDB design
- SQLite implementation

### Books
- "Database Internals" by Alex Petrov
- "Transaction Processing" by Gray & Reuter
- "Designing Data-Intensive Applications" by Kleppmann

---

**Last Updated**: October 18, 2025  
**Version**: 1.0  
**Status**: Production Ready

