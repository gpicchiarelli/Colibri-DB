# Database Engine Internals

## Overview

The `Database` class is the central coordinator of ColibrìDB, acting as a facade that unifies storage, WAL, MVCC, policies, and catalogs. It provides a single interface for CLI commands and query operators, ensuring consistent adoption of locking, MVCC, and WAL across all operations.

## Class Structure and State Management

### Core State Variables

```swift
public final class Database {
    /// Runtime configuration (page size, buffer, isolation, policies, etc.)
    public let config: DBConfig
    
    // Apple Silicon optimizations
    private let logger = Logger(subsystem: "com.colibridb", category: "database")
```

**Analysis:**
- **`final class`**: Prevents inheritance, ensuring the database state cannot be corrupted by subclassing
- **`config: DBConfig`**: Immutable configuration object that defines runtime behavior
- **`Logger`**: Uses `os.log` framework for efficient, structured logging optimized for Apple Silicon

### Storage Layer State

```swift
// MARK: - Storage state
var tablesMem: [String: HeapTable] = [:]
var tablesFile: [String: FileHeapTable] = [:]
var wal: FileWAL?
var lastDBLSN: UInt64 = 0
```

**Detailed Analysis:**

#### `tablesMem: [String: HeapTable]`
- **Purpose**: In-memory table storage for frequently accessed tables
- **Key**: Table name (String)
- **Value**: `HeapTable` instance
- **Design Rationale**: Provides fast access to table data without disk I/O
- **Memory Implications**: Each `HeapTable` maintains its own memory structures
- **Access Pattern**: O(1) lookup, but requires memory management

#### `tablesFile: [String: FileHeapTable]`
- **Purpose**: Persistent table storage backed by files
- **Key**: Table name (String)  
- **Value**: `FileHeapTable` instance
- **Design Rationale**: Ensures data durability and supports larger datasets
- **I/O Implications**: File operations are slower but provide persistence
- **Access Pattern**: O(1) lookup with potential disk I/O

#### `wal: FileWAL?`
- **Purpose**: Write-ahead logging for crash recovery
- **Type**: Optional `FileWAL` instance
- **Design Rationale**: Ensures ACID properties by logging changes before applying them
- **Recovery**: Enables recovery to last committed state after crash
- **Performance**: Sequential writes are faster than random writes

#### `lastDBLSN: UInt64`
- **Purpose**: Tracks the last Log Sequence Number (LSN) for the database
- **Type**: 64-bit unsigned integer
- **Design Rationale**: Provides unique ordering of database operations
- **Usage**: Used for WAL recovery and MVCC timestamping

### Index Management State

```swift
/// Available backends for each registered index
public enum IndexBackend {
    case anyString(AnyStringIndex)
    case persistentBTree(FileBPlusTreeIndex)
}

// MARK: - Index state & catalog
var indexes: [String: [String: (columns: [String], backend: IndexBackend)]] = [:]
var indexCatalog: IndexCatalog?
var systemCatalog: SystemCatalog?
var multiDatabaseCatalog: MultiDatabaseCatalog?
var catalogManager: CatalogManager?
```

**Detailed Analysis:**

#### `IndexBackend` Enum
```swift
public enum IndexBackend {
    case anyString(AnyStringIndex)
    case persistentBTree(FileBPlusTreeIndex)
}
```

**Design Rationale:**
- **`anyString`**: Optimized for string operations, uses specialized string indexing
- **`persistentBTree`**: General-purpose B+Tree for range queries and sorting
- **Enum Pattern**: Provides type safety and clear backend selection
- **Performance**: Each backend is optimized for specific use cases

#### `indexes` Dictionary Structure
```swift
var indexes: [String: [String: (columns: [String], backend: IndexBackend)]] = [:]
```

**Nested Dictionary Analysis:**
- **Outer Key**: Table name (String)
- **Inner Key**: Index name (String)
- **Value Tuple**: 
  - `columns: [String]`: Indexed columns
  - `backend: IndexBackend`: Index implementation

**Memory Layout:**
```
indexes["users"] = [
    "idx_email": (columns: ["email"], backend: .anyString(...)),
    "idx_name_age": (columns: ["name", "age"], backend: .persistentBTree(...))
]
```

**Access Pattern:**
- **Lookup**: O(1) for table, O(1) for index within table
- **Memory**: Each table can have multiple indexes
- **Flexibility**: Supports composite indexes with multiple columns

### Statistics and Caching

```swift
var cachedTableStats: [String: HeapFragmentationStats] = [:]
var tableStatistics: [String: TableStatistics] = [:]
var indexStatistics: [String: IndexStatistics] = [:]
var lastIndexCompaction: [String: Date] = [:]
var materializedViewCache: [String: [[String: Value]]] = [:]
let materializedViewLock = NSLock()
```

**Detailed Analysis:**

#### `cachedTableStats: [String: HeapFragmentationStats]`
- **Purpose**: Caches fragmentation statistics for tables
- **Key**: Table name
- **Value**: `HeapFragmentationStats` struct
- **Design Rationale**: Avoids expensive recalculation of fragmentation metrics
- **Update Strategy**: Updated during maintenance operations
- **Memory Trade-off**: Caches data vs. memory usage

#### `tableStatistics: [String: TableStatistics]`
- **Purpose**: Stores table-level statistics for query optimization
- **Key**: Table name
- **Value**: `TableStatistics` struct
- **Usage**: Query planner uses these for cost estimation
- **Update Frequency**: Updated during ANALYZE operations
- **Performance Impact**: Critical for query optimization

#### `indexStatistics: [String: IndexStatistics]`
- **Purpose**: Stores index-level statistics
- **Key**: Index name
- **Value**: `IndexStatistics` struct
- **Usage**: Index selection and maintenance decisions
- **Cardinality**: Tracks unique value counts
- **Selectivity**: Measures index effectiveness

#### `lastIndexCompaction: [String: Date]`
- **Purpose**: Tracks when each index was last compacted
- **Key**: Index name
- **Value**: Last compaction timestamp
- **Usage**: Determines when index maintenance is needed
- **Maintenance**: Prevents excessive compaction operations

#### `materializedViewCache: [String: [[String: Value]]]`
- **Purpose**: Caches results of materialized views
- **Key**: View name
- **Value**: Array of rows (array of column-value pairs)
- **Design Rationale**: Avoids recomputing expensive views
- **Memory Management**: Requires careful cache invalidation
- **Concurrency**: Protected by `materializedViewLock`

### Constraint Management

```swift
// MARK: - Constraint management
public var constraintManager: ConstraintManager
```

**Analysis:**
- **Public Access**: Allows external access for constraint operations
- **Centralized**: Single point for all constraint management
- **Integration**: Works with storage and transaction layers
- **Performance**: Constraints are checked during data modification

### Policy and Optimization

```swift
// MARK: - Policies & optimizer
var policyStore: InMemoryPolicyStore
let simulator: SimpleOptimizationSimulator
let mvcc = MVCCManager()
let lockManager: LockManager
let serialClock = SerializableClock()
```

**Detailed Analysis:**

#### `policyStore: InMemoryPolicyStore`
- **Purpose**: Stores database policies (retention, compression, etc.)
- **Type**: In-memory store for fast policy lookup
- **Usage**: Applied during data operations
- **Performance**: O(1) policy lookup

#### `simulator: SimpleOptimizationSimulator`
- **Purpose**: Simulates query execution for optimization
- **Usage**: Cost-based query optimization
- **Algorithm**: Estimates execution cost without running queries
- **Integration**: Works with query planner

#### `mvcc: MVCCManager`
- **Purpose**: Manages Multi-Version Concurrency Control
- **Design**: Enables concurrent reads without blocking
- **Implementation**: Maintains multiple versions of data
- **Performance**: Reduces lock contention

#### `lockManager: LockManager`
- **Purpose**: Manages database locks
- **Features**: Deadlock detection, timeout handling
- **Integration**: Works with MVCC for concurrency control
- **Performance**: Optimized for high concurrency

#### `serialClock: SerializableClock`
- **Purpose**: Provides serializable transaction ordering
- **Usage**: Ensures transaction ordering for serializable isolation
- **Algorithm**: Lamport clock or similar timestamping
- **Consistency**: Maintains ACID properties

### Transaction Context

```swift
struct TransactionContext {
    let isolation: IsolationLevel
    let snapshotCutoff: UInt64
    let clockTimestamp: UInt64
}

var txContexts: [UInt64: TransactionContext] = [:]
var lastCommittedClockTimestamp: UInt64 = 0
```

**Detailed Analysis:**

#### `TransactionContext` Struct
- **`isolation: IsolationLevel`**: Transaction isolation level (READ_COMMITTED, REPEATABLE_READ, SERIALIZABLE)
- **`snapshotCutoff: UInt64`**: Point-in-time snapshot for MVCC
- **`clockTimestamp: UInt64`**: Transaction start timestamp
- **Immutability**: `let` ensures context cannot be modified after creation

#### `txContexts: [UInt64: TransactionContext]`
- **Key**: Transaction ID (UInt64)
- **Value**: Transaction context
- **Purpose**: Tracks active transaction state
- **Memory**: Grows with number of active transactions
- **Cleanup**: Must be cleaned up when transactions complete

### Transaction State Management

```swift
// MARK: - Transaction state
var nextTID: UInt64 = 1
var activeTIDs: Set<UInt64> = []
struct TxOp { 
    enum Kind { case insert, delete }
    let kind: Kind
    let table: String
    let rid: RID
    let row: Row
}
struct TxState {
    var ops: [TxOp] = []
    var savepoints: [String: Int] = [:]
}
var txStates: [UInt64: TxState] = [:]
var preparedTransactions: Set<UInt64> = []
var txLastLSN: [UInt64: UInt64] = [:]
```

**Detailed Analysis:**

#### `nextTID: UInt64`
- **Purpose**: Generates unique transaction IDs
- **Initialization**: Starts at 1
- **Increment**: Atomically incremented for each new transaction
- **Uniqueness**: Ensures no two transactions have the same ID

#### `activeTIDs: Set<UInt64>`
- **Purpose**: Tracks currently active transactions
- **Type**: Set for O(1) lookup and insertion
- **Usage**: Prevents cleanup of active transactions
- **Memory**: Grows with concurrent transaction count

#### `TxOp` Struct
```swift
struct TxOp { 
    enum Kind { case insert, delete }
    let kind: Kind
    let table: String
    let rid: RID
    let row: Row
}
```

**Field Analysis:**
- **`kind: Kind`**: Operation type (insert or delete)
- **`table: String`**: Target table name
- **`rid: RID`**: Record identifier (page ID + slot ID)
- **`row: Row`**: Data being inserted or deleted
- **Immutability**: All fields are `let` for thread safety

#### `TxState` Struct
```swift
struct TxState {
    var ops: [TxOp] = []
    var savepoints: [String: Int] = [:]
}
```

**Field Analysis:**
- **`ops: [TxOp]`**: Array of operations in transaction
- **`savepoints: [String: Int]`**: Named savepoints with operation indices
- **Usage**: Enables transaction rollback to specific points
- **Memory**: Grows with transaction size

#### `txStates: [UInt64: TxState]`
- **Key**: Transaction ID
- **Value**: Transaction state
- **Purpose**: Maintains per-transaction state
- **Cleanup**: Must be cleaned up when transactions complete

### Dirty Page Tracking

```swift
// Dirty Page Table: pageId -> recLSN
var dpt: [UInt64: UInt64] = [:]
```

**Analysis:**
- **Purpose**: Tracks which pages have been modified
- **Key**: Page ID (UInt64)
- **Value**: Recovery LSN (UInt64)
- **Usage**: ARIES recovery algorithm
- **Performance**: O(1) lookup for page dirty status

### Vacuum System

```swift
// MARK: - Vacuum background job state & metrics
var vacuumTimer: DispatchSourceTimer?
let vacuumQueue = DispatchQueue(label: "ColibriDB.Vacuum")
var vacuumPositions: [String: UInt64] = [:]
var vacuumPagesPerRun: Int = 32
public internal(set) var vacuumTotalPagesCompacted: Int = 0
public internal(set) var vacuumTotalBytesReclaimed: Int = 0
public internal(set) var vacuumRuns: Int = 0
public internal(set) var vacuumLastRun: Date? = nil
```

**Detailed Analysis:**

#### `vacuumTimer: DispatchSourceTimer?`
- **Purpose**: Schedules periodic vacuum operations
- **Type**: Optional timer for background processing
- **Usage**: Triggers vacuum at configured intervals
- **Memory**: Timer must be properly cancelled to prevent leaks

#### `vacuumQueue: DispatchQueue`
- **Purpose**: Dedicated queue for vacuum operations
- **Label**: "ColibriDB.Vacuum" for debugging
- **Concurrency**: Prevents vacuum from blocking main operations
- **Priority**: Can be configured for background processing

#### `vacuumPositions: [String: UInt64]`
- **Purpose**: Tracks vacuum progress per table
- **Key**: Table name
- **Value**: Last vacuumed position
- **Usage**: Enables incremental vacuuming
- **Persistence**: Should be persisted for crash recovery

#### Vacuum Metrics
- **`vacuumTotalPagesCompacted`**: Total pages compacted
- **`vacuumTotalBytesReclaimed`**: Total bytes reclaimed
- **`vacuumRuns`**: Number of vacuum runs
- **`vacuumLastRun`**: Timestamp of last vacuum
- **Visibility**: `public internal(set)` allows read access but prevents external modification

## Initialization Process

### Constructor Analysis

```swift
public init(config: DBConfig) {
    self.config = config
    self.lockManager = LockManager(defaultTimeout: config.lockTimeoutSeconds)
    self.policyStore = InMemoryPolicyStore()
    self.simulator = SimpleOptimizationSimulator()
    self.constraintManager = ConstraintManager()
    
    // Set global buffer quotas per namespace
    BufferNamespaceManager.shared.setQuota(group: "table", pages: config.dataBufferPoolPages)
    BufferNamespaceManager.shared.setQuota(group: "index", pages: config.indexBufferPoolPages)
```

**Step-by-Step Analysis:**

1. **Configuration Assignment**: `self.config = config`
   - Stores immutable configuration
   - Used throughout database lifecycle
   - Provides runtime behavior control

2. **Lock Manager Initialization**: `LockManager(defaultTimeout: config.lockTimeoutSeconds)`
   - Creates lock manager with configured timeout
   - Enables deadlock detection
   - Provides concurrency control

3. **Policy Store Initialization**: `InMemoryPolicyStore()`
   - Creates in-memory policy storage
   - Fast policy lookup
   - Runtime policy management

4. **Simulator Initialization**: `SimpleOptimizationSimulator()`
   - Creates query optimization simulator
   - Enables cost-based optimization
   - Simulates query execution

5. **Constraint Manager Initialization**: `ConstraintManager()`
   - Creates constraint management system
   - Handles data integrity
   - Integrates with storage layer

6. **Buffer Quota Configuration**:
   ```swift
   BufferNamespaceManager.shared.setQuota(group: "table", pages: config.dataBufferPoolPages)
   BufferNamespaceManager.shared.setQuota(group: "index", pages: config.indexBufferPoolPages)
   ```
   - Sets memory quotas for different components
   - Prevents memory exhaustion
   - Enables resource management

### WAL Initialization

```swift
if config.walEnabled {
    let walPath = URL(fileURLWithPath: config.dataDir).appendingPathComponent("wal.log").path
    self.wal = try? FileWAL(path: walPath)
    self.wal?.setFullFSync(enabled: config.walFullFSyncEnabled)
    self.wal?.setIOHints(enabled: config.ioSequentialReadHint)
    self.wal?.setCompression(config.walCompression)
}
```

**Analysis:**
- **Conditional**: Only initializes WAL if enabled
- **Path Construction**: Uses URL for safe path handling
- **Error Handling**: Uses `try?` for graceful failure
- **Configuration**: Applies WAL-specific settings
- **Performance**: Configures I/O hints and compression

### Catalog Initialization

```swift
// Load index catalog
let idxDir = URL(fileURLWithPath: config.dataDir).appendingPathComponent("indexes").path
self.indexCatalog = try? IndexCatalog(dir: idxDir)
let catalogPath = URL(fileURLWithPath: config.dataDir).appendingPathComponent("system_catalog.json").path
self.systemCatalog = try? SystemCatalog(path: catalogPath)

// Initialize multi-database catalog system
self.multiDatabaseCatalog = MultiDatabaseCatalog(database: self)
self.catalogManager = CatalogManager(database: self)

// Initialize catalog system
try? self.catalogManager?.initializeCatalog()
```

**Analysis:**
- **Index Catalog**: Loads existing index definitions
- **System Catalog**: Loads system metadata
- **Multi-Database Catalog**: Creates multi-database support
- **Catalog Manager**: Centralizes catalog operations
- **Initialization**: Sets up catalog system

### Bootstrap Process

```swift
bootstrapSystemCatalogTables()
bootstrapSystemCatalogRoles()
bootstrapSystemCatalogConfigurations()
if let defs = indexCatalog?.list() {
    for def in defs { try? restoreIndex(from: def) }
}
// Replay DB WAL to recover
try? replayDBWAL()
bootstrapMVCCState()
if config.autoCompactionEnabled {
    startVacuum(intervalSeconds: config.autoCompactionIntervalSeconds, pagesPerRun: config.autoCompactionPagesPerRun)
}
```

**Analysis:**
- **System Tables**: Creates system catalog tables
- **System Roles**: Sets up default roles and permissions
- **System Configurations**: Initializes system settings
- **Index Restoration**: Restores existing indexes
- **WAL Recovery**: Replays WAL for crash recovery
- **MVCC State**: Initializes MVCC state
- **Auto Compaction**: Starts background vacuum if enabled

## Memory Management

### Memory Layout

The Database class uses several memory management strategies:

1. **Value Types**: Structs like `TransactionContext`, `TxOp`, `TxState` are value types
2. **Reference Types**: Classes like `HeapTable`, `FileHeapTable` are reference types
3. **Collections**: Dictionaries and arrays for state management
4. **Locks**: NSLock for thread safety

### Memory Optimization

```swift
// Apple Silicon optimizations
private let logger = Logger(subsystem: "com.colibridb", category: "database")
```

- **Logger**: Uses `os.log` for efficient logging
- **Subsystem**: "com.colibridb" for log filtering
- **Category**: "database" for specific component logging
- **Performance**: Optimized for Apple Silicon

### Thread Safety

The Database class uses several synchronization mechanisms:

1. **NSLock**: `materializedViewLock` for view cache protection
2. **DispatchQueue**: `vacuumQueue` for background processing
3. **Atomic Operations**: Transaction ID generation
4. **MVCC**: Multi-version concurrency control
5. **Lock Manager**: Centralized lock management

## Performance Considerations

### Access Patterns

1. **Table Lookup**: O(1) for both memory and file tables
2. **Index Lookup**: O(1) for table, O(1) for index within table
3. **Transaction State**: O(1) for transaction ID lookup
4. **Statistics**: O(1) for cached statistics

### Memory Usage

1. **Tables**: Memory tables use more RAM but are faster
2. **File Tables**: File tables use less RAM but are slower
3. **Indexes**: Each index maintains its own data structures
4. **Statistics**: Cached statistics use additional memory
5. **Transactions**: Active transactions consume memory

### I/O Patterns

1. **WAL**: Sequential writes for durability
2. **File Tables**: Random access for data pages
3. **Indexes**: B+Tree for range queries, Hash for equality
4. **Recovery**: Sequential reads during WAL replay

## Error Handling

The Database class uses several error handling strategies:

1. **Graceful Degradation**: `try?` for non-critical operations
2. **Error Propagation**: Throws errors for critical operations
3. **Logging**: Uses Logger for error tracking
4. **Recovery**: WAL replay for crash recovery

## Integration Points

The Database class integrates with several components:

1. **Storage Layer**: HeapTable, FileHeapTable
2. **Index Layer**: Various index implementations
3. **Transaction Layer**: MVCC, LockManager
4. **Catalog Layer**: MultiDatabaseCatalog, CatalogManager
5. **WAL Layer**: FileWAL for durability
6. **Policy Layer**: InMemoryPolicyStore
7. **Optimization Layer**: SimpleOptimizationSimulator

## Future Extensions

The Database class is designed for extensibility:

1. **New Index Types**: Can be added to IndexBackend enum
2. **New Storage Engines**: Can be added to storage layer
3. **New Transaction Types**: Can be added to transaction system
4. **New Policies**: Can be added to policy store
5. **New Catalogs**: Can be added to catalog system

---

*This analysis provides a comprehensive understanding of the Database class internals. For specific implementation details, see the corresponding source files.*
