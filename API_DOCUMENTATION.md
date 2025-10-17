# 📖 Colibrì-DB API Documentation

Complete API reference for Colibrì-DB

---

## 🗄️ Core Database API

### Database Class

The main entry point for all database operations.

```swift
public final class Database {
    public init(config: DBConfig) throws
    public func close() throws
}
```

#### Table Operations

```swift
// Create a new table
func createTable(_ name: String) throws

// Drop an existing table
func dropTable(_ name: String) throws

// List all tables
func listTables() -> [String]
```

#### Data Manipulation

```swift
// Insert a row (requires transaction)
func insert(table: String, row: Row, tid: UInt64) throws -> RID

// Read a specific row
func read(table: String, rid: RID, tid: UInt64? = nil) throws -> Row

// Update a row (requires transaction)
func update(table: String, rid: RID, newRow: Row, tid: UInt64) throws

// Delete a row (requires transaction)
func delete(table: String, rid: RID, tid: UInt64) throws

// Scan all rows in a table
func scan(table: String, tid: UInt64? = nil) throws -> [(rid: RID, row: Row)]
```

#### Transaction Management

```swift
// Begin a new transaction
func begin(isolation: IsolationLevel = .readCommitted) throws -> UInt64

// Commit a transaction
func commit(_ tid: UInt64) throws

// Rollback a transaction  
func rollback(_ tid: UInt64) throws

// Create a savepoint
func setSavepoint(tid: UInt64, name: String) throws

// Rollback to savepoint
func rollbackToSavepoint(tid: UInt64, name: String) throws
```

#### Index Operations

```swift
// Create an index
func createIndex(
    table: String,
    name: String,
    columns: [String],
    indexType: String
) throws

// Search using an index
func indexSearch(
    table: String,
    index: String,
    key: String
) throws -> [(rid: RID, row: Row)]

// Drop an index
func dropIndex(table: String, name: String) throws
```

---

## 🔧 Configuration API

### DBConfig Struct

```swift
public struct DBConfig: Codable {
    public var dataDir: String                     // Data directory path
    public var maxConnectionsLogical: Int          // Max logical connections
    public var maxConnectionsPhysical: Int         // Max physical connections
    public var bufferPoolSizeBytes: UInt64         // Buffer pool size
    public var pageSizeBytes: Int                  // Page size (typically 8192)
    public var walEnabled: Bool                    // Enable WAL
    public var checksumEnabled: Bool               // Enable checksums
    public var cliEnabled: Bool                    // Enable CLI
    public var metricsEnabled: Bool                // Enable metrics
    public var serverEnabled: Bool                 // Enable server mode
    public var indexImplementation: String         // Default index type
    public var storageEngine: String               // Storage engine type
}
```

### Loading Configuration

```swift
// Load from JSON file
let config = try ConfigIO.load(from: "colibridb.conf.json")

// Save to JSON file
try ConfigIO.save(config, to: "colibridb.conf.json")

// Use defaults
let config = DBConfig()
```

---

## 📊 Types and Values

### Row Type

```swift
public typealias Row = [String: Value]
```

### Value Enum

```swift
public enum Value: Codable {
    case int(Int64)
    case double(Double)
    case bool(Bool)
    case string(String)
    case null
    case decimal(Decimal)
    case date(Date)
}
```

### RID (Record Identifier)

```swift
public struct RID: Hashable, Codable {
    public let pageId: UInt64
    public let slotId: UInt16
}
```

---

## 🔒 Isolation Levels

```swift
public enum IsolationLevel: String, Codable {
    case readUncommitted
    case readCommitted      // Default
    case repeatableRead
    case serializable
}
```

**Usage:**
```swift
let tid = try db.begin(isolation: .repeatableRead)
```

---

## 📈 Performance Monitoring

### Get Statistics

```swift
// Buffer pool statistics
let bufferStats = db.getBufferPoolStats()
print("Hit rate: \(bufferStats.hitRate)%")

// Transaction statistics
let txStats = db.getTransactionStats()
print("Active: \(txStats.activeTx)")

// Table statistics
let tableStats = try db.getTableStatistics("users")
print("Rows: \(tableStats.rowCount)")
```

---

## 🛠️ Utility APIs

### PathValidator

```swift
// Validate a path
let safePath = try PathValidator.validatePath(userInput)

// Create safe path
let fullPath = try PathValidator.createSafePath(
    baseDir: dataDir,
    filename: "table.dat"
)
```

### MemoryOptimizer

```swift
let optimizer = MemoryOptimizer()

// Collect statistics
let stats = optimizer.collectStats()

// Get optimization actions
let actions = optimizer.optimize(stats: stats)

// Apply actions
for action in actions {
    switch action {
    case "compact_heap":
        try db.compactTable("users")
    case "adjust_buffer_pool":
        // Adjust buffer pool size
    default:
        break
    }
}
```

---

## 🎯 Complete Example

```swift
import ColibriCore

// 1. Configure
var config = DBConfig()
config.dataDir = "./my_database"
config.walEnabled = true
config.defaultIsolationLevel = .readCommitted

// 2. Initialize
let db = try Database(config: config)
defer { try? db.close() }

// 3. Create schema
try db.createTable("users")
try db.createIndex(
    table: "users",
    name: "idx_email",
    columns: ["email"],
    indexType: "BTree"
)

// 4. Insert data
let tid = try db.begin()

let user1RID = try db.insert(
    table: "users",
    row: [
        "id": .int(1),
        "name": .string("Alice"),
        "email": .string("alice@example.com"),
        "age": .int(30)
    ],
    tid: tid
)

// 5. Query
let allUsers = try db.scan(table: "users", tid: tid)
print("Users: \(allUsers.count)")

// 6. Update
try db.update(
    table: "users",
    rid: user1RID,
    newRow: [
        "id": .int(1),
        "name": .string("Alice Smith"),
        "email": .string("alice@example.com"),
        "age": .int(31)
    ],
    tid: tid
)

// 7. Commit
try db.commit(tid)

// 8. Index search
let results = try db.indexSearch(
    table: "users",
    index: "idx_email",
    key: "alice@example.com"
)

print("Found: \(results.count) users")
```

---

## 🚨 Error Handling

### Error Types

```swift
public enum DBError: Error {
    case io(String)              // I/O errors
    case config(String)          // Configuration errors
    case invalidArgument(String) // Invalid parameters
    case notFound(String)        // Resource not found
    case conflict(String)        // Conflicts (duplicate keys, etc.)
    case deadlock(String)        // Deadlock detected
    case lockTimeout(String)     // Lock timeout exceeded
}
```

### Handling Errors

```swift
do {
    try db.insert(table: "users", row: row, tid: tid)
    try db.commit(tid)
} catch DBError.conflict(let msg) {
    print("Conflict: \(msg)")
    try db.rollback(tid)
} catch DBError.deadlock(let cycle) {
    print("Deadlock: \(cycle)")
    try db.rollback(tid)
} catch {
    print("Error: \(error)")
    try? db.rollback(tid)
}
```

---

## 🔗 See Also

- [Quick Start Guide](QUICK_START.md)
- [Contributing Guide](CONTRIBUTING_EXTENDED.md)
- [Full Documentation](docs/wiki/)
- [Examples](Examples/)

---

*Last updated: 17 Ottobre 2025*

