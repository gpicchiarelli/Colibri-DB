# 🚀 Colibrì-DB Quick Start Guide

Get up and running with Colibrì-DB in 5 minutes!

---

## 📦 Prerequisites

- **macOS 13+** (Apple Silicon recommended)
- **Swift 6.0+**
- **Xcode 15+** or Swift toolchain

---

## ⚡ Installation

### Option 1: Build from Source (Recommended)

```bash
# Clone the repository
git clone https://github.com/gpicchiarelli/Colibri-DB.git
cd Colibri-DB

# Build the project
make build

# Run tests to verify installation
make test
```

### Option 2: Swift Package Manager

```bash
swift build
swift test
```

---

## 🎯 Basic Usage

### 1. Start the Database

```swift
import ColibriCore

// Create configuration
var config = DBConfig()
config.dataDir = "./my_database"
config.walEnabled = true

// Initialize database
let db = try Database(config: config)
```

### 2. Create a Table

```swift
try db.createTable("users")
```

### 3. Insert Data

```swift
let tid = try db.begin()

let row: Row = [
    "id": .int(1),
    "name": .string("Alice"),
    "age": .int(30),
    "email": .string("alice@example.com")
]

try db.insert(table: "users", row: row, tid: tid)
try db.commit(tid)
```

### 4. Query Data

```swift
// Scan all rows
let results = try db.scan(table: "users")

for (rid, row) in results {
    print("User: \(row["name"] ?? .null)")
}
```

### 5. Create an Index

```swift
try db.createIndex(
    table: "users",
    name: "idx_name",
    columns: ["name"],
    indexType: "BTree"
)
```

### 6. Search Using Index

```swift
let results = try db.indexSearch(
    table: "users",
    index: "idx_name",
    key: "Alice"
)
```

---

## 📚 Advanced Features

### Transactions with MVCC

```swift
// Begin transaction
let tid = try db.begin()

// Multiple operations
try db.insert(table: "users", row: row1, tid: tid)
try db.update(table: "users", rid: rid, newRow: row2, tid: tid)

// Commit or rollback
try db.commit(tid)
// OR: try db.rollback(tid)
```

### Query with SQL (Basic)

```swift
let results = try db.executeSQL(
    "SELECT * FROM users WHERE age > 25"
)
```

### Performance Monitoring

```swift
// Get buffer pool stats
let stats = db.getBufferPoolStats()
print("Hit rate: \(stats.hitRate)%")

// Get transaction stats
let txStats = db.getTransactionStats()
print("Active transactions: \(txStats.active)")
```

---

## 🛠️ Configuration Options

### Basic Configuration

```swift
var config = DBConfig()
config.dataDir = "./data"                    // Data directory
config.pageSizeBytes = 8192                  // Page size (8KB)
config.walEnabled = true                     // Enable WAL
config.bufferPoolEnabled = true              // Enable buffer pool
```

### Performance Tuning

```swift
config.dataBufferPoolPages = 16384          // ~128MB buffer
config.indexBufferPoolPages = 4096          // ~32MB for indexes
config.autoCompactionEnabled = true         // Enable auto-compaction
config.lockTimeoutSeconds = 5.0             // Lock timeout
```

### Isolation Levels

```swift
config.defaultIsolationLevel = .readCommitted
// Options: .readUncommitted, .readCommitted, .repeatableRead, .serializable
```

---

## 🧪 Running Tests

```bash
# Run all tests
make test

# Run specific test suite
swift test --filter Storage
swift test --filter Concurrency
swift test --filter Integration

# Run with coverage
swift test --enable-code-coverage
```

---

## 📊 Benchmarking

```bash
# Run all benchmarks
make benchmark

# Specific benchmarks
swift run benchmarks --wal-throughput
swift run benchmarks --btree-lookups
swift run benchmarks --transaction-throughput
```

---

## 🐛 Troubleshooting

### "Permission denied" when creating database

```bash
# Ensure data directory is writable
mkdir -p ./data
chmod 755 ./data
```

### "File not found" errors

```swift
// Use absolute paths or ensure working directory is correct
let absolutePath = FileManager.default.currentDirectoryPath + "/data"
config.dataDir = absolutePath
```

### Performance issues

```swift
// Increase buffer pool size
config.dataBufferPoolPages = 32768  // 256MB

// Disable WAL for testing (not recommended for production)
config.walEnabled = false

// Enable compression
config.walCompression = .lzfse
```

---

## 🔒 Security Best Practices

1. **Use Prepared Statements** (when available):
```swift
// GOOD (when supported)
let stmt = try db.prepare("SELECT * FROM users WHERE id = $1")
try stmt.bind(parameters: ["$1": .int(userId)])
let results = try stmt.execute()
```

2. **Validate Input**:
```swift
// Always validate user input before inserting
func validateEmail(_ email: String) -> Bool {
    // Email validation logic
    return email.contains("@")
}
```

3. **Use Transactions**:
```swift
// Always use transactions for consistency
let tid = try db.begin()
defer {
    // Ensure cleanup
    try? db.rollback(tid)
}

// Your operations...
try db.commit(tid)
```

---

## 📈 Performance Tips

1. **Batch Operations**: Group multiple inserts in one transaction
2. **Use Indexes**: Create indexes on frequently queried columns
3. **Buffer Pool**: Size appropriately for your workload
4. **Compaction**: Run periodic compaction for heavily updated tables
5. **WAL**: Consider group commit settings for write-heavy workloads

---

## 🔗 Next Steps

- Read the [Full Documentation](docs/)
- Explore [Examples](Examples/)
- Check [API Reference](docs/wiki/API-Reference.md)
- Join [Discussions](https://github.com/gpicchiarelli/Colibri-DB/discussions)
- Report [Issues](https://github.com/gpicchiarelli/Colibri-DB/issues)

---

## 💬 Getting Help

- 📖 [Documentation](docs/)
- 💬 [GitHub Discussions](https://github.com/gpicchiarelli/Colibri-DB/discussions)
- 🐛 [Issue Tracker](https://github.com/gpicchiarelli/Colibri-DB/issues)
- 📧 [Email Support](mailto:support@colibridb.org)

---

## 📝 License

Colibrì-DB is licensed under the BSD 3-Clause License.

---

**Happy Database Building! 🎉**

