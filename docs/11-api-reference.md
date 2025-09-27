# API Reference

## Overview

This chapter provides comprehensive documentation for ColibrìDB's programmatic APIs, including Swift APIs, configuration options, and extension points.

## Swift API

### Core Database API

#### Database Class
The main entry point for database operations.

```swift
import ColibriCore

// Initialize database
let config = DBConfig(
    dataDir: "/path/to/data",
    maxConnectionsLogical: 100,
    maxConnectionsPhysical: 10
)
let database = try Database(config: config)

// Ensure data directory exists
try database.ensureDataDir()
```

#### Database Configuration
Configuration options for database initialization.

```swift
public struct DBConfig {
    public let dataDir: String
    public let maxConnectionsLogical: Int
    public let maxConnectionsPhysical: Int
    public let bufferPoolSize: String?
    public let enableWAL: Bool
    public let checkpointInterval: TimeInterval?
    public let logLevel: LogLevel?
    
    public init(
        dataDir: String,
        maxConnectionsLogical: Int = 100,
        maxConnectionsPhysical: Int = 10,
        bufferPoolSize: String? = nil,
        enableWAL: Bool = true,
        checkpointInterval: TimeInterval? = nil,
        logLevel: LogLevel? = nil
    )
}
```

#### Database Operations
Core database operations.

```swift
// Create database
try database.createDatabase("myapp")

// Drop database
try database.dropDatabase("myapp")

// List databases
let databases = try database.listDatabases()

// Switch database
try database.useDatabase("myapp")
```

### Table Management API

#### Table Operations
Create, modify, and manage tables.

```swift
// Create table with schema
let schema = CatalogTableSchema(
    columns: [
        CatalogColumnDefinition(name: "id", type: .int, nullable: false),
        CatalogColumnDefinition(name: "name", type: .string, nullable: false),
        CatalogColumnDefinition(name: "email", type: .string, nullable: true)
    ],
    primaryKey: PrimaryKeyDefinition(columns: ["id"]),
    uniqueKeys: [UniqueKeyDefinition(columns: ["email"])]
)
try database.createTable("users", in: "myapp", schema: schema)

// Drop table
try database.dropTable("users", in: "myapp")

// List tables
let tables = try database.listTables(in: "myapp")

// Get table info
let tableInfo = try database.getTableInfo("users", in: "myapp")
```

#### Schema Management
Modify table schemas.

```swift
// Add column
try database.addColumn("phone", type: .string, to: "users", in: "myapp")

// Modify column
try database.modifyColumn("email", type: .string, length: 255, in: "users", in: "myapp")

// Drop column
try database.dropColumn("phone", from: "users", in: "myapp")

// Add constraint
try database.addConstraint(
    CheckConstraintDefinition(
        name: "chk_age",
        expression: "age >= 0"
    ),
    to: "users",
    in: "myapp"
)
```

### Data Manipulation API

#### Insert Operations
Insert data into tables.

```swift
// Insert single row
let row: Row = [
    "id": .int(1),
    "name": .string("John Doe"),
    "email": .string("john@example.com")
]
let rid = try database.insert(into: "users", row: row)

// Insert multiple rows
let rows: [Row] = [
    ["id": .int(1), "name": .string("John"), "email": .string("john@example.com")],
    ["id": .int(2), "name": .string("Jane"), "email": .string("jane@example.com")]
]
let rids = try database.insert(into: "users", rows: rows)
```

#### Query Operations
Query data from tables.

```swift
// Select all rows
let rows = try database.select(from: "users")

// Select with conditions
let rows = try database.select(
    from: "users",
    where: "age > 25"
)

// Select specific columns
let rows = try database.select(
    columns: ["name", "email"],
    from: "users",
    where: "age > 25"
)
```

#### Update Operations
Update existing data.

```swift
// Update single row
let updated = try database.update(
    table: "users",
    set: ["name": .string("John Smith")],
    where: "id = 1"
)

// Update multiple rows
let updated = try database.update(
    table: "users",
    set: ["age": .int(30)],
    where: "age < 18"
)
```

#### Delete Operations
Delete data from tables.

```swift
// Delete single row
let deleted = try database.delete(
    from: "users",
    where: "id = 1"
)

// Delete multiple rows
let deleted = try database.delete(
    from: "users",
    where: "age < 18"
)
```

### Index Management API

#### Index Operations
Create and manage indexes.

```swift
// Create B+Tree index
try database.createIndex(
    "idx_users_age",
    on: "users",
    columns: ["age"],
    type: .btree,
    in: "myapp"
)

// Create hash index
try database.createIndex(
    "idx_users_email",
    on: "users",
    columns: ["email"],
    type: .hash,
    in: "myapp"
)

// Create composite index
try database.createIndex(
    "idx_orders_user_date",
    on: "orders",
    columns: ["user_id", "order_date"],
    type: .btree,
    in: "myapp"
)

// Drop index
try database.dropIndex("idx_users_age", on: "users", in: "myapp")
```

#### Index Management
Maintain and optimize indexes.

```swift
// Rebuild index
try database.rebuildIndex("idx_users_email", on: "users", in: "myapp")

// Validate index
let isValid = try database.validateIndex("idx_users_email", on: "users", in: "myapp")

// Get index statistics
let stats = try database.getIndexStats("idx_users_email", on: "users", in: "myapp")
```

### Transaction API

#### Transaction Management
Manage database transactions.

```swift
// Begin transaction
let tid = try database.beginTransaction()

// Commit transaction
try database.commitTransaction(tid)

// Rollback transaction
try database.rollbackTransaction(tid)

// Get current transaction
let currentTid = database.currentTransaction
```

#### Transaction Operations
Perform operations within transactions.

```swift
// Insert within transaction
let tid = try database.beginTransaction()
let rid = try database.insert(into: "users", row: row, tid: tid)
try database.commitTransaction(tid)

// Update within transaction
let tid = try database.beginTransaction()
let updated = try database.update(
    table: "users",
    set: ["name": .string("John Smith")],
    where: "id = 1",
    tid: tid
)
try database.commitTransaction(tid)
```

### Multi-Database Catalog API

#### Catalog Management
Manage database catalogs.

```swift
// Get catalog manager
let catalog = database.multiDatabaseCatalog

// Create database
try catalog.createDatabase("myapp")

// Drop database
try catalog.dropDatabase("myapp")

// List databases
let databases = try catalog.listDatabases()
```

#### Schema Management
Manage database schemas.

```swift
// Create table
try catalog.createTable("users", in: "myapp", schema: schema)

// Drop table
try catalog.dropTable("users", in: "myapp")

// List tables
let tables = try catalog.listTables(in: "myapp")
```

## Data Types

### Value Types
Core data types supported by ColibrìDB.

```swift
public enum Value: Codable, Hashable, CustomStringConvertible, Sendable {
    case int(Int64)
    case double(Double)
    case bool(Bool)
    case string(String)
    case null
    case date(Date)
    case decimal(Decimal)
    case blob(Data)
    case json(Data)
    case enumValue(String, String)
}
```

### Row Type
Represents a row of data.

```swift
public typealias Row = [String: Value]

// Create row
let row: Row = [
    "id": .int(1),
    "name": .string("John Doe"),
    "email": .string("john@example.com"),
    "age": .int(30),
    "is_active": .bool(true)
]
```

### Schema Types
Schema definition types.

```swift
// Table schema
public struct CatalogTableSchema {
    public let columns: [CatalogColumnDefinition]
    public let primaryKey: PrimaryKeyDefinition?
    public let uniqueKeys: [UniqueKeyDefinition]
    public let foreignKeys: [ForeignKeyDefinition]
    public let checkConstraints: [CheckConstraintDefinition]
}

// Column definition
public struct CatalogColumnDefinition {
    public let name: String
    public let type: DataType
    public let nullable: Bool
    public let defaultValue: Value?
    public let autoIncrement: Bool
    public let comment: String?
}
```

## Configuration API

### Database Configuration
Configuration options for database initialization.

```swift
public struct DBConfig {
    // Data directory
    public let dataDir: String
    
    // Connection limits
    public let maxConnectionsLogical: Int
    public let maxConnectionsPhysical: Int
    
    // Memory settings
    public let bufferPoolSize: String?
    public let maxQueryMemory: String?
    public let sortMemory: String?
    public let hashJoinMemory: String?
    
    // WAL settings
    public let enableWAL: Bool
    public let checkpointInterval: TimeInterval?
    
    // Logging
    public let logLevel: LogLevel?
    public let logFile: String?
    
    // Performance
    public let enableSIMD: Bool
    public let parallelWorkers: Int
    public let prefetchPages: Int
    public let batchSize: Int
    
    // Storage
    public let pageSize: Int
    public let maxFileSize: String?
    public let compressionEnabled: Bool
    public let encryptionEnabled: Bool
}
```

### Logging Configuration
Logging configuration options.

```swift
public enum LogLevel: String, CaseIterable {
    case debug = "DEBUG"
    case info = "INFO"
    case warn = "WARN"
    case error = "ERROR"
}

public struct LogConfig {
    public let level: LogLevel
    public let file: String?
    public let maxSize: String?
    public let maxFiles: Int
    public let format: LogFormat
}
```

## Error Handling

### Error Types
Comprehensive error types for different scenarios.

```swift
public enum ColibriError: Error {
    case databaseNotFound(String)
    case tableNotFound(String)
    case columnNotFound(String)
    case indexNotFound(String)
    case constraintViolation(String)
    case transactionError(String)
    case connectionError(String)
    case storageError(String)
    case parseError(String)
    case executionError(String)
    case configurationError(String)
    case permissionError(String)
    case resourceError(String)
    case internalError(String)
}
```

### Error Handling
Best practices for error handling.

```swift
do {
    let database = try Database(config: config)
    try database.ensureDataDir()
    let rid = try database.insert(into: "users", row: row)
} catch ColibriError.databaseNotFound(let name) {
    print("Database '\(name)' not found")
} catch ColibriError.tableNotFound(let name) {
    print("Table '\(name)' not found")
} catch ColibriError.constraintViolation(let message) {
    print("Constraint violation: \(message)")
} catch {
    print("Unexpected error: \(error)")
}
```

## Extension Points

### Plugin System
Extend ColibrìDB with custom functionality.

```swift
// Data structure plugin
public protocol DataStructurePlugin {
    func createIndex(name: String, columns: [String], options: [String: Any]) throws -> Index
    func dropIndex(name: String) throws
    func insert(key: Value, value: Value) throws
    func lookup(key: Value) throws -> Value?
    func range(lower: Value, upper: Value) throws -> [Value]
}

// Storage plugin
public protocol StoragePlugin {
    func readPage(pageId: UInt64) throws -> Data
    func writePage(pageId: UInt64, data: Data) throws
    func allocatePage() throws -> UInt64
    func deallocatePage(pageId: UInt64) throws
}

// Query plugin
public protocol QueryPlugin {
    func parse(query: String) throws -> QueryAST
    func plan(query: QueryAST) throws -> QueryPlan
    func execute(plan: QueryPlan) throws -> [Row]
}
```

### Custom Data Types
Define custom data types.

```swift
// Custom data type
public struct CustomType: ValueType {
    public let value: String
    
    public init(_ value: String) {
        self.value = value
    }
    
    public func encode(to encoder: Encoder) throws {
        var container = encoder.singleValueContainer()
        try container.encode(value)
    }
    
    public init(from decoder: Decoder) throws {
        let container = try decoder.singleValueContainer()
        value = try container.decode(String.self)
    }
}

// Register custom type
try database.registerCustomType("custom", type: CustomType.self)
```

### Custom Functions
Define custom SQL functions.

```swift
// Custom function
public struct CustomFunction: SQLFunction {
    public let name: String
    public let arity: Int
    public let returnType: DataType
    
    public func evaluate(args: [Value]) throws -> Value {
        // Custom function implementation
        return .string("custom result")
    }
}

// Register custom function
try database.registerFunction(CustomFunction(name: "custom_func", arity: 1, returnType: .string))
```

## Performance APIs

### Profiling API
Profile database operations.

```swift
// Start profiling
let profiler = try database.startProfiling()

// Run operations
let rid = try database.insert(into: "users", row: row)

// Stop profiling
let results = try profiler.stop()

// Get profiling results
print("Total time: \(results.totalTime)")
print("Memory usage: \(results.memoryUsage)")
print("CPU usage: \(results.cpuUsage)")
```

### Monitoring API
Monitor database performance.

```swift
// Get performance metrics
let metrics = try database.getPerformanceMetrics()

// Get memory usage
let memoryUsage = try database.getMemoryUsage()

// Get query statistics
let queryStats = try database.getQueryStatistics()

// Get index statistics
let indexStats = try database.getIndexStatistics()
```

### Benchmarking API
Benchmark database operations.

```swift
// Create benchmark suite
let suite = BenchmarkSuite(database: database)

// Add benchmark
suite.addBenchmark("insert", operation: {
    try database.insert(into: "users", row: row)
})

// Run benchmark
let results = try suite.run(iterations: 1000)

// Get results
print("Operations per second: \(results.operationsPerSecond)")
print("Average time: \(results.averageTime)")
print("Total time: \(results.totalTime)")
```

## Testing APIs

### Test Framework
Built-in testing framework.

```swift
// Create test suite
let testSuite = TestSuite(database: database)

// Add unit test
testSuite.addUnitTest("test_insert") {
    let row: Row = ["id": .int(1), "name": .string("John")]
    let rid = try database.insert(into: "users", row: row)
    assert(rid != nil)
}

// Add integration test
testSuite.addIntegrationTest("test_transaction") {
    let tid = try database.beginTransaction()
    let rid = try database.insert(into: "users", row: row, tid: tid)
    try database.commitTransaction(tid)
    assert(rid != nil)
}

// Run tests
let results = try testSuite.run()
print("Tests passed: \(results.passedCount)")
print("Tests failed: \(results.failedCount)")
```

### Mock Data
Generate mock data for testing.

```swift
// Create data generator
let generator = DataGenerator(database: database)

// Generate users
let users = try generator.generateUsers(count: 1000)

// Generate orders
let orders = try generator.generateOrders(count: 5000)

// Generate with specific patterns
let users = try generator.generateUsers(
    count: 1000,
    patterns: [
        "name": .randomString(length: 10),
        "email": .email,
        "age": .randomInt(min: 18, max: 65)
    ]
)
```

## Security APIs

### Authentication
User authentication and management.

```swift
// Create user
try database.createUser("john", password: "password123")

// Authenticate user
let authenticated = try database.authenticate("john", password: "password123")

// Change password
try database.changePassword("john", newPassword: "newpassword123")

// Delete user
try database.deleteUser("john")
```

### Authorization
Permission management.

```swift
// Grant permissions
try database.grantPermission("john", on: "myapp", permission: .select)
try database.grantPermission("john", on: "myapp.users", permission: .insert)

// Revoke permissions
try database.revokePermission("john", on: "myapp", permission: .select)

// Check permissions
let canSelect = try database.hasPermission("john", on: "myapp", permission: .select)
```

### Encryption
Data encryption and decryption.

```swift
// Enable encryption
try database.enableEncryption(algorithm: .aes256, key: encryptionKey)

// Encrypt data
let encrypted = try database.encrypt(data: sensitiveData)

// Decrypt data
let decrypted = try database.decrypt(encryptedData: encrypted)
```

## Backup and Recovery APIs

### Backup Operations
Create and manage backups.

```swift
// Create full backup
try database.createBackup("backup_20230120", type: .full)

// Create incremental backup
try database.createBackup("backup_20230120_incr", type: .incremental)

// List backups
let backups = try database.listBackups()

// Verify backup
let isValid = try database.verifyBackup("backup_20230120")
```

### Recovery Operations
Restore from backups.

```swift
// Restore from backup
try database.restoreFromBackup("backup_20230120")

// Restore to point in time
try database.restoreToPointInTime("backup_20230120", timestamp: Date())

// Restore specific tables
try database.restoreTables(["users", "orders"], from: "backup_20230120")
```

## Migration APIs

### Schema Migration
Migrate database schemas.

```swift
// Create migration
let migration = SchemaMigration()
migration.addTable("users", schema: userSchema)
migration.addIndex("idx_users_email", on: "users", columns: ["email"])

// Apply migration
try database.applyMigration(migration)

// Rollback migration
try database.rollbackMigration(migration)
```

### Data Migration
Migrate data between databases.

```swift
// Create data migration
let migration = DataMigration(from: sourceDatabase, to: targetDatabase)
migration.addTable("users")
migration.addTable("orders")

// Execute migration
try migration.execute()

// Verify migration
let verified = try migration.verify()
```

## Next Steps

Now that you understand the APIs:

- [Core Concepts](04-core-concepts.md) - Understand the fundamental concepts
- [Database Management](05-database-management.md) - Apply APIs to manage databases
- [Performance Tuning](09-performance-tuning.md) - Use APIs for optimization

---

*For advanced API usage and custom extensions, see the [Contributing](12-contributing.md) guide.*
