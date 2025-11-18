# RFC 0040: Catalog Manager (System Catalog)

**Status**: Standards Track  
**Author**: ColibrìDB Team  
**Date**: 2025-11-18  
**TLA+ Spec**: `spec/Catalog.tla`

## Abstract

This RFC defines the Catalog Manager component, the **foundation** of ColibrìDB. The System Catalog is the single source of truth for ALL database metadata, including table schemas, indexes, statistics, user permissions, system configurations, and more. **Every component in ColibrìDB depends on the Catalog** to function correctly.

## 1. Introduction

The Catalog Manager is the **most critical component** in ColibrìDB. It serves as the foundation for all other components by providing centralized metadata management. **Nothing in ColibrìDB operates without consulting the Catalog first.**

### 1.1 Purpose and Goals

The primary goals of the Catalog Manager are:

1. **Single Source of Truth**: Central repository for ALL database metadata
2. **Foundation for All Components**: Every component depends on Catalog for metadata
3. **Schema Management**: Manage table schemas, columns, constraints, indexes
4. **Statistics Management**: Track statistics for query optimization
5. **User Management**: Manage users, roles, and permissions
6. **System Configuration**: Store system-wide configurations
7. **Durability**: Catalog must survive crashes (persisted to disk)
8. **Consistency**: All metadata changes must be atomic and consistent

### 1.2 Problem Statement

Database systems need to:

- **Track Metadata**: Know what tables, columns, indexes exist
- **Validate Operations**: Verify table/index existence before operations
- **Optimize Queries**: Use statistics for query optimization
- **Manage Permissions**: Control access to tables/columns
- **Maintain Consistency**: Ensure metadata is always consistent
- **Survive Crashes**: Catalog must be durable

The Catalog Manager solves these challenges by:

- **Centralized Metadata**: Single source of truth for all metadata
- **System Tables**: Catalog itself stored in system tables (bootstrapped)
- **Transaction Integration**: Metadata changes are transactional
- **Persistence**: Catalog persisted to disk for durability
- **Validation**: All operations validate against Catalog first

### 1.3 Key Concepts

**System Catalog**: Central repository for ALL database metadata.

**Catalog Tables**: System tables that store the Catalog itself:
- **`colibri_tables`**: Table definitions
- **`colibri_columns`**: Column definitions per table
- **`colibri_indexes`**: Index definitions
- **`colibri_statistics`**: Table statistics
- **`colibri_users`**: User accounts
- **`colibri_roles`**: Role definitions
- **`colibri_permissions`**: Access permissions
- **`colibri_system_config`**: System configurations

**Metadata Types**:
- **Table Metadata**: Schema, columns, constraints, primary keys, foreign keys
- **Index Metadata**: Index type, columns, uniqueness
- **Statistics**: Row counts, distinct values, selectivities
- **User Metadata**: Users, roles, permissions
- **Configuration**: System-wide settings

**Schema Versioning**: Track schema changes with version numbers.

**Bootstrap Process**: Catalog must bootstrap itself (create system tables).

### 1.4 Relationship to Other Components

```
                    ┌─────────────────┐
                    │  Catalog        │
                    │  Manager        │
                    └────────┬────────┘
                             │
        ┌────────────────────┼────────────────────┐
        │                    │                    │
        ▼                    ▼                    ▼
┌──────────────┐    ┌──────────────┐    ┌──────────────┐
│   Storage    │    │    Index     │    │    Query     │
│   Manager    │    │   Manager    │    │  Optimizer   │
└──────────────┘    └──────────────┘    └──────────────┘
        │                    │                    │
        ▼                    ▼                    ▼
┌──────────────┐    ┌──────────────┐    ┌──────────────┐
│ Transaction  │    │  Authentication│   │   Statistics │
│   Manager    │    │   Manager     │   │   Manager    │
└──────────────┘    └──────────────┘    └──────────────┘
```

**EVERY Component → Catalog Manager**:
- **Storage Manager**: Gets table metadata before operations
- **Index Manager**: Gets index metadata before operations
- **Query Optimizer**: Uses statistics and metadata for optimization
- **Transaction Manager**: Validates operations against Catalog
- **Authentication Manager**: Uses user/role metadata for authorization
- **Statistics Manager**: Updates Catalog statistics

## 2. Design Principles

### 2.1 Single Source of Truth

**Invariant**: ALL metadata MUST come from Catalog.

```
\A component \in Components:
    component.metadataSource = Catalog
```

**No Direct Storage**: Components MUST NOT maintain their own metadata copies.

**Catalog-First**: Every operation MUST check Catalog first.

### 2.2 Bootstrap Process

**Self-Bootstrapping**: Catalog must create its own system tables.

**Bootstrap Sequence**:
1. Catalog starts empty (in-memory)
2. Catalog creates system tables (first operation)
3. System tables stored in special area
4. Catalog loads from system tables on restart
5. All operations go through Catalog

### 2.3 Durability Guarantee

**Invariant**: Catalog MUST survive crashes.

```
\A crash \in Crashes:
    AfterRecovery(Catalog) = BeforeCrash(Catalog)
```

**Persistence**: Catalog persisted to system tables.

**WAL Integration**: Catalog changes logged to WAL.

**Recovery**: Catalog reconstructed from WAL during recovery.

### 2.4 Transactional Consistency

**Invariant**: Catalog changes MUST be transactional.

```
\A catalogChange \in CatalogChanges:
    catalogChange.transactional = TRUE
```

**ACID Properties**: Catalog changes respect ACID.

**Isolation**: DDL operations isolated from DML operations.

**Atomicity**: Catalog changes all-or-nothing.

### 2.5 Apple-First Architecture

#### 2.5.1 Swift Actor Model

**Why Actors**: Thread-safe Catalog operations without explicit locking.

```swift
public actor CatalogManager {
    // All state isolated within actor
    private var tables: [String: TableMetadata] = [:]
    private var indexes: [String: IndexMetadata] = [:]
    
    // Methods automatically synchronized
    public func createTable(...) async throws {
        // Safe concurrent access
    }
}
```

**Benefits**:
- **Thread Safety**: No data races
- **No Locks**: Actors eliminate lock contention
- **Composable**: Easy to compose with other actors

#### 2.5.2 Async/Await

**Why Async/Await**: Catalog operations may involve I/O.

```swift
// Non-blocking catalog lookup
public func getTable(name: String) async -> TableMetadata? {
    // May read from system tables
    return tables[name]
}
```

**Benefits**:
- **Non-Blocking**: Threads not blocked on Catalog operations
- **Concurrent**: Supports thousands of concurrent lookups
- **Structured**: Clear error handling and control flow

#### 2.5.3 Value Types

**Why Value Types**: Immutable metadata structures are thread-safe.

```swift
public struct TableMetadata: Sendable {
    public let name: String
    public let columns: [ColumnMetadata]
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
CatalogManager (Swift Actor)
├── tables: [String -> TableMetadata]
│   ├── Purpose: Table schema definitions
│   ├── Type: Dictionary mapping table name to metadata
│   ├── Lifetime: Persists across restarts
│   └── Access: O(1) hash table lookup
│
├── indexes: [String -> IndexMetadata]
│   ├── Purpose: Index definitions
│   ├── Type: Dictionary mapping index name to metadata
│   ├── Lifetime: Persists across restarts
│   └── Access: O(1) hash table lookup
│
├── statistics: [String -> Statistics]
│   ├── Purpose: Table statistics for query optimization
│   ├── Type: Dictionary mapping table name to statistics
│   ├── Updates: Updated by Statistics Manager
│   └── Use: Query optimization cost estimation
│
├── users: [String -> UserMetadata]
│   ├── Purpose: User account information
│   ├── Type: Dictionary mapping username to user metadata
│   ├── Lifetime: Persists across restarts
│   └── Use: Authentication and authorization
│
├── roles: [String -> RoleMetadata]
│   ├── Purpose: Role definitions
│   ├── Type: Dictionary mapping role name to role metadata
│   ├── Lifetime: Persists across restarts
│   └── Use: Role-based access control (RBAC)
│
├── permissions: [String -> [Permission]]
│   ├── Purpose: Access permissions per user/role
│   ├── Type: Dictionary mapping user/role to permissions
│   ├── Lifetime: Persists across restarts
│   └── Use: Access control validation
│
├── systemConfig: SystemConfiguration
│   ├── Purpose: System-wide configuration
│   ├── Type: Configuration structure
│   ├── Updates: Updated by system administrator
│   └── Use: System behavior configuration
│
├── schemaVersion: Int
│   ├── Purpose: Track schema changes
│   ├── Type: Monotonically increasing integer
│   ├── Updates: Incremented on each schema change
│   └── Use: Schema evolution tracking
│
├── storageManager: StorageManager?
│   ├── Purpose: Persist Catalog to system tables
│   ├── Used: For Catalog persistence
│   └── Operations: readPage, writePage for system tables
│
└── isBootstrapped: Bool
    ├── Purpose: Track bootstrap completion
    ├── Type: Boolean flag
    └── Use: Ensure system tables exist
```

### 3.2 System Tables Structure

#### 3.2.1 `colibri_tables` System Table

**Purpose**: Store table definitions

**Schema**:
```sql
CREATE TABLE colibri_tables (
    table_name VARCHAR PRIMARY KEY,
    schema_version INT NOT NULL,
    created_at TIMESTAMP NOT NULL,
    metadata_json TEXT NOT NULL  -- TableMetadata JSON
)
```

**Usage**: All table metadata persisted here

#### 3.2.2 `colibri_columns` System Table

**Purpose**: Store column definitions

**Schema**:
```sql
CREATE TABLE colibri_columns (
    table_name VARCHAR NOT NULL,
    column_name VARCHAR NOT NULL,
    column_type VARCHAR NOT NULL,
    nullable BOOLEAN NOT NULL,
    default_value TEXT,
    ordinal_position INT NOT NULL,
    PRIMARY KEY (table_name, column_name)
)
```

**Usage**: All column metadata persisted here

#### 3.2.3 `colibri_indexes` System Table

**Purpose**: Store index definitions

**Schema**:
```sql
CREATE TABLE colibri_indexes (
    index_name VARCHAR PRIMARY KEY,
    table_name VARCHAR NOT NULL,
    columns TEXT NOT NULL,  -- JSON array of column names
    index_type VARCHAR NOT NULL,
    unique BOOLEAN NOT NULL,
    created_at TIMESTAMP NOT NULL
)
```

**Usage**: All index metadata persisted here

#### 3.2.4 `colibri_statistics` System Table

**Purpose**: Store table statistics

**Schema**:
```sql
CREATE TABLE colibri_statistics (
    table_name VARCHAR PRIMARY KEY,
    row_count BIGINT NOT NULL,
    avg_row_size INT NOT NULL,
    distinct_values TEXT,  -- JSON object
    last_updated TIMESTAMP NOT NULL
)
```

**Usage**: Statistics for query optimization

#### 3.2.5 `colibri_users` System Table

**Purpose**: Store user accounts

**Schema**:
```sql
CREATE TABLE colibri_users (
    username VARCHAR PRIMARY KEY,
    password_hash VARCHAR NOT NULL,
    created_at TIMESTAMP NOT NULL,
    last_login TIMESTAMP,
    is_active BOOLEAN NOT NULL
)
```

**Usage**: User authentication

#### 3.2.6 `colibri_roles` System Table

**Purpose**: Store role definitions

**Schema**:
```sql
CREATE TABLE colibri_roles (
    role_name VARCHAR PRIMARY KEY,
    description TEXT,
    created_at TIMESTAMP NOT NULL
)
```

**Usage**: Role-based access control

#### 3.2.7 `colibri_permissions` System Table

**Purpose**: Store access permissions

**Schema**:
```sql
CREATE TABLE colibri_permissions (
    grantee VARCHAR NOT NULL,  -- User or role
    grantee_type VARCHAR NOT NULL,  -- 'USER' or 'ROLE'
    table_name VARCHAR NOT NULL,
    permission_type VARCHAR NOT NULL,  -- 'SELECT', 'INSERT', etc.
    granted_at TIMESTAMP NOT NULL,
    PRIMARY KEY (grantee, table_name, permission_type)
)
```

**Usage**: Access control validation

#### 3.2.8 `colibri_system_config` System Table

**Purpose**: Store system configuration

**Schema**:
```sql
CREATE TABLE colibri_system_config (
    config_key VARCHAR PRIMARY KEY,
    config_value TEXT NOT NULL,
    description TEXT,
    updated_at TIMESTAMP NOT NULL
)
```

**Usage**: System-wide configuration

### 3.3 Bootstrap Process

#### 3.3.1 Bootstrap Sequence

```
┌──────────────────┐
│ Catalog Start    │
│ (Empty)          │
└──────┬───────────┘
       │
       ▼
   ┌──────────────┐
   │Check System  │
   │Tables Exist  │
   └───┬───────┬───┘
       │Yes    │No
       ▼       ▼
  ┌─────────┐ ┌──────────────┐
  │Load from│ │Bootstrap:    │
  │System   │ │Create System │
  │Tables   │ │Tables        │
  └───┬─────┘ └───┬──────────┘
      │           │
      └──────┬────┘
             ▼
      ┌──────────────┐
      │Catalog Ready │
      │(Bootstrapped)│
      └──────────────┘
```

#### 3.3.2 Bootstrap Implementation

```swift
private func bootstrapSystemTables() async throws {
    // 1. Create colibri_tables
    try await createSystemTable(
        name: "colibri_tables",
        columns: [
            ColumnMetadata(name: "table_name", type: .string, nullable: false),
            ColumnMetadata(name: "schema_version", type: .int, nullable: false),
            ColumnMetadata(name: "created_at", type: .date, nullable: false),
            ColumnMetadata(name: "metadata_json", type: .string, nullable: false)
        ],
        primaryKey: ["table_name"]
    )
    
    // 2. Create colibri_columns
    try await createSystemTable(...)
    
    // 3. Create colibri_indexes
    try await createSystemTable(...)
    
    // ... (all system tables)
    
    // Mark as bootstrapped
    isBootstrapped = true
}
```

### 3.4 Data Flow Diagrams

#### 3.4.1 Table Creation Flow

```
┌──────────────────┐
│createTable(...)  │
└──────┬───────────┘
       │
       ▼
   ┌──────────────┐
   │Validate      │
   │Metadata      │
   └───┬──────────┘
       │
       ▼
   ┌──────────────┐
   │Store in      │
   │Memory        │
   └───┬──────────┘
       │
       ▼
   ┌──────────────┐
   │Persist to    │
   │System Table  │
   └───┬──────────┘
       │
       ▼
   ┌──────────────┐
   │Log to WAL    │
   └───┬──────────┘
       │
       ▼
   ┌──────────────┐
   │Increment     │
   │Schema Version│
   └───┬──────────┘
       │
       ▼
   ┌──────────────┐
   │Notify        │
   │Components    │
   └──────────────┘
```

#### 3.4.2 Catalog Lookup Flow

```
┌──────────────────┐
│getTable(name)    │
└──────┬───────────┘
       │
       ▼
   ┌──────────────┐
   │Check Memory  │
   └───┬───────┬───┘
       │Hit    │Miss
       ▼       ▼
  ┌─────────┐ ┌──────────────┐
  │Return   │ │Load from     │
  │from     │ │System Table  │
  │Memory   │ └───┬──────────┘
  └─────────┘     │
                  ▼
          ┌──────────────┐
          │Cache in      │
          │Memory        │
          └───┬──────────┘
              │
              ▼
          ┌──────────────┐
          │Return        │
          │Metadata      │
          └──────────────┘
```

## 4. State Variables (TLA+ Mapping)

| Swift Variable | TLA+ Variable | Type | Description |
|----------------|---------------|------|-------------|
| `tables` | `tables` | `[TableName -> TableMetadata]` | Table definitions |
| `indexes` | `indexes` | `[IndexName -> IndexMetadata]` | Index definitions |
| `statistics` | `statistics` | `[TableName -> Statistics]` | Table statistics |
| `schemaVersion` | `schemaVersion` | `Nat` | Schema version number |
| `users` | (future) | `[UserName -> UserMetadata]` | User accounts |
| `roles` | (future) | `[RoleName -> RoleMetadata]` | Role definitions |
| `permissions` | (future) | `[String -> [Permission]]` | Access permissions |

## 5. API Specification

### 5.1 Initialization

```swift
public actor CatalogManager {
    public init(storageManager: StorageManager? = nil)
}
```

**Parameters**:
- `storageManager`: Optional storage manager for Catalog persistence

**Bootstrap**:
- If `storageManager` provided: Loads Catalog from system tables
- If `storageManager` nil: In-memory only (for testing)

**Initialization Sequence**:
1. Initialize in-memory state (empty)
2. If `storageManager` provided:
   - Check if system tables exist
   - If not: Bootstrap system tables
   - If yes: Load Catalog from system tables
3. Mark as bootstrapped

### 5.2 Table Operations

#### 5.2.1 Create Table

```swift
public func createTable(
    name: String,
    columns: [ColumnMetadata],
    primaryKey: Set<String> = [],
    foreignKeys: [ForeignKeyMetadata] = [],
    constraints: [ConstraintMetadata] = []
) async throws
```

**TLA+ Action**: `CreateTable(tableName, columns, primaryKey)`

**Behavior**: Detailed step-by-step execution

1. **Validate Table Name**:
   ```swift
   guard !name.isEmpty else {
       throw CatalogError.invalidTableName("Table name cannot be empty")
   }
   guard !name.hasPrefix("colibri_") else {
       throw CatalogError.invalidTableName("Cannot create table with colibri_ prefix")
   }
   ```
   - Table name must be non-empty
   - Cannot use system table prefix

2. **Check Table Doesn't Exist**:
   ```swift
   guard tables[name] == nil else {
       throw CatalogError.tableAlreadyExists(name)
   }
   ```
   - Table must not already exist
   - Catalog is single source of truth

3. **Validate Primary Key Columns**:
   ```swift
   for pkColumn in primaryKey {
       guard columns.contains(where: { $0.name == pkColumn }) else {
           throw CatalogError.invalidColumn("Primary key column \(pkColumn) not found")
       }
   }
   ```
   - Primary key columns must exist in column list
   - Validates metadata consistency

4. **Validate Foreign Key Columns**:
   ```swift
   for fk in foreignKeys {
       for fkColumn in fk.from {
           guard columns.contains(where: { $0.name == fkColumn }) else {
               throw CatalogError.invalidColumn("Foreign key column \(fkColumn) not found")
           }
       }
       // Validate referenced table exists
       guard tables[fk.to.table] != nil else {
           throw CatalogError.tableNotFound(fk.to.table)
       }
   }
   ```
   - Foreign key columns must exist
   - Referenced table must exist
   - Validates referential integrity

5. **Create Table Metadata**:
   ```swift
   let tableMetadata = TableMetadata(
       name: name,
       columns: columns,
       primaryKey: primaryKey,
       foreignKeys: foreignKeys,
       constraints: constraints
   )
   ```
   - **Table Metadata**: Complete table definition
   - **Immutable**: Value type for thread safety
   - **Complete**: All metadata in one structure

6. **Store in Memory**:
   ```swift
   tables[name] = tableMetadata
   ```
   - **In-Memory Cache**: Fast access
   - **O(1) Lookup**: Hash table lookup
   - **Immediate**: Available immediately

7. **Persist to System Table** (if storage available):
   ```swift
   if let storage = storageManager {
       try await persistTableMetadata(name: name, metadata: tableMetadata)
   }
   ```
   - **Persistence**: Write to `colibri_tables` system table
   - **Durability**: Catalog survives crashes
   - **Atomic**: Part of transaction

8. **Log to WAL** (if available):
   ```swift
   if let wal = walManager {
       try await wal.append(kind: .ddl, txID: txId, ...)
   }
   ```
   - **Durability**: WAL ensures durability
   - **Recovery**: Catalog reconstructed from WAL

9. **Increment Schema Version**:
   ```swift
   schemaVersion += 1
   ```
   - **Versioning**: Track schema changes
   - **Monotonic**: Always increasing
   - **Tracking**: Used for schema evolution

10. **Notify Components** (if needed):
    ```swift
    // Components subscribe to Catalog changes
    notifyCatalogChange(.tableCreated(name: name))
    ```
    - **Change Notification**: Components can react to changes
    - **Cache Invalidation**: Components can invalidate caches
    - **Reinitialization**: Components can reinitialize if needed

**Preconditions**:
- Table name is valid (non-empty, not system table)
- Table doesn't exist (`tables[name] == nil`)
- Columns are valid (non-empty, unique names)
- Primary key columns exist in columns
- Foreign key tables exist (if any)

**Postconditions**:
- Table created (`tables[name] != nil`)
- Table persisted (if storage available)
- Schema version incremented (`schemaVersion = oldVersion + 1`)
- Catalog consistent (all invariants hold)

**Performance Characteristics**:
- **Create**: ~100ns-1ms (depends on persistence)
  - Validation: ~100ns
  - Memory store: ~100ns
  - Persistence: ~1ms (if storage available)
- **Scalable**: O(1) operation

**Catalog Dependency**:

**Storage Manager** uses Catalog:
```swift
// Storage Manager MUST check Catalog before operations
let tableMetadata = try await catalog.getTable(name: tableName)
guard tableMetadata != nil else {
    throw StorageError.tableNotFound
}
// Use tableMetadata.columns for validation
```

**Index Manager** uses Catalog:
```swift
// Index Manager MUST check Catalog before index operations
let indexMetadata = try await catalog.getIndex(name: indexName)
guard indexMetadata != nil else {
    throw IndexError.indexNotFound
}
// Use indexMetadata.columns for index creation
```

**Query Optimizer** uses Catalog:
```swift
// Query Optimizer MUST use Catalog for optimization
let tableMetadata = try await catalog.getTable(name: tableName)
let statistics = try await catalog.getStatistics(tableName: tableName)
// Use metadata and statistics for cost estimation
```

**Example Usage**:
```swift
// Create table with Catalog
try await catalog.createTable(
    name: "users",
    columns: [
        ColumnMetadata(name: "id", type: .int, nullable: false),
        ColumnMetadata(name: "email", type: .string, nullable: false),
        ColumnMetadata(name: "name", type: .string, nullable: true)
    ],
    primaryKey: ["id"],
    constraints: [
        ConstraintMetadata(type: .unique, columns: ["email"])
    ]
)

// Now Storage Manager can create heap table
// Now Index Manager can create indexes
// Now Query Optimizer can optimize queries
```

**Edge Cases**:

1. **Duplicate Table Name**:
   - **Behavior**: Throws `CatalogError.tableAlreadyExists`
   - **Prevention**: Check table existence before create

2. **Invalid Column**:
   - **Behavior**: Throws `CatalogError.invalidColumn`
   - **Validation**: Column validation before create

3. **Storage Unavailable**:
   - **Behavior**: Table created in memory only (not persistent)
   - **Warning**: Data lost on restart
   - **Use Case**: Testing scenarios

4. **Concurrent Create**:
   - **Behavior**: Actor isolation serializes operations
   - **Safety**: No race conditions

#### 5.2.2 Drop Table

```swift
public func dropTable(name: String) async throws
```

**TLA+ Action**: `DropTable(tableName)`

**Behavior**: Detailed step-by-step execution

1. **Validate Table Exists**:
   ```swift
   guard tables[name] != nil else {
       throw CatalogError.tableNotFound(name)
   }
   ```
   - Table must exist
   - Cannot drop non-existent table

2. **Check Dependencies**:
   ```swift
   // Check for dependent indexes
   let dependentIndexes = indexes.values.filter { $0.tableName == name }
   if !dependentIndexes.isEmpty {
       throw CatalogError.tableHasDependencies(name)
   }
   
   // Check for foreign key references
   let referencingTables = tables.values.filter { table in
       table.foreignKeys.contains { $0.to.table == name }
   }
   if !referencingTables.isEmpty {
       throw CatalogError.tableHasDependencies(name)
   }
   ```
   - **Dependency Check**: Cannot drop table with dependencies
   - **Indexes**: Must drop indexes first
   - **Foreign Keys**: Must drop foreign keys first

3. **Remove from Memory**:
   ```swift
   tables.removeValue(forKey: name)
   statistics.removeValue(forKey: name)
   ```
   - **Cleanup**: Remove table and statistics
   - **Memory**: Free memory used by table

4. **Persist to System Table** (if storage available):
   ```swift
   if let storage = storageManager {
       try await deleteTableMetadata(name: name)
   }
   ```
   - **Persistence**: Delete from `colibri_tables` system table
   - **Atomic**: Part of transaction

5. **Log to WAL** (if available):
   ```swift
   if let wal = walManager {
       try await wal.append(kind: .ddl, txID: txId, ...)
   }
   ```
   - **Durability**: WAL ensures durability
   - **Recovery**: Catalog reconstructed from WAL

6. **Increment Schema Version**:
   ```swift
   schemaVersion += 1
   ```
   - **Versioning**: Track schema changes
   - **Monotonic**: Always increasing

7. **Notify Components**:
   ```swift
   notifyCatalogChange(.tableDropped(name: name))
   ```
   - **Change Notification**: Components can react to changes
   - **Cleanup**: Components can clean up resources

**Preconditions**:
- Table exists (`tables[name] != nil`)
- No dependent indexes (indexes referencing table)
- No foreign key references (other tables referencing this table)

**Postconditions**:
- Table dropped (`tables[name] == nil`)
- Table removed from persistence (if storage available)
- Schema version incremented (`schemaVersion = oldVersion + 1`)
- Catalog consistent (all invariants hold)

**Performance Characteristics**:
- **Drop**: ~100ns-1ms (depends on persistence)
  - Validation: ~100ns
  - Memory remove: ~100ns
  - Persistence: ~1ms (if storage available)
- **Scalable**: O(1) operation

#### 5.2.3 Get Table

```swift
public func getTable(name: String) async -> TableMetadata?
```

**TLA+ Action**: `GetTable(tableName)`

**Behavior**: Detailed step-by-step execution

1. **Check Memory Cache**:
   ```swift
   if let table = tables[name] {
       return table  // Cache hit
   }
   ```
   - **Cache Hit**: Fast path (~10ns)
   - **O(1) Lookup**: Hash table lookup

2. **Load from System Table** (if storage available):
   ```swift
   if let storage = storageManager {
       if let tableMetadata = try await loadTableMetadata(name: name) {
           // Cache in memory
           tables[name] = tableMetadata
           return tableMetadata
       }
   }
   ```
   - **Cache Miss**: Load from persistence
   - **Persistence**: Read from `colibri_tables` system table
   - **Cache**: Store in memory for future access

3. **Return nil** (table doesn't exist):
   ```swift
   return nil
   ```

**Preconditions**:
- None (safe to query non-existent table)

**Postconditions**:
- Table metadata returned (if exists)
- Table cached in memory (if loaded from persistence)

**Returns**: `TableMetadata?` (nil if table doesn't exist)

**Performance Characteristics**:
- **Cache Hit**: ~10ns (dictionary lookup)
- **Cache Miss**: ~1ms (load from system table)
- **Scalable**: O(1) operation

**Catalog Dependency**:

**Storage Manager** MUST use Catalog:
```swift
// Storage Manager MUST check Catalog before operations
guard let tableMetadata = await catalog.getTable(name: tableName) else {
    throw StorageError.tableNotFound
}
// Validate operations against tableMetadata
```

**Query Executor** MUST use Catalog:
```swift
// Query Executor MUST check Catalog before executing queries
guard let tableMetadata = await catalog.getTable(name: tableName) else {
    throw QueryError.tableNotFound
}
// Use tableMetadata.columns for type checking
```

### 5.3 Index Operations

#### 5.3.1 Create Index

```swift
public func createIndex(
    name: String,
    tableName: String,
    columns: [String],
    indexType: IndexType = .btree,
    unique: Bool = false
) async throws
```

**TLA+ Action**: `CreateIndex(indexName, tableName, columns, indexType, unique)`

**Behavior**: Detailed step-by-step execution

1. **Validate Index Name**:
   ```swift
   guard !name.isEmpty else {
       throw CatalogError.invalidIndexName("Index name cannot be empty")
   }
   ```
   - Index name must be non-empty

2. **Check Index Doesn't Exist**:
   ```swift
   guard indexes[name] == nil else {
       throw CatalogError.indexAlreadyExists(name)
   }
   ```
   - Index must not already exist

3. **Validate Table Exists**:
   ```swift
   guard let tableMetadata = tables[tableName] else {
       throw CatalogError.tableNotFound(tableName)
   }
   ```
   - **Catalog Dependency**: Index creation depends on Catalog
   - Table must exist before creating index

4. **Validate Index Columns**:
   ```swift
   for column in columns {
       guard tableMetadata.columns.contains(where: { $0.name == column }) else {
           throw CatalogError.invalidColumn("Index column \(column) not found in table")
       }
   }
   ```
   - **Catalog Dependency**: Column validation uses Catalog
   - Index columns must exist in table

5. **Create Index Metadata**:
   ```swift
   let indexMetadata = IndexMetadata(
       name: name,
       tableName: tableName,
       columns: columns,
       indexType: indexType,
       unique: unique
   )
   ```
   - **Index Metadata**: Complete index definition
   - **Immutable**: Value type for thread safety

6. **Store in Memory**:
   ```swift
   indexes[name] = indexMetadata
   ```
   - **In-Memory Cache**: Fast access
   - **O(1) Lookup**: Hash table lookup

7. **Persist to System Table** (if storage available):
   ```swift
   if let storage = storageManager {
       try await persistIndexMetadata(name: name, metadata: indexMetadata)
   }
   ```
   - **Persistence**: Write to `colibri_indexes` system table
   - **Durability**: Catalog survives crashes

8. **Log to WAL** (if available):
   ```swift
   if let wal = walManager {
       try await wal.append(kind: .ddl, txID: txId, ...)
   }
   ```
   - **Durability**: WAL ensures durability

9. **Increment Schema Version**:
   ```swift
   schemaVersion += 1
   ```

10. **Notify Components**:
    ```swift
    notifyCatalogChange(.indexCreated(name: name, tableName: tableName))
    ```

**Preconditions**:
- Index name is valid (non-empty)
- Index doesn't exist (`indexes[name] == nil`)
- Table exists (`tables[tableName] != nil`)
- Index columns exist in table

**Postconditions**:
- Index created (`indexes[name] != nil`)
- Index persisted (if storage available)
- Schema version incremented

**Catalog Dependency**:

**Index Manager** MUST use Catalog:
```swift
// Index Manager MUST check Catalog before index operations
guard let indexMetadata = await catalog.getIndex(name: indexName) else {
    throw IndexError.indexNotFound
}
// Use indexMetadata for index structure creation
```

**Query Optimizer** MUST use Catalog:
```swift
// Query Optimizer MUST use Catalog for index selection
let indexes = await catalog.getIndexes(for: tableName)
// Use indexes for query plan generation
```

#### 5.3.2 Get Index

```swift
public func getIndex(name: String) async -> IndexMetadata?
public func getIndexes(for tableName: String) async -> [IndexMetadata]
```

**TLA+ Action**: `GetIndex(indexName)`, `GetIndexes(tableName)`

**Behavior**: Similar to `getTable()` but for indexes

**Catalog Dependency**: Components MUST use Catalog for index metadata

### 5.4 Statistics Operations

#### 5.4.1 Update Statistics

```swift
public func updateStatistics(tableName: String, stats: Statistics) async throws
```

**TLA+ Action**: `UpdateStatistics(tableName, stats)`

**Behavior**: Detailed step-by-step execution

1. **Validate Table Exists**:
   ```swift
   guard tables[tableName] != nil else {
       throw CatalogError.tableNotFound(tableName)
   }
   ```
   - **Catalog Dependency**: Statistics update depends on Catalog
   - Table must exist

2. **Store in Memory**:
   ```swift
   statistics[tableName] = stats
   ```
   - **In-Memory Cache**: Fast access

3. **Persist to System Table** (if storage available):
   ```swift
   if let storage = storageManager {
       try await persistStatistics(tableName: tableName, stats: stats)
   }
   ```
   - **Persistence**: Write to `colibri_statistics` system table

**Preconditions**:
- Table exists (`tables[tableName] != nil`)

**Postconditions**:
- Statistics updated (`statistics[tableName] = stats`)

**Catalog Dependency**:

**Statistics Manager** MUST use Catalog:
```swift
// Statistics Manager MUST update Catalog
try await catalog.updateStatistics(tableName: tableName, stats: stats)
```

**Query Optimizer** MUST use Catalog:
```swift
// Query Optimizer MUST use Catalog statistics
let stats = await catalog.getStatistics(tableName: tableName)
// Use stats for cost estimation
```

### 5.5 User Management Operations (Future)

#### 5.5.1 Create User

```swift
public func createUser(
    username: String,
    passwordHash: String
) async throws
```

**Catalog Dependency**: Authentication Manager MUST use Catalog for user metadata

#### 5.5.2 Create Role

```swift
public func createRole(name: String, description: String? = nil) async throws
```

**Catalog Dependency**: Authorization Manager MUST use Catalog for role metadata

#### 5.5.3 Grant Permission

```swift
public func grantPermission(
    grantee: String,
    granteeType: GranteeType,  // .user or .role
    tableName: String,
    permission: PermissionType  // .select, .insert, .update, .delete
) async throws
```

**Catalog Dependency**: Authorization Manager MUST use Catalog for permission checks

### 5.6 Query Operations

#### 5.6.1 Table Exists

```swift
public func tableExists(_ name: String) async -> Bool
```

**Usage**: Components check table existence before operations

#### 5.6.2 Index Exists

```swift
public func indexExists(_ name: String) async -> Bool
```

**Usage**: Components check index existence before operations

#### 5.6.3 Get Schema Version

```swift
public func getSchemaVersion() -> Int
```

**Usage**: Components check schema version for compatibility

## 6. Component Dependencies

### 6.1 Storage Manager Dependency

**Storage Manager MUST**:
- Check Catalog before table operations
- Use Catalog for table metadata
- Validate operations against Catalog

**Example**:
```swift
// Storage Manager MUST check Catalog
guard let tableMetadata = await catalog.getTable(name: tableName) else {
    throw StorageError.tableNotFound
}

// Use tableMetadata.columns for validation
let columns = tableMetadata.columns
// Validate row data against columns
```

### 6.2 Index Manager Dependency

**Index Manager MUST**:
- Check Catalog before index operations
- Use Catalog for index metadata
- Create indexes only for tables in Catalog

**Example**:
```swift
// Index Manager MUST check Catalog
guard let indexMetadata = await catalog.getIndex(name: indexName) else {
    throw IndexError.indexNotFound
}

// Use indexMetadata.columns for index creation
let columns = indexMetadata.columns
// Create index structure based on metadata
```

### 6.3 Query Optimizer Dependency

**Query Optimizer MUST**:
- Use Catalog for table metadata
- Use Catalog for index metadata
- Use Catalog for statistics
- Check Catalog before optimization

**Example**:
```swift
// Query Optimizer MUST use Catalog
let tableMetadata = await catalog.getTable(name: tableName)
let indexes = await catalog.getIndexes(for: tableName)
let statistics = await catalog.getStatistics(tableName: tableName)

// Use metadata and statistics for optimization
let cost = estimateCost(table: tableMetadata, indexes: indexes, stats: statistics)
```

### 6.4 Query Executor Dependency

**Query Executor MUST**:
- Check Catalog before execution
- Use Catalog for type checking
- Validate queries against Catalog

**Example**:
```swift
// Query Executor MUST check Catalog
guard let tableMetadata = await catalog.getTable(name: tableName) else {
    throw QueryError.tableNotFound
}

// Use tableMetadata.columns for type checking
for column in selectedColumns {
    guard tableMetadata.columns.contains(where: { $0.name == column }) else {
        throw QueryError.columnNotFound(column)
    }
}
```

### 6.5 Transaction Manager Dependency

**Transaction Manager MUST**:
- Validate operations against Catalog
- Check permissions from Catalog
- Use Catalog for constraint validation

**Example**:
```swift
// Transaction Manager MUST validate against Catalog
guard let tableMetadata = await catalog.getTable(name: tableName) else {
    throw TransactionError.tableNotFound
}

// Check foreign key constraints from Catalog
for fk in tableMetadata.foreignKeys {
    // Validate foreign key constraint
}
```

### 6.6 Authentication Manager Dependency

**Authentication Manager MUST**:
- Use Catalog for user metadata
- Use Catalog for role metadata
- Use Catalog for permission checks

**Example**:
```swift
// Authentication Manager MUST use Catalog
guard let userMetadata = await catalog.getUser(username: username) else {
    throw AuthenticationError.userNotFound
}

// Check permissions from Catalog
let hasPermission = await catalog.hasPermission(
    username: username,
    tableName: tableName,
    permission: .select
)
```

## 7. Persistence Implementation

### 7.1 System Tables Storage

**Storage Location**: Special `system` area (separate from user data)

**Storage Format**: JSON serialization of metadata

**Update Strategy**: Write-through (immediate persistence)

### 7.2 Bootstrap on Restart

```swift
private func loadCatalogFromSystemTables() async throws {
    // 1. Load tables
    let tableRows = try await loadFromSystemTable("colibri_tables")
    for row in tableRows {
        let metadata = try JSONDecoder().decode(TableMetadata.self, from: row.metadata_json)
        tables[metadata.name] = metadata
    }
    
    // 2. Load indexes
    let indexRows = try await loadFromSystemTable("colibri_indexes")
    // ... decode and store
    
    // 3. Load statistics
    let statsRows = try await loadFromSystemTable("colibri_statistics")
    // ... decode and store
    
    // 4. Load users, roles, permissions
    // ...
}
```

### 7.3 WAL Integration

**Catalog Changes Logged**: All DDL operations logged to WAL

**Recovery**: Catalog reconstructed from WAL during ARIES recovery

## 8. Invariants (TLA+ Verification)

### 8.1 Primary Key Valid Invariant

```tla
Inv_Catalog_PrimaryKeyValid ==
    \A t \in DOMAIN tables:
        tables[t].primaryKey \subseteq {tables[t].columns[i].name : i \in DOMAIN tables[t].columns}
```

**Swift Implementation**:
```swift
public func checkPrimaryKeyValidInvariant() -> Bool {
    for (_, table) in tables {
        for pkColumn in table.primaryKey {
            guard table.columns.contains(where: { $0.name == pkColumn }) else {
                return false
            }
        }
    }
    return true
}
```

### 8.2 Foreign Key Valid Invariant

```tla
Inv_Catalog_ForeignKeyValid ==
    \A t \in DOMAIN tables:
        \A fk \in tables[t].foreignKeys:
            /\ fk.to.table \in DOMAIN tables
            /\ fk.from \subseteq {tables[t].columns[i].name : i \in DOMAIN tables[t].columns}
```

**Swift Implementation**:
```swift
public func checkForeignKeyValidInvariant() -> Bool {
    for (_, table) in tables {
        for fk in table.foreignKeys {
            // Check referenced table exists
            guard tables[fk.to.table] != nil else {
                return false
            }
            // Check foreign key columns exist
            for fkColumn in fk.from {
                guard table.columns.contains(where: { $0.name == fkColumn }) else {
                    return false
                }
            }
        }
    }
    return true
}
```

### 8.3 Index Valid Invariant

```tla
Inv_Catalog_IndexValid ==
    \A idx \in DOMAIN indexes:
        /\ indexes[idx].tableName \in DOMAIN tables
        /\ indexes[idx].columns \subseteq {tables[indexes[idx].tableName].columns[i].name : i \in DOMAIN tables[indexes[idx].tableName].columns}
```

**Swift Implementation**:
```swift
public func checkIndexValidInvariant() -> Bool {
    for (_, index) in indexes {
        // Check referenced table exists
        guard let table = tables[index.tableName] else {
            return false
        }
        // Check index columns exist
        for indexColumn in index.columns {
            guard table.columns.contains(where: { $0.name == indexColumn }) else {
                return false
            }
        }
    }
    return true
}
```

### 8.4 Statistics Valid Invariant

```tla
Inv_Catalog_StatisticsValid ==
    \A t \in DOMAIN statistics:
        t \in DOMAIN tables /\ statistics[t].rowCount >= 0
```

**Swift Implementation**:
```swift
public func checkStatisticsValidInvariant() -> Bool {
    for (tableName, _) in statistics {
        guard tables[tableName] != nil else {
            return false
        }
    }
    return true
}
```

### 8.5 Consistency Invariant

```tla
Inv_Catalog_Consistency ==
    /\ Inv_Catalog_PrimaryKeyValid
    /\ Inv_Catalog_ForeignKeyValid
    /\ Inv_Catalog_IndexValid
    /\ Inv_Catalog_StatisticsValid
```

**Swift Implementation**:
```swift
public func checkConsistencyInvariant() -> Bool {
    let pkValid = checkPrimaryKeyValidInvariant()
    let fkValid = checkForeignKeyValidInvariant()
    let idxValid = checkIndexValidInvariant()
    let statsValid = checkStatisticsValidInvariant()
    
    return pkValid && fkValid && idxValid && statsValid
}
```

## 9. Performance Characteristics

### 9.1 Lookup Operations

**Operation**: `getTable()`, `getIndex()`

**Complexity**: O(1)

**Latency**: 
- Cache hit: ~10ns
- Cache miss: ~1ms (load from system table)

### 9.2 Create Operations

**Operation**: `createTable()`, `createIndex()`

**Complexity**: O(1)

**Latency**: ~100ns-1ms (depends on persistence)

### 9.3 Validation Operations

**Operation**: `tableExists()`, `indexExists()`

**Complexity**: O(1)

**Latency**: ~10ns (dictionary lookup)

## 10. Error Handling

### 10.1 Error Types

```swift
public enum CatalogError: Error {
    case tableNotFound(String)
    case tableAlreadyExists(String)
    case indexNotFound(String)
    case indexAlreadyExists(String)
    case invalidTableName(String)
    case invalidIndexName(String)
    case invalidColumn(String)
    case tableHasDependencies(String)
    case bootstrapFailed(String)
    case persistenceFailed(String)
}
```

### 10.2 Error Recovery

- **Table Not Found**: Return error, caller handles
- **Bootstrap Failed**: Retry bootstrap or fail initialization
- **Persistence Failed**: Log warning, continue in-memory only

## 11. Testing

### 11.1 Unit Tests

- Table create/drop operations
- Index create/drop operations
- Statistics update operations
- Invariant verification
- Bootstrap process

### 11.2 Integration Tests

- Catalog + Storage Manager persistence
- Catalog + Index Manager integration
- Catalog + Query Optimizer integration
- Catalog + Transaction Manager validation
- Catalog recovery from system tables

### 11.3 Performance Tests

- Lookup latency (cache hit/miss)
- Create/drop throughput
- Memory usage
- Bootstrap time

## 12. Apple-First Optimizations

### 12.1 Swift Actors

- **Actor Isolation**: Thread-safe Catalog operations
- **No Locks**: Eliminates lock contention
- **Composable**: Easy to compose with other actors

### 12.2 Value Types

- **Immutable Metadata**: Metadata structs are immutable
- **Copy-on-Write**: Efficient memory usage
- **Thread Safety**: Immutable values are thread-safe

### 12.3 Async/Await

- **Non-Blocking**: Catalog operations don't block threads
- **Concurrent**: Supports thousands of concurrent lookups
- **Structured**: Clear error handling and control flow

## 13. References

- **RFC 0006**: Storage Manager
- **RFC 0010**: Index Manager
- **RFC 0025**: Query Optimizer
- **TLA+ Spec**: `spec/Catalog.tla`

---

**Next**: See RFC 0035 for Authentication Manager details.
