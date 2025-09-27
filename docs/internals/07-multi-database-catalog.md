# Multi-Database Catalog System Internals

## Overview

ColibrìDB implements a comprehensive multi-database catalog system that serves as the single source of truth for all database metadata, object definitions, and configurations. This chapter provides a detailed analysis of the catalog architecture, data structures, and management operations.

## Catalog Architecture

### Class Structure

```swift
/// Multidatabase catalog system that serves as the single source of truth
/// for all database objects, metadata, and configurations.
public class MultiDatabaseCatalog {
    private let logger = Logger(subsystem: "com.colibridb.catalog", category: "multidb")
    private let database: Database
    private let catalogManager: CatalogManager
    
    // System database name
    private static let SYSTEM_DATABASE = "ColibRegister"
    
    public init(database: Database) {
        self.database = database
        self.catalogManager = CatalogManager(database: database)
    }
}
```

**Detailed Analysis:**

#### Core Components
- **`logger: Logger`**: Structured logging for catalog operations
- **`database: Database`**: Reference to the main database instance
- **`catalogManager: CatalogManager`**: Manages catalog operations
- **`SYSTEM_DATABASE`**: Name of the system database

#### Logging Configuration
- **Subsystem**: "com.colibridb.catalog" for log filtering
- **Category**: "multidb" for specific component logging
- **Purpose**: Track catalog operations and errors
- **Performance**: Efficient structured logging

#### Initialization
- **Database Reference**: Store reference to main database
- **Catalog Manager**: Create catalog manager instance
- **Dependency Injection**: Database is injected for flexibility

### Database Management

#### Create Database

```swift
/// Creates a new database in the catalog
public func createDatabase(_ name: String, owner: String? = nil) throws {
    logger.info("Creating database: \(name)")
    
    // Check if database already exists
    if try databaseExists(name) {
        throw CatalogError.databaseAlreadyExists(name)
    }
    
    // Create database entry in catalog
    let dbId = UUID()
    let dbEntry = DatabaseEntry(
        id: dbId,
        name: name,
        owner: owner ?? "system",
        created: Date(),
        lastModified: Date(),
        status: .active,
        defaultTablespace: "default",
        characterSet: "utf8",
        collation: "utf8_general_ci"
    )
    
    try catalogManager.insertDatabase(dbEntry)
    
    // Create default tablespace
    try createTablespace("default", for: name)
    
    logger.info("Database created successfully: \(name)")
}
```

**Detailed Analysis:**

#### Process Flow
1. **Logging**: Log database creation start
2. **Existence Check**: Verify database doesn't exist
3. **ID Generation**: Generate unique UUID for database
4. **Entry Creation**: Create DatabaseEntry with metadata
5. **Catalog Insertion**: Insert entry into catalog
6. **Tablespace Creation**: Create default tablespace
7. **Logging**: Log successful creation

#### Database Entry Structure
```swift
struct DatabaseEntry {
    let id: UUID
    let name: String
    let owner: String
    let created: Date
    let lastModified: Date
    let status: DatabaseStatus
    let defaultTablespace: String
    let characterSet: String
    let collation: String
}
```

**Field Analysis:**
- **`id: UUID`**: Unique identifier for database
- **`name: String`**: Human-readable database name
- **`owner: String`**: Database owner (default: "system")
- **`created: Date`**: Creation timestamp
- **`lastModified: Date`**: Last modification timestamp
- **`status: DatabaseStatus`**: Current status (.active, .inactive, .archived)
- **`defaultTablespace: String`**: Default tablespace name
- **`characterSet: String`**: Character encoding (utf8)
- **`collation: String`**: Collation rules (utf8_general_ci)

#### Error Handling
- **Existence Check**: Throw error if database exists
- **Catalog Operations**: Propagate errors from catalog manager
- **Tablespace Creation**: Handle tablespace creation errors

#### Performance
- **Existence Check**: O(1) database lookup
- **Entry Creation**: O(1) object creation
- **Catalog Insertion**: O(1) catalog operation
- **Tablespace Creation**: O(1) tablespace operation
- **Total Time**: O(1) operation

#### Drop Database

```swift
/// Drops a database from the catalog
public func dropDatabase(_ name: String, cascade: Bool = false) throws {
    logger.info("Dropping database: \(name)")
    
    guard try databaseExists(name) else {
        throw CatalogError.databaseNotFound(name)
    }
    
    // Get all objects in the database
    let tables = try catalogManager.getTables(in: name)
    let indexes = try catalogManager.getIndexes(in: name)
    let views = try catalogManager.getViews(in: name)
    let sequences = try catalogManager.getSequences(in: name)
    
    if !cascade && (!tables.isEmpty || !indexes.isEmpty || !views.isEmpty || !sequences.isEmpty) {
        throw CatalogError.databaseNotEmpty(name)
    }
    
    // Drop all objects if cascade is true
    if cascade {
        for table in tables {
            try dropTable(table.name, in: name)
        }
        for view in views {
            try dropView(view.name, in: name)
        }
        for sequence in sequences {
            try dropSequence(sequence.name, in: name)
        }
    }
    
    // Remove database entry
    try catalogManager.deleteDatabase(name)
    
    logger.info("Database dropped successfully: \(name)")
}
```

**Detailed Analysis:**

#### Process Flow
1. **Logging**: Log database drop start
2. **Existence Check**: Verify database exists
3. **Object Enumeration**: Get all objects in database
4. **Cascade Check**: Check if cascade is required
5. **Object Cleanup**: Drop all objects if cascade
6. **Database Removal**: Remove database entry
7. **Logging**: Log successful drop

#### Object Enumeration
- **Tables**: Get all tables in database
- **Indexes**: Get all indexes in database
- **Views**: Get all views in database
- **Sequences**: Get all sequences in database

#### Cascade Logic
- **No Cascade**: Throw error if objects exist
- **Cascade**: Drop all objects before dropping database
- **Order**: Drop objects in dependency order

#### Error Handling
- **Not Found**: Throw error if database doesn't exist
- **NotEmpty**: Throw error if objects exist without cascade
- **Object Drop**: Handle errors from object dropping

#### Performance
- **Existence Check**: O(1) database lookup
- **Object Enumeration**: O(n) where n is number of objects
- **Object Cleanup**: O(n) where n is number of objects
- **Database Removal**: O(1) catalog operation
- **Total Time**: O(n) where n is number of objects

### Table Management

#### Create Table

```swift
/// Creates a new table in the specified database
public func createTable(_ name: String, in database: String, schema: CatalogTableSchema) throws {
    logger.info("Creating table: \(name) in database: \(database)")
    
    // Verify database exists
    guard try databaseExists(database) else {
        throw CatalogError.databaseNotFound(database)
    }
    
    // Check if table already exists
    if try tableExists(name, in: database) {
        throw CatalogError.tableAlreadyExists(name)
    }
    
    // Create table entry
    let tableId = UUID()
    let tableEntry = TableEntry(
        id: tableId,
        name: name,
        database: database,
        schema: schema,
        created: Date(),
        lastModified: Date(),
        status: .active,
        rowCount: 0,
        sizeBytes: 0
    )
    
    try catalogManager.insertTable(tableEntry)
    
    // Create table in database
    try database.createTable(name, in: database, schema: schema)
    
    logger.info("Table created successfully: \(name)")
}
```

**Detailed Analysis:**

#### Process Flow
1. **Logging**: Log table creation start
2. **Database Check**: Verify database exists
3. **Existence Check**: Verify table doesn't exist
4. **Entry Creation**: Create TableEntry with metadata
5. **Catalog Insertion**: Insert entry into catalog
6. **Database Creation**: Create table in database
7. **Logging**: Log successful creation

#### Table Entry Structure
```swift
struct TableEntry {
    let id: UUID
    let name: String
    let database: String
    let schema: CatalogTableSchema
    let created: Date
    let lastModified: Date
    let status: TableStatus
    let rowCount: Int
    let sizeBytes: Int
}
```

**Field Analysis:**
- **`id: UUID`**: Unique identifier for table
- **`name: String`**: Table name
- **`database: String`**: Parent database name
- **`schema: CatalogTableSchema`**: Table schema definition
- **`created: Date`**: Creation timestamp
- **`lastModified: Date`**: Last modification timestamp
- **`status: TableStatus`**: Current status (.active, .inactive, .archived)
- **`rowCount: Int`**: Number of rows in table
- **`sizeBytes: Int`**: Size of table in bytes

#### Error Handling
- **Database Not Found**: Throw error if database doesn't exist
- **Table Exists**: Throw error if table already exists
- **Catalog Operations**: Propagate errors from catalog manager
- **Database Operations**: Handle database creation errors

#### Performance
- **Database Check**: O(1) database lookup
- **Existence Check**: O(1) table lookup
- **Entry Creation**: O(1) object creation
- **Catalog Insertion**: O(1) catalog operation
- **Database Creation**: O(1) database operation
- **Total Time**: O(1) operation

#### Drop Table

```swift
/// Drops a table from the specified database
public func dropTable(_ name: String, in database: String) throws {
    logger.info("Dropping table: \(name) from database: \(database)")
    
    // Verify database exists
    guard try databaseExists(database) else {
        throw CatalogError.databaseNotFound(database)
    }
    
    // Check if table exists
    guard try tableExists(name, in: database) else {
        throw CatalogError.tableNotFound(name)
    }
    
    // Get all indexes on the table
    let indexes = try catalogManager.getIndexes(on: name, in: database)
    
    // Drop all indexes
    for index in indexes {
        try dropIndex(index.name, in: database)
    }
    
    // Remove table from database
    try database.dropTable(name, in: database)
    
    // Remove table entry from catalog
    try catalogManager.deleteTable(name, from: database)
    
    logger.info("Table dropped successfully: \(name)")
}
```

**Detailed Analysis:**

#### Process Flow
1. **Logging**: Log table drop start
2. **Database Check**: Verify database exists
3. **Existence Check**: Verify table exists
4. **Index Enumeration**: Get all indexes on table
5. **Index Cleanup**: Drop all indexes
6. **Database Removal**: Remove table from database
7. **Catalog Cleanup**: Remove table entry from catalog
8. **Logging**: Log successful drop

#### Index Cleanup
- **Index Enumeration**: Get all indexes on table
- **Index Dropping**: Drop each index
- **Dependency Order**: Drop indexes before table

#### Error Handling
- **Database Not Found**: Throw error if database doesn't exist
- **Table Not Found**: Throw error if table doesn't exist
- **Index Operations**: Handle errors from index dropping
- **Database Operations**: Handle database drop errors

#### Performance
- **Database Check**: O(1) database lookup
- **Existence Check**: O(1) table lookup
- **Index Enumeration**: O(n) where n is number of indexes
- **Index Cleanup**: O(n) where n is number of indexes
- **Database Removal**: O(1) database operation
- **Catalog Cleanup**: O(1) catalog operation
- **Total Time**: O(n) where n is number of indexes

### Index Management

#### Create Index

```swift
/// Creates a new index on the specified table
public func createIndex(_ name: String, on table: String, in database: String, columns: [String], type: IndexType = .bTree) throws {
    logger.info("Creating index: \(name) on table: \(table) in database: \(database)")
    
    // Verify database exists
    guard try databaseExists(database) else {
        throw CatalogError.databaseNotFound(database)
    }
    
    // Verify table exists
    guard try tableExists(table, in: database) else {
        throw CatalogError.tableNotFound(table)
    }
    
    // Check if index already exists
    if try indexExists(name, in: database) {
        throw CatalogError.indexAlreadyExists(name)
    }
    
    // Create index entry
    let indexId = UUID()
    let indexEntry = IndexEntry(
        id: indexId,
        name: name,
        table: table,
        database: database,
        columns: columns,
        type: type,
        created: Date(),
        lastModified: Date(),
        status: .active,
        sizeBytes: 0,
        entryCount: 0
    )
    
    try catalogManager.insertIndex(indexEntry)
    
    // Create index in database
    try database.createIndex(name, on: table, in: database, columns: columns, type: type)
    
    logger.info("Index created successfully: \(name)")
}
```

**Detailed Analysis:**

#### Process Flow
1. **Logging**: Log index creation start
2. **Database Check**: Verify database exists
3. **Table Check**: Verify table exists
4. **Existence Check**: Verify index doesn't exist
5. **Entry Creation**: Create IndexEntry with metadata
6. **Catalog Insertion**: Insert entry into catalog
7. **Database Creation**: Create index in database
8. **Logging**: Log successful creation

#### Index Entry Structure
```swift
struct IndexEntry {
    let id: UUID
    let name: String
    let table: String
    let database: String
    let columns: [String]
    let type: IndexType
    let created: Date
    let lastModified: Date
    let status: IndexStatus
    let sizeBytes: Int
    let entryCount: Int
}
```

**Field Analysis:**
- **`id: UUID`**: Unique identifier for index
- **`name: String`**: Index name
- **`table: String`**: Parent table name
- **`database: String`**: Parent database name
- **`columns: [String]`**: Indexed columns
- **`type: IndexType`**: Index type (.bTree, .hash, .art, .lsm)
- **`created: Date`**: Creation timestamp
- **`lastModified: Date`**: Last modification timestamp
- **`status: IndexStatus`**: Current status (.active, .inactive, .archived)
- **`sizeBytes: Int`**: Size of index in bytes
- **`entryCount: Int`**: Number of entries in index

#### Error Handling
- **Database Not Found**: Throw error if database doesn't exist
- **Table Not Found**: Throw error if table doesn't exist
- **Index Exists**: Throw error if index already exists
- **Catalog Operations**: Propagate errors from catalog manager
- **Database Operations**: Handle database creation errors

#### Performance
- **Database Check**: O(1) database lookup
- **Table Check**: O(1) table lookup
- **Existence Check**: O(1) index lookup
- **Entry Creation**: O(1) object creation
- **Catalog Insertion**: O(1) catalog operation
- **Database Creation**: O(1) database operation
- **Total Time**: O(1) operation

### View Management

#### Create View

```swift
/// Creates a new view in the specified database
public func createView(_ name: String, in database: String, definition: String) throws {
    logger.info("Creating view: \(name) in database: \(database)")
    
    // Verify database exists
    guard try databaseExists(database) else {
        throw CatalogError.databaseNotFound(database)
    }
    
    // Check if view already exists
    if try viewExists(name, in: database) {
        throw CatalogError.viewAlreadyExists(name)
    }
    
    // Create view entry
    let viewId = UUID()
    let viewEntry = ViewEntry(
        id: viewId,
        name: name,
        database: database,
        definition: definition,
        created: Date(),
        lastModified: Date(),
        status: .active
    )
    
    try catalogManager.insertView(viewEntry)
    
    logger.info("View created successfully: \(name)")
}
```

**Detailed Analysis:**

#### Process Flow
1. **Logging**: Log view creation start
2. **Database Check**: Verify database exists
3. **Existence Check**: Verify view doesn't exist
4. **Entry Creation**: Create ViewEntry with metadata
5. **Catalog Insertion**: Insert entry into catalog
6. **Logging**: Log successful creation

#### View Entry Structure
```swift
struct ViewEntry {
    let id: UUID
    let name: String
    let database: String
    let definition: String
    let created: Date
    let lastModified: Date
    let status: ViewStatus
}
```

**Field Analysis:**
- **`id: UUID`**: Unique identifier for view
- **`name: String`**: View name
- **`database: String`**: Parent database name
- **`definition: String`**: SQL definition of view
- **`created: Date`**: Creation timestamp
- **`lastModified: Date`**: Last modification timestamp
- **`status: ViewStatus`**: Current status (.active, .inactive, .archived)

#### Error Handling
- **Database Not Found**: Throw error if database doesn't exist
- **View Exists**: Throw error if view already exists
- **Catalog Operations**: Propagate errors from catalog manager

#### Performance
- **Database Check**: O(1) database lookup
- **Existence Check**: O(1) view lookup
- **Entry Creation**: O(1) object creation
- **Catalog Insertion**: O(1) catalog operation
- **Total Time**: O(1) operation

### Sequence Management

#### Create Sequence

```swift
/// Creates a new sequence in the specified database
public func createSequence(_ name: String, in database: String, start: Int = 1, increment: Int = 1, max: Int? = nil, min: Int? = nil) throws {
    logger.info("Creating sequence: \(name) in database: \(database)")
    
    // Verify database exists
    guard try databaseExists(database) else {
        throw CatalogError.databaseNotFound(database)
    }
    
    // Check if sequence already exists
    if try sequenceExists(name, in: database) {
        throw CatalogError.sequenceAlreadyExists(name)
    }
    
    // Create sequence entry
    let sequenceId = UUID()
    let sequenceEntry = SequenceEntry(
        id: sequenceId,
        name: name,
        database: database,
        start: start,
        increment: increment,
        max: max,
        min: min,
        current: start,
        created: Date(),
        lastModified: Date(),
        status: .active
    )
    
    try catalogManager.insertSequence(sequenceEntry)
    
    logger.info("Sequence created successfully: \(name)")
}
```

**Detailed Analysis:**

#### Process Flow
1. **Logging**: Log sequence creation start
2. **Database Check**: Verify database exists
3. **Existence Check**: Verify sequence doesn't exist
4. **Entry Creation**: Create SequenceEntry with metadata
5. **Catalog Insertion**: Insert entry into catalog
6. **Logging**: Log successful creation

#### Sequence Entry Structure
```swift
struct SequenceEntry {
    let id: UUID
    let name: String
    let database: String
    let start: Int
    let increment: Int
    let max: Int?
    let min: Int?
    let current: Int
    let created: Date
    let lastModified: Date
    let status: SequenceStatus
}
```

**Field Analysis:**
- **`id: UUID`**: Unique identifier for sequence
- **`name: String`**: Sequence name
- **`database: String`**: Parent database name
- **`start: Int`**: Starting value (default: 1)
- **`increment: Int`**: Increment value (default: 1)
- **`max: Int?`**: Maximum value (optional)
- **`min: Int?`**: Minimum value (optional)
- **`current: Int`**: Current value
- **`created: Date`**: Creation timestamp
- **`lastModified: Date`**: Last modification timestamp
- **`status: SequenceStatus`**: Current status (.active, .inactive, .archived)

#### Error Handling
- **Database Not Found**: Throw error if database doesn't exist
- **Sequence Exists**: Throw error if sequence already exists
- **Catalog Operations**: Propagate errors from catalog manager

#### Performance
- **Database Check**: O(1) database lookup
- **Existence Check**: O(1) sequence lookup
- **Entry Creation**: O(1) object creation
- **Catalog Insertion**: O(1) catalog operation
- **Total Time**: O(1) operation

### Statistics Management

#### Update Table Statistics

```swift
/// Updates statistics for a table
public func updateTableStatistics(_ table: String, in database: String) throws {
    logger.info("Updating statistics for table: \(table) in database: \(database)")
    
    // Get table entry
    guard let tableEntry = try catalogManager.getTable(table, in: database) else {
        throw CatalogError.tableNotFound(table)
    }
    
    // Get table statistics from database
    let stats = try database.getTableStatistics(table, in: database)
    
    // Update table entry with new statistics
    let updatedEntry = TableEntry(
        id: tableEntry.id,
        name: tableEntry.name,
        database: tableEntry.database,
        schema: tableEntry.schema,
        created: tableEntry.created,
        lastModified: Date(),
        status: tableEntry.status,
        rowCount: stats.rowCount,
        sizeBytes: stats.sizeBytes
    )
    
    try catalogManager.updateTable(updatedEntry)
    
    logger.info("Table statistics updated successfully: \(table)")
}
```

**Detailed Analysis:**

#### Process Flow
1. **Logging**: Log statistics update start
2. **Table Lookup**: Get table entry from catalog
3. **Statistics Retrieval**: Get statistics from database
4. **Entry Update**: Update table entry with new statistics
5. **Catalog Update**: Update entry in catalog
6. **Logging**: Log successful update

#### Statistics Fields
- **`rowCount: Int`**: Number of rows in table
- **`sizeBytes: Int`**: Size of table in bytes
- **`lastModified: Date`**: Update timestamp

#### Error Handling
- **Table Not Found**: Throw error if table doesn't exist
- **Statistics Retrieval**: Handle errors from database
- **Catalog Operations**: Propagate errors from catalog manager

#### Performance
- **Table Lookup**: O(1) catalog lookup
- **Statistics Retrieval**: O(1) database operation
- **Entry Update**: O(1) object creation
- **Catalog Update**: O(1) catalog operation
- **Total Time**: O(1) operation

### Configuration Management

#### Set Configuration

```swift
/// Sets a configuration value for a database
public func setConfiguration(_ key: String, value: String, for database: String, scope: ConfigurationScope = .database) throws {
    logger.info("Setting configuration: \(key) = \(value) for database: \(database)")
    
    // Verify database exists
    guard try databaseExists(database) else {
        throw CatalogError.databaseNotFound(database)
    }
    
    // Create configuration entry
    let configId = UUID()
    let configEntry = ConfigurationEntry(
        id: configId,
        key: key,
        value: value,
        scope: scope,
        database: database,
        created: Date(),
        lastModified: Date(),
        status: .active
    )
    
    try catalogManager.insertConfiguration(configEntry)
    
    logger.info("Configuration set successfully: \(key)")
}
```

**Detailed Analysis:**

#### Process Flow
1. **Logging**: Log configuration set start
2. **Database Check**: Verify database exists
3. **Entry Creation**: Create ConfigurationEntry with metadata
4. **Catalog Insertion**: Insert entry into catalog
5. **Logging**: Log successful set

#### Configuration Entry Structure
```swift
struct ConfigurationEntry {
    let id: UUID
    let key: String
    let value: String
    let scope: ConfigurationScope
    let database: String
    let created: Date
    let lastModified: Date
    let status: ConfigurationStatus
}
```

**Field Analysis:**
- **`id: UUID`**: Unique identifier for configuration
- **`key: String`**: Configuration key
- **`value: String`**: Configuration value
- **`scope: ConfigurationScope`**: Scope (.global, .database, .table)
- **`database: String`**: Target database name
- **`created: Date`**: Creation timestamp
- **`lastModified: Date`**: Last modification timestamp
- **`status: ConfigurationStatus`**: Current status (.active, .inactive, .archived)

#### Error Handling
- **Database Not Found**: Throw error if database doesn't exist
- **Catalog Operations**: Propagate errors from catalog manager

#### Performance
- **Database Check**: O(1) database lookup
- **Entry Creation**: O(1) object creation
- **Catalog Insertion**: O(1) catalog operation
- **Total Time**: O(1) operation

## Performance Characteristics

### Time Complexity

| Operation | Time Complexity | Space Complexity |
|-----------|----------------|------------------|
| Create Database | O(1) | O(1) |
| Drop Database | O(n) | O(1) |
| Create Table | O(1) | O(1) |
| Drop Table | O(n) | O(1) |
| Create Index | O(1) | O(1) |
| Drop Index | O(1) | O(1) |
| Create View | O(1) | O(1) |
| Drop View | O(1) | O(1) |
| Create Sequence | O(1) | O(1) |
| Drop Sequence | O(1) | O(1) |
| Update Statistics | O(1) | O(1) |
| Set Configuration | O(1) | O(1) |

### Memory Usage

| Component | Memory | Purpose |
|-----------|--------|---------|
| Database Entries | O(d) | Store database metadata |
| Table Entries | O(t) | Store table metadata |
| Index Entries | O(i) | Store index metadata |
| View Entries | O(v) | Store view metadata |
| Sequence Entries | O(s) | Store sequence metadata |
| Configuration Entries | O(c) | Store configuration |

### Concurrency

| Aspect | Performance | Notes |
|--------|-------------|-------|
| Read Concurrency | High | Multiple readers supported |
| Write Concurrency | Medium | Limited by catalog manager |
| Lock Contention | Low | Fine-grained locking |
| Deadlock Prevention | High | Single lock prevents deadlocks |

## Design Decisions

### Why Multi-Database?

- **Isolation**: Separate databases for different applications
- **Security**: Database-level access control
- **Management**: Easier database management
- **Performance**: Isolated performance characteristics

### Why Catalog Manager?

- **Centralization**: Single point for catalog operations
- **Consistency**: Ensures catalog consistency
- **Performance**: Optimized catalog operations
- **Maintainability**: Easier to maintain and extend

### Why UUID Identifiers?

- **Uniqueness**: Globally unique identifiers
- **Distributed**: Works in distributed systems
- **Performance**: Good performance characteristics
- **Compatibility**: Standard identifier format

## Future Optimizations

### Caching

- **Metadata Caching**: Cache frequently accessed metadata
- **Query Caching**: Cache query results
- **Performance**: Reduce catalog access time
- **Memory**: Trade memory for performance

### Parallel Operations

- **Concurrent Reads**: Parallel metadata reads
- **Batch Operations**: Batch catalog operations
- **Performance**: Better utilization of resources
- **Complexity**: More complex implementation

### Compression

- **Metadata Compression**: Compress metadata storage
- **Space**: Reduce storage requirements
- **CPU**: Trade CPU for space
- **Performance**: Faster I/O operations

---

*This analysis provides a comprehensive understanding of ColibrìDB's multi-database catalog system. For specific implementation details, see the corresponding source files.*
