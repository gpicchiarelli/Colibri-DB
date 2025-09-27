# Core Concepts

## Understanding ColibrìDB

ColibrìDB is built around several fundamental concepts that distinguish it from traditional database systems. Understanding these concepts is essential for effective use of the system.

## Multi-Database Architecture

### Database Isolation

Unlike traditional databases that manage a single database, ColibrìDB manages multiple independent databases within a single instance:

```
ColibrìDB Instance
├── Database: "ecommerce"
│   ├── Tables: users, products, orders
│   ├── Indexes: idx_users_email, idx_products_category
│   └── Views: user_summary, sales_report
├── Database: "analytics"
│   ├── Tables: events, metrics, reports
│   └── Indexes: idx_events_timestamp
└── Database: "logs"
    └── Tables: application_logs, error_logs
```

### Benefits of Multi-Database Design

- **Isolation**: Complete separation between different applications
- **Security**: Database-level access control
- **Maintenance**: Independent backup and recovery
- **Performance**: Isolated resource usage
- **Scalability**: Independent scaling strategies

### Database Lifecycle

```sql
-- Create a new database
CREATE DATABASE myapp;

-- Switch to the database
USE myapp;

-- Create tables within the database
CREATE TABLE users (id INT, name STRING);

-- Drop the database (with all its contents)
DROP DATABASE myapp;
```

## Data Types and Values

### Primitive Types

#### Integer Types
```sql
-- 64-bit signed integer
id INT
-- Examples: 1, -42, 9223372036854775807
```

#### Floating-Point Types
```sql
-- 64-bit double precision
price DOUBLE
-- Examples: 3.14, -2.5, 1.0e10
```

#### Boolean Type
```sql
-- True or false value
is_active BOOL
-- Examples: true, false
```

#### String Type
```sql
-- Variable-length string
name STRING
-- Examples: "Hello", "World", "ColibrìDB"
```

### Temporal Types

#### Date Type
```sql
-- Date without time
birth_date DATE
-- Examples: '2023-01-15', '1990-12-25'
```

#### Timestamp Type
```sql
-- Date and time with precision
created_at TIMESTAMP
-- Examples: '2023-01-15 14:30:25', '2023-01-15T14:30:25Z'
```

### Complex Types

#### JSON Type
```sql
-- JSON document
metadata JSON
-- Examples: '{"key": "value"}', '{"users": [1, 2, 3]}'
```

#### BLOB Type
```sql
-- Binary large object
image_data BLOB
-- Examples: Binary data, encoded strings
```

#### Decimal Type
```sql
-- Precise decimal number
price DECIMAL(10,2)
-- Examples: 123.45, 0.01, 99999999.99
```

#### Enum Type
```sql
-- User-defined enumeration
status ENUM('active', 'inactive', 'pending')
-- Examples: 'active', 'inactive', 'pending'
```

### NULL Values

All types support NULL values to represent missing or unknown data:

```sql
-- NULL can be used with any type
name STRING NULL
age INT NULL
is_active BOOL NULL
```

## Tables and Schemas

### Table Structure

A table in ColibrìDB consists of:

- **Columns**: Named attributes with specific data types
- **Constraints**: Rules that data must follow
- **Indexes**: Structures for fast data access
- **Metadata**: Information about the table structure

### Column Definition

```sql
CREATE TABLE users (
    id INT PRIMARY KEY,                    -- Primary key constraint
    name STRING NOT NULL,                  -- Not null constraint
    email STRING UNIQUE,                   -- Unique constraint
    age INT CHECK (age >= 0),             -- Check constraint
    created_at TIMESTAMP DEFAULT NOW(),   -- Default value
    updated_at TIMESTAMP                  -- Regular column
);
```

### Schema Evolution

ColibrìDB supports dynamic schema changes:

```sql
-- Add a new column
ALTER TABLE users ADD COLUMN phone STRING;

-- Modify an existing column
ALTER TABLE users MODIFY COLUMN email STRING(255);

-- Drop a column
ALTER TABLE users DROP COLUMN phone;

-- Add a constraint
ALTER TABLE users ADD CONSTRAINT chk_age CHECK (age >= 18);
```

## Indexes and Performance

### Index Types

#### B+Tree Index
- **Use Case**: Range queries, sorting
- **Performance**: O(log n) for lookups
- **Example**: `CREATE INDEX idx_users_email ON users(email)`

#### Hash Index
- **Use Case**: Equality lookups
- **Performance**: O(1) average case
- **Example**: `CREATE INDEX idx_users_id ON users(id) USING HASH`

#### ART (Adaptive Radix Tree) Index
- **Use Case**: String prefix searches
- **Performance**: O(k) where k is key length
- **Example**: `CREATE INDEX idx_users_name ON users(name) USING ART`

#### LSM-Tree Index
- **Use Case**: Write-heavy workloads
- **Performance**: Excellent write performance
- **Example**: `CREATE INDEX idx_logs_timestamp ON logs(timestamp) USING LSM`

### Index Selection

ColibrìDB automatically selects the best index type based on:

- **Query Patterns**: Type of queries expected
- **Data Characteristics**: Size, distribution, cardinality
- **Workload**: Read vs. write ratio
- **Memory Constraints**: Available memory for indexes

## Transactions and Concurrency

### ACID Properties

#### Atomicity
All operations in a transaction succeed or fail together:

```sql
BEGIN TRANSACTION;
    INSERT INTO users (id, name) VALUES (1, 'Alice');
    INSERT INTO orders (user_id, amount) VALUES (1, 100.00);
    -- Both inserts succeed or both fail
COMMIT;
```

#### Consistency
Database remains in a valid state after each transaction:

```sql
-- This will fail due to foreign key constraint
INSERT INTO orders (user_id, amount) VALUES (999, 100.00);
-- User 999 doesn't exist, so the insert is rejected
```

#### Isolation
Concurrent transactions don't interfere with each other:

```sql
-- Transaction 1
BEGIN TRANSACTION;
SELECT * FROM users WHERE id = 1;
-- Transaction 2 can't modify user 1 until Transaction 1 commits
```

#### Durability
Committed changes persist even after system failures:

```sql
COMMIT;
-- Changes are written to disk and will survive a crash
```

### Isolation Levels

#### Read Committed
- **Default Level**: Most common isolation level
- **Behavior**: Reads see only committed data
- **Use Case**: General purpose applications

#### Repeatable Read
- **Behavior**: Consistent reads within a transaction
- **Use Case**: Financial applications, reporting

#### Serializable
- **Behavior**: Highest isolation level
- **Use Case**: Critical data integrity requirements

### MVCC (Multi-Version Concurrency Control)

ColibrìDB uses MVCC to provide high concurrency:

- **Version Chains**: Multiple versions of each row
- **Snapshot Isolation**: Consistent point-in-time views
- **Garbage Collection**: Automatic cleanup of old versions

## Memory Management

### Buffer Pool

The buffer pool manages data pages in memory:

- **LRU Eviction**: Least recently used pages are evicted
- **Dirty Page Tracking**: Modified pages are written to disk
- **Prefetching**: Predictive loading of related pages

### Memory Allocation

- **Memory Pools**: Efficient allocation for common operations
- **SIMD Operations**: Vectorized processing for better performance
- **Memory Mapping**: Direct memory access to data files

## Storage Architecture

### Page-Based Storage

Data is stored in fixed-size pages:

- **Page Size**: 8KB (configurable)
- **Page Types**: Data pages, index pages, system pages
- **Page Management**: Allocation, deallocation, fragmentation handling

### Write-Ahead Logging (WAL)

All changes are logged before being applied:

- **Durability**: Ensures data survives crashes
- **Recovery**: Fast recovery from system failures
- **Performance**: Sequential writes are faster than random writes

### Compression

Data compression reduces storage requirements:

- **Page-Level Compression**: Compress individual pages
- **Column-Level Compression**: Compress similar data
- **Dictionary Compression**: Replace repeated values with references

## Query Processing

### Query Lifecycle

1. **Parsing**: SQL is parsed into an abstract syntax tree
2. **Planning**: Query planner generates execution plans
3. **Optimization**: Cost-based optimizer selects best plan
4. **Execution**: Query executor runs the selected plan
5. **Result**: Results are returned to the client

### Query Optimization

- **Cost-Based Optimization**: Selects plans based on estimated costs
- **Index Selection**: Automatically chooses appropriate indexes
- **Join Ordering**: Optimizes the order of table joins
- **Predicate Pushdown**: Pushes filters closer to data sources

## Security and Access Control

### Authentication

- **User Management**: Create and manage database users
- **Password Policies**: Enforce strong password requirements
- **Session Management**: Secure session handling

### Authorization

- **Role-Based Access Control**: Assign permissions to roles
- **Resource-Level Permissions**: Control access to databases, tables, columns
- **Audit Logging**: Track all database activities

### Data Protection

- **Encryption**: Encrypt data at rest and in transit
- **Data Masking**: Hide sensitive data from unauthorized users
- **Backup Security**: Encrypt backup files

## Monitoring and Observability

### Metrics Collection

- **Performance Metrics**: Query execution times, throughput
- **Resource Metrics**: CPU, memory, disk usage
- **Business Metrics**: Custom application metrics

### Logging

- **Structured Logging**: JSON-formatted log entries
- **Log Levels**: Configurable verbosity
- **Log Rotation**: Automatic log management

### Profiling

- **Query Profiling**: Detailed execution analysis
- **Memory Profiling**: Memory usage patterns
- **Performance Profiling**: Bottleneck identification

## Next Steps

Now that you understand the core concepts:

- [Database Management](05-database-management.md) - Learn to work with databases
- [SQL Reference](06-sql-reference.md) - Master the SQL language
- [CLI Reference](07-cli-reference.md) - Use the command-line interface

---

*These concepts form the foundation of ColibrìDB. For implementation details, see the [API Reference](11-api-reference.md).*
