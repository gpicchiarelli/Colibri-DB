# Architecture Overview

## System Architecture

ColibrìDB is built with a modular, layered architecture that separates concerns and enables extensibility. The system is designed around several key principles:

- **Layered Design**: Clear separation between storage, query processing, and interface layers
- **Plugin Architecture**: Extensible system for custom data structures and operations
- **Multi-Database Support**: Isolated database environments with shared infrastructure
- **Performance Optimization**: Hardware-specific optimizations for Apple Silicon

## High-Level Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                    Application Layer                        │
├─────────────────────────────────────────────────────────────┤
│  CLI Interface  │  SQL Interface  │  Programmatic API      │
├─────────────────────────────────────────────────────────────┤
│                    Query Processing Layer                   │
├─────────────────────────────────────────────────────────────┤
│  SQL Parser  │  Query Planner  │  Query Executor  │  Optimizer │
├─────────────────────────────────────────────────────────────┤
│                    Transaction Management                   │
├─────────────────────────────────────────────────────────────┤
│  MVCC  │  Lock Manager  │  Two-Phase Commit  │  WAL        │
├─────────────────────────────────────────────────────────────┤
│                    Storage Layer                           │
├─────────────────────────────────────────────────────────────┤
│  Buffer Pool  │  Page Manager  │  Index Manager  │  Catalog  │
├─────────────────────────────────────────────────────────────┤
│                    Physical Storage                        │
├─────────────────────────────────────────────────────────────┤
│  File System  │  Memory Mapped Files  │  Compression      │
└─────────────────────────────────────────────────────────────┘
```

## Core Components

### 1. Storage Layer

The storage layer is responsible for persistent data storage and retrieval.

#### Buffer Pool Manager
- **Purpose**: Manages data pages in memory for efficient access
- **Features**: LRU eviction, dirty page tracking, prefetching
- **Configuration**: Configurable size, eviction policies

#### Page Manager
- **Purpose**: Handles physical page allocation and deallocation
- **Features**: Page-level operations, space management, fragmentation handling
- **Types**: Data pages, index pages, system pages

#### Index Manager
- **Purpose**: Manages various index types for fast data access
- **Supported Types**: B+Tree, ART (Adaptive Radix Tree), LSM-Tree, Hash
- **Features**: Automatic index selection, bulk loading, maintenance

### 2. Transaction Management

#### MVCC (Multi-Version Concurrency Control)
- **Purpose**: Enables concurrent access without blocking
- **Features**: Version chains, snapshot isolation, garbage collection
- **Benefits**: High concurrency, consistent reads

#### Lock Manager
- **Purpose**: Manages locks for critical sections
- **Features**: Deadlock detection, lock escalation, timeout handling
- **Types**: Shared, exclusive, intention locks

#### Two-Phase Commit
- **Purpose**: Ensures distributed transaction consistency
- **Phases**: Prepare and commit phases
- **Features**: Coordinator/participant model, recovery support

#### Write-Ahead Logging (WAL)
- **Purpose**: Ensures durability and crash recovery
- **Features**: Sequential logging, checkpointing, replay capability
- **Benefits**: Fast recovery, reduced I/O

### 3. Query Processing

#### SQL Parser
- **Purpose**: Parses SQL statements into internal representations
- **Features**: Syntax validation, semantic analysis, error reporting
- **Supported**: DDL, DML, DQL statements

#### Query Planner
- **Purpose**: Generates optimal execution plans
- **Features**: Cost-based optimization, join ordering, index selection
- **Algorithms**: Dynamic programming, heuristic methods

#### Query Executor
- **Purpose**: Executes query plans efficiently
- **Features**: Pipeline execution, operator fusion, vectorization
- **Optimizations**: SIMD operations, memory pooling

### 4. Multi-Database Catalog

#### Database Management
- **Purpose**: Manages multiple isolated databases
- **Features**: Database creation, deletion, metadata management
- **Isolation**: Complete separation between databases

#### Schema Management
- **Purpose**: Manages table schemas and metadata
- **Features**: Schema evolution, constraint management, type checking
- **Types**: Tables, views, indexes, sequences

#### Statistics Collection
- **Purpose**: Collects and maintains query optimization statistics
- **Features**: Cardinality estimation, histogram generation, cost modeling
- **Updates**: Automatic and manual statistics updates

## Data Flow

### 1. Query Processing Flow

```
SQL Query
    ↓
SQL Parser
    ↓
Query Planner
    ↓
Query Executor
    ↓
Storage Layer
    ↓
Physical Storage
```

### 2. Transaction Flow

```
BEGIN TRANSACTION
    ↓
Query Processing
    ↓
Lock Acquisition
    ↓
Data Modification
    ↓
WAL Logging
    ↓
COMMIT/ROLLBACK
    ↓
Lock Release
```

### 3. Data Storage Flow

```
Data Insert
    ↓
Buffer Pool
    ↓
Page Manager
    ↓
Index Updates
    ↓
WAL Logging
    ↓
Physical Storage
```

## Plugin Architecture

ColibrìDB supports a plugin system for extending functionality:

### Data Structure Plugins
- Custom index types
- Specialized storage engines
- Compression algorithms
- Encryption methods

### Query Processing Plugins
- Custom operators
- User-defined functions
- Aggregation functions
- Window functions

### Storage Plugins
- Custom page formats
- Compression codecs
- Encryption providers
- Backup/restore handlers

## Performance Optimizations

### Apple Silicon Optimizations
- **SIMD Operations**: Vectorized data processing
- **Memory Hierarchy**: Optimized for M1/M2/M3 caches
- **Power Efficiency**: Dynamic frequency scaling awareness
- **Unified Memory**: Efficient CPU/GPU data sharing

### General Optimizations
- **Memory Pooling**: Reduced allocation overhead
- **Lock-Free Structures**: High-concurrency data structures
- **Batch Processing**: Reduced per-operation overhead
- **Prefetching**: Predictive data loading

## Scalability Considerations

### Horizontal Scaling
- **Sharding**: Database partitioning across instances
- **Replication**: Read replicas for load distribution
- **Federation**: Cross-database query processing

### Vertical Scaling
- **Memory Scaling**: Larger buffer pools
- **CPU Scaling**: Parallel query processing
- **Storage Scaling**: Faster storage devices

## Security Architecture

### Authentication
- **User Management**: Role-based access control
- **Authentication**: Multiple authentication methods
- **Session Management**: Secure session handling

### Authorization
- **Permission System**: Granular access control
- **Resource Protection**: Database and table-level permissions
- **Audit Logging**: Comprehensive activity logging

### Data Protection
- **Encryption**: At-rest and in-transit encryption
- **Data Masking**: Sensitive data protection
- **Backup Security**: Encrypted backup storage

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

Now that you understand ColibrìDB's architecture, explore the core concepts:

- [Core Concepts](04-core-concepts.md) - Understanding the fundamental concepts
- [Database Management](05-database-management.md) - Working with databases
- [SQL Reference](06-sql-reference.md) - SQL language reference

---

*The architecture is designed for extensibility and performance. For implementation details, see the [API Reference](11-api-reference.md).*
