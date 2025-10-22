# ColibriCore — Core Engine

The core database engine implementation for ColibrìDB, providing all essential database functionality with formal verification through TLA+ specifications.

## Core Modules

### Query Processing
- **`SQL/`** — SQL lexer, parser, AST, and query interface
- **`Planner/`** — Query planner with Volcano operators and cost model
- **`Query/`** — Query execution engine and optimization

### Transaction Management
- **`Transaction/`** — Transaction manager, isolation levels, and 2PC
- **`MVCC/`** — Multi-Version Concurrency Control implementation
- **`WAL/`** — Write-Ahead Logging and recovery system

### Storage Engine
- **`Storage/`** — Page management, heap tables, and file storage
- **`Buffer/`** — Buffer pool with LRU/Clock-Sweep eviction
- **`Indexes/`** — B+Tree, Hash, ART, and other index implementations

### System Components
- **`Core/`** — Fundamental types and utilities
- **`Catalog/`** — System catalog and metadata management
- **`Security/`** — Authentication and authorization
- **`Recovery/`** — ARIES crash recovery implementation

### Advanced Features
- **`Distributed/`** — Distributed transaction management
- **`Replication/`** — Data replication and consistency
- **`Monitoring/`** — Performance monitoring and metrics
- **`Testing/`** — Testing framework and chaos engineering

## Architecture

ColibriCore follows a modular architecture with clear separation of concerns:

- **Actor-based concurrency** using Swift's actor model
- **Protocol-oriented design** for dependency injection
- **Comprehensive error handling** with typed errors
- **Formal verification** through TLA+ specifications
- **Performance optimization** with caching and batching

## Getting Started

For detailed information about each module, see:
- **Technical Documentation**: `docs/wiki/` for comprehensive guides
- **API Reference**: Inline documentation in each Swift file
- **Examples**: `Examples/` directory for usage examples

## Development

This module is part of the larger ColibrìDB project. See the main [README](../README.md) for build instructions and project overview.

