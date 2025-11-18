# RFC 0000: ColibrìDB Overview and Index

**Status**: Informational  
**Author**: ColibrìDB Team  
**Date**: 2025-11-18  
**TLA+ Spec**: `spec/ColibriDB.tla`

## Abstract

ColibrìDB is a production-grade relational database management system (RDBMS) implemented in Swift 6.0 with formal verification using TLA+ specifications. This document provides an overview of the ColibrìDB architecture, design principles, and serves as an index to all technical RFCs.

## 1. Introduction

ColibrìDB is designed as an Apple-first database system, leveraging Swift's modern concurrency model (actors, async/await), type safety, and memory management. Every critical component is formally verified using TLA+ specifications to ensure correctness and reliability.

### 1.1 Design Principles

1. **Apple-First Architecture**: Native Swift implementation optimized for Apple platforms
2. **Formal Verification**: 69 TLA+ specifications for critical components
3. **Type Safety**: Strong typing throughout the codebase
4. **Concurrency Safety**: Swift actors and structured concurrency
5. **Performance**: Optimized for high-throughput transaction processing
6. **Correctness**: ACID properties with mathematical guarantees

### 1.2 Key Features

- **Storage Engine**: WAL, Buffer Pool, Heap Tables, Multiple Index Types (B+Tree, Hash, ART, LSM, Fractal Tree, T-Tree, SkipList, Bloom Filter)
- **Transaction Management**: MVCC, Lock Manager, ACID Properties, Two-Phase Commit
- **Query Processing**: SQL Parser, Cost-Based Optimizer, Physical Executor
- **Recovery**: ARIES Algorithm (Analysis, Redo, Undo phases)
- **Security**: Authentication, Authorization (RBAC, ABAC), Encryption
- **Scalability**: Sharding, Replication, Distributed Transactions

## 2. Architecture Overview

```
┌─────────────────────────────────────────────────────────────┐
│                    ColibrìDB Architecture                    │
├─────────────────────────────────────────────────────────────┤
│  CLI (coldb)  │  Server (coldb-server)  │  Benchmarks       │
├─────────────────────────────────────────────────────────────┤
│                    ColibriCore                              │
│  ┌────────────┬────────────┬────────────┬────────────┐     │
│  │   Catalog  │  Database  │   Planner  │  Functions │     │
│  └────────────┴────────────┴────────────┴────────────┘     │
│  ┌────────────┬────────────┬────────────┬────────────┐     │
│  │   Storage  │  Transaction│   Query   │  Recovery  │     │
│  │  Manager   │   Manager   │  Executor │  Manager   │     │
│  └────────────┴────────────┴────────────┴────────────┘     │
│  ┌────────────┬────────────┬────────────┬────────────┐     │
│  │     WAL    │  Buffer    │   Index    │   MVCC     │     │
│  │            │  Manager   │  Manager   │  Manager   │     │
│  └────────────┴────────────┴────────────┴────────────┘     │
│  ┌────────────┬────────────┬────────────┬────────────┐     │
│  │  Security  │  Network   │  Monitoring│ Distributed│     │
│  │  Manager   │  Protocol  │            │            │     │
│  └────────────┴────────────┴────────────┴────────────┘     │
└─────────────────────────────────────────────────────────────┘
```

## 3. RFC Index

### Core Architecture
- **RFC 0001**: Architecture Overview and Design Patterns
- **RFC 0002**: Core Types and Type System
- **RFC 0003**: Error Handling and Error Types

### Storage Layer
- **RFC 0004**: Buffer Manager
- **RFC 0005**: Write-Ahead Logging (WAL)
- **RFC 0006**: Storage Manager
- **RFC 0007**: Heap Table Implementation
- **RFC 0008**: Page Directory and Page Management
- **RFC 0009**: Disk Format and On-Disk Layout

### Index Layer
- **[RFC 0010: Index Manager](0010-index-manager.md)** - Index creation, management, and querying
- **RFC 0011**: B+Tree Index Implementation
- **RFC 0012**: Hash Index Implementation
- **RFC 0013**: Adaptive Radix Tree (ART) Index
- **RFC 0014**: Log-Structured Merge Tree (LSM)
- **RFC 0015**: Fractal Tree Index
- **RFC 0016**: T-Tree Index
- **RFC 0017**: SkipList Index
- **RFC 0018**: Bloom Filter

### Transaction Layer
- **[RFC 0019: Transaction Manager](0019-transaction-manager.md)** - Transaction lifecycle and ACID guarantees
- **[RFC 0020: Multi-Version Concurrency Control (MVCC)](0020-mvcc-manager.md)** - Snapshot isolation and version management
- **RFC 0021**: Lock Manager
- **RFC 0022**: Serializable Snapshot Isolation
- **RFC 0023**: Two-Phase Commit (2PC)

### Query Processing
- **RFC 0024**: SQL Parser
- **RFC 0025**: Query Optimizer
- **RFC 0026**: Query Executor
- **RFC 0027**: Join Algorithms
- **RFC 0028**: Aggregation Operations
- **RFC 0029**: Window Functions
- **RFC 0030**: Materialization Strategies
- **RFC 0031**: Prepared Statements

### Recovery
- **RFC 0032**: ARIES Recovery Algorithm
- **RFC 0033**: Point-in-Time Recovery
- **RFC 0034**: Checkpoint Mechanism

### Security
- **RFC 0035**: Authentication Manager
- **RFC 0036**: Authorization and Access Control
- **RFC 0037**: Role-Based Access Control (RBAC)
- **RFC 0038**: Encryption Service
- **RFC 0039**: Audit Manager

### System Management
- **RFC 0040**: Catalog Manager
- **RFC 0041**: Schema Evolution
- **RFC 0042**: Statistics Maintenance
- **RFC 0043**: VACUUM Operations
- **RFC 0044**: Backup and Restore

### Networking and Server
- **RFC 0045**: Wire Protocol
- **RFC 0046**: Connection Manager
- **RFC 0047**: Database Server
- **RFC 0048**: Authenticated Server

### Distributed Systems
- **RFC 0049**: Sharding Manager
- **RFC 0050**: Replication Manager
- **RFC 0051**: Consensus Protocol (Raft)
- **RFC 0052**: Distributed Transactions
- **RFC 0053**: Distributed Query Processing
- **RFC 0054**: Load Balancer
- **RFC 0055**: Clock Synchronization

### Performance and Optimization
- **RFC 0056**: Compression Service
- **RFC 0057**: Group Commit
- **RFC 0058**: Performance Monitoring
- **RFC 0059**: Resource Management
- **RFC 0060**: APFS Optimizations
- **RFC 0061**: Memory Management

### Testing and Reliability
- **RFC 0062**: Chaos Engineering
- **RFC 0063**: Fault Injection
- **RFC 0064**: Testing Framework

## 4. Apple-First Design Choices

### 4.1 Swift-Specific Optimizations

- **Swift Actors**: Thread-safe concurrency without locks
- **Async/Await**: Structured concurrency for I/O operations
- **Type Safety**: Compile-time guarantees for data correctness
- **ARC**: Automatic memory management
- **Value Types**: Performance-optimized data structures

### 4.2 Platform Integration

- **APFS**: Native file system optimizations
- **Grand Central Dispatch**: Efficient task scheduling
- **Foundation**: Native Swift APIs
- **CryptoKit**: Hardware-accelerated cryptography

### 4.3 Performance Characteristics

- **Zero-Copy**: Where possible, avoid data copies
- **Buffer Pool**: In-memory page caching
- **WAL Group Commit**: Batch writes for throughput
- **Index-Aware**: Query optimization uses index statistics

## 5. Formal Verification

Each RFC references TLA+ specifications in the `spec/` directory. The TLA+ specs define:

- **State Variables**: System state representation
- **Actions**: State transitions and operations
- **Invariants**: Properties that must always hold
- **Temporal Properties**: Liveness and safety guarantees

All implementations are verified to match their TLA+ specifications.

## 6. Implementation Status

| Module | RFC | Status | TLA+ Spec |
|--------|-----|--------|-----------|
| Buffer Manager | RFC 0004 | Complete | BufferPool.tla |
| WAL | RFC 0005 | Complete | WAL.tla |
| Storage Manager | RFC 0006 | Complete | Storage.tla |
| Index Manager | RFC 0010 | Complete | Index.tla |
| Transaction Manager | RFC 0019 | Complete | TransactionManager.tla |
| MVCC | RFC 0020 | Complete | MVCC.tla |
| Query Optimizer | RFC 0025 | Complete | QueryOptimizer.tla |
| ARIES Recovery | RFC 0032 | Complete | RECOVERY.tla |

*See individual RFCs for detailed status.*

## 7. References

- TLA+ Specifications: `spec/*.tla`
- Source Code: `Sources/ColibriCore/`
- Tests: `Tests/ColibriCoreTests/`
- Developer Guide: `.github/DEVELOPER_GUIDE.md`

## 8. Document Status

This RFC is **Informational** and serves as the entry point to all ColibrìDB documentation. Individual RFCs may have different statuses (Standards Track, Experimental, Informational).

---

**Next**: See RFC 0001 for detailed architecture overview.

