# RFC 0001: ColibrìDB Architecture Overview

**Status**: Standards Track  
**Author**: ColibrìDB Team  
**Date**: 2025-11-18  
**TLA+ Spec**: `spec/ColibriDB.tla`

## Abstract

This RFC defines the overall architecture of ColibrìDB, including design patterns, module organization, and Apple-first design principles.

## 1. Introduction

ColibrìDB follows a layered architecture optimized for Apple platforms, with formal verification at each layer. The system is designed for high performance, correctness, and maintainability.

## 2. Architecture Layers

### 2.1 Presentation Layer

**Components**:
- CLI (`coldb`): Command-line interface
- Server (`coldb-server`): Network server
- Benchmarks: Performance testing tools

**Responsibilities**:
- User interaction
- Request/response handling
- Connection management

### 2.2 Query Processing Layer

**Components**:
- SQL Parser (RFC 0024)
- Query Optimizer (RFC 0025)
- Query Executor (RFC 0026)
- Query Planner (RFC 0024)

**Responsibilities**:
- Parse SQL queries
- Generate optimal execution plans
- Execute queries
- Return results

### 2.3 Transaction Layer

**Components**:
- Transaction Manager (RFC 0019)
- MVCC Manager (RFC 0020)
- Lock Manager (RFC 0021)
- Two-Phase Commit (RFC 0023)

**Responsibilities**:
- Transaction lifecycle management
- Concurrency control
- ACID guarantees
- Distributed transaction coordination

### 2.4 Storage Layer

**Components**:
- Buffer Manager (RFC 0004)
- Write-Ahead Log (RFC 0005)
- Storage Manager (RFC 0006)
- Heap Table (RFC 0007)
- Page Directory (RFC 0008)

**Responsibilities**:
- Page caching and eviction
- Durability guarantees
- Data organization
- Free space management

### 2.5 Index Layer

**Components**:
- Index Manager (RFC 0010)
- Multiple index types (RFC 0011-0018)

**Responsibilities**:
- Index creation and maintenance
- Query optimization support
- Range and point lookups

### 2.6 Recovery Layer

**Components**:
- ARIES Recovery (RFC 0032)
- Checkpoint Manager (RFC 0034)

**Responsibilities**:
- Crash recovery
- Transaction rollback
- Data consistency

### 2.7 System Services Layer

**Components**:
- Catalog Manager (RFC 0040)
- Schema Evolution (RFC 0041)
- Statistics Maintenance (RFC 0042)
- Security (RFC 0035-0039)

**Responsibilities**:
- Metadata management
- Schema changes
- Performance statistics
- Authentication and authorization

## 3. Design Patterns

### 3.1 Actor Model (Swift Actors)

**Usage**: All managers are Swift actors for thread-safe concurrency.

```swift
public actor BufferManager {
    // Thread-safe state
    private var bufferPool: [FrameIndex: BufferPage] = [:]
    
    // Methods are automatically isolated
    public func getPage(pageId: PageID) async throws -> BufferPage {
        // Safe concurrent access
    }
}
```

**Benefits**:
- No explicit locking required
- Compile-time safety guarantees
- Efficient message passing

### 3.2 Protocol-Oriented Programming

**Usage**: Abstractions through protocols for testability and flexibility.

```swift
public protocol DiskManager: Sendable {
    func readPage(pageId: PageID) async throws -> Data
    func writePage(pageId: PageID, data: Data) async throws
}
```

**Benefits**:
- Easy testing with mocks
- Multiple implementations
- Dependency injection

### 3.3 Value Types

**Usage**: Immutable data structures where possible.

```swift
public struct BufferPage: Sendable {
    public let pageId: PageID
    public let data: Data
    public let lsn: LSN
    // Immutable for thread safety
}
```

**Benefits**:
- Thread-safe by default
- Copy-on-write optimization
- Predictable behavior

### 3.4 Async/Await

**Usage**: All I/O operations use async/await.

```swift
public func fetchPage(pageId: PageID) async throws -> BufferPage {
    let pageData = try await diskManager.readPage(pageId: pageId)
    // Non-blocking I/O
}
```

**Benefits**:
- Non-blocking I/O
- Structured concurrency
- Error propagation

## 4. Module Organization

### 4.1 Directory Structure

```
Sources/ColibriCore/
├── Buffer/           # Buffer management
├── BufferPool/       # Buffer pool implementation
├── WAL/              # Write-ahead logging
├── Storage/          # Storage layer
├── Index/            # Index management
├── Indexes/          # Index implementations
├── Transaction/      # Transaction management
├── MVCC/             # Multi-version concurrency
├── Query/            # Query processing
├── Recovery/         # Crash recovery
├── Security/         # Security and encryption
├── Catalog/          # System catalog
├── Network/          # Networking
├── Server/           # Server implementation
├── Distributed/      # Distributed systems
├── Monitoring/       # Observability
└── Core/             # Core types and utilities
```

### 4.2 Module Dependencies

```
Query Layer
    ↓
Transaction Layer
    ↓
Storage Layer ← Index Layer
    ↓
Buffer Manager ← WAL
    ↓
Disk Manager
```

## 5. Apple-First Design Choices

### 5.1 Swift 6.0 Features

- **Strict Concurrency**: All code checked for concurrency safety
- **Actors**: Native concurrency primitive
- **Async/Await**: Structured asynchronous programming
- **Sendable**: Type system for safe data sharing

### 5.2 Platform-Specific Optimizations

- **APFS**: Leverages APFS features (RFC 0060)
- **Grand Central Dispatch**: Efficient task scheduling
- **Metal**: Future GPU acceleration (planned)
- **CryptoKit**: Hardware-accelerated encryption

### 5.3 Memory Management

- **ARC**: Automatic reference counting
- **Value Types**: Stack allocation where possible
- **Buffer Pool**: Explicit memory management for pages
- **Zero-Copy**: Avoid unnecessary copies

### 5.4 Performance Characteristics

- **Single-Threaded Per Actor**: No internal locking
- **Async I/O**: Non-blocking operations
- **Batch Operations**: Group commit, batch inserts
- **Index-Aware**: Statistics-driven optimization

## 6. Concurrency Model

### 6.1 Actor Isolation

Each manager is an actor, ensuring:
- Exclusive access to internal state
- No race conditions
- Compile-time safety

### 6.2 Async Boundaries

I/O operations cross actor boundaries:
```swift
// Actor A calls Actor B
let page = try await bufferManager.getPage(pageId: pageId)
```

### 6.3 Structured Concurrency

Tasks are structured with clear lifetimes:
```swift
try await withThrowingTaskGroup(of: Void.self) { group in
    group.addTask { await manager1.operation() }
    group.addTask { await manager2.operation() }
}
```

## 7. Error Handling

### 7.1 Error Types

Domain-specific error types:
```swift
public enum BufferError: Error {
    case pageNotFound
    case pagePinned
    case noPageToEvict
}
```

### 7.2 Error Propagation

Errors propagate through async boundaries:
```swift
func operation() async throws -> Result {
    try await subOperation() // Propagates errors
}
```

## 8. Testing Strategy

### 8.1 Unit Tests

Each module has comprehensive unit tests:
- Functionality tests
- Invariant verification
- Edge case handling

### 8.2 Integration Tests

End-to-end tests verify:
- Cross-module interactions
- Transaction processing
- Recovery scenarios

### 8.3 Property Tests

TLA+ properties verified in tests:
- Invariants always hold
- Temporal properties
- Safety guarantees

## 9. Formal Verification

### 9.1 TLA+ Specifications

Each component has a corresponding TLA+ spec:
- State variables
- Actions (state transitions)
- Invariants (properties)
- Temporal formulas

### 9.2 Verification Process

1. Write TLA+ specification
2. Model-check with TLC
3. Implement in Swift
4. Verify implementation matches spec

## 10. References

- **RFC 0000**: Overview and Index
- **TLA+ Spec**: `spec/ColibriDB.tla`
- **Swift Concurrency**: [swift.org/concurrency](https://swift.org/blog/swift-concurrency/)
- **Actor Model**: [Actor Model Wikipedia](https://en.wikipedia.org/wiki/Actor_model)

---

**Next**: See RFC 0004 for Buffer Manager details.

