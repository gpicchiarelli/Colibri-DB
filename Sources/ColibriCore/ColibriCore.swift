//
//  ColibriCore.swift
//  ColibrìDB Public API Exports
//
//  Author: ColibrìDB Team
//  Date: 2025-10-19
//
//  This file exports the public API of ColibrìDB Core module
//  All implementations are based on formal TLA+ specifications
//

import Foundation

// MARK: - Core Types

// Re-export all core types
@_exported import struct Foundation.Data
@_exported import struct Foundation.Date
@_exported import struct Foundation.URL

// Core types are defined in their respective files and automatically exported
// due to public access level

// MARK: - Main Database Interface

/// Main ColibrìDB interface
/// Use this class to create and interact with a database instance
///
/// Example:
/// ```swift
/// let config = ColibrìDB.Configuration(
///     dataDirectory: URL(fileURLWithPath: "/path/to/data")
/// )
/// let db = try ColibrìDB(config: config)
/// try await db.start()
///
/// // Use the database
/// let txID = try await db.beginTransaction()
/// // ... perform operations ...
/// try await db.commit(txID)
///
/// try await db.shutdown()
/// ```

// MARK: - Module Organization

/*
 ColibrìDB Module Organization:
 
 ├── Core/
 │   └── Types.swift                    - Basic types (LSN, TxID, Value, etc.)
 │
 ├── WAL/
 │   ├── WALTypes.swift                - WAL record types
 │   └── FileWAL.swift                 - Write-Ahead Log implementation
 │
 ├── MVCC/
 │   ├── MVCCTypes.swift               - MVCC types (Version, Snapshot)
 │   └── MVCCManager.swift             - Multi-Version Concurrency Control
 │
 ├── BufferPool/
 │   └── BufferPool.swift              - Page caching with Clock-Sweep
 │
 ├── Storage/
 │   └── HeapTable.swift               - Slotted page heap storage
 │
 ├── Indexes/
 │   └── BTreeIndex.swift              - B+Tree index implementation
 │
 ├── Transaction/
 │   ├── LockManager.swift             - Lock management with deadlock detection
 │   └── TransactionManager.swift     - ACID transaction management
 │
 ├── Recovery/
 │   └── ARIESRecovery.swift          - ARIES 3-phase recovery
 │
 ├── Query/
 │   └── QueryExecutor.swift          - Query execution engine
 │
 ├── Catalog/
 │   └── Catalog.swift                - System catalog and metadata
 │
 ├── Security/
 │   └── Authentication.swift         - User authentication
 │
 ├── Distributed/
 │   └── Clock.swift                  - Hybrid Logical Clock
 │
 ├── Optimization/
 │   └── Compression.swift            - Data compression
 │
 ├── MultiTenancy/
 │   └── ResourceQuotas.swift         - Resource quota management
 │
 ├── Server/
 │   └── DatabaseServer.swift         - Database server
 │
 └── Database/
     └── ColibrìDB.swift               - Main database engine integration
 
 All implementations are based on formal TLA+ specifications located in spec/
 */

// MARK: - Version Information

/// ColibrìDB version information
public enum ColibriDBVersion {
    /// Major version
    public static let major = 1
    
    /// Minor version
    public static let minor = 0
    
    /// Patch version
    public static let patch = 0
    
    /// Full version string
    public static var versionString: String {
        return "\(major).\(minor).\(patch)"
    }
    
    /// Build information
    public static let buildDate = "2025-10-19"
    
    /// Full version with build info
    public static var fullVersion: String {
        return "ColibrìDB v\(versionString) (built \(buildDate))"
    }
}

// MARK: - Documentation

/*
 # ColibrìDB - A Formally Verified Database System
 
 ColibrìDB is a complete relational database management system with all components
 formally specified using TLA+ and implemented in Swift.
 
 ## Key Features
 
 - ✅ **ACID Transactions**: Full transaction support with MVCC
 - ✅ **Write-Ahead Logging**: Durability with WAL
 - ✅ **ARIES Recovery**: Crash recovery with Analysis, Redo, Undo
 - ✅ **Snapshot Isolation**: Multi-version concurrency control
 - ✅ **B+Tree Indexes**: Efficient indexing with range scans
 - ✅ **Lock Management**: Deadlock detection and resolution
 - ✅ **Buffer Pool**: Page caching with Clock-Sweep eviction
 - ✅ **Query Execution**: Relational operators and optimization
 - ✅ **Authentication**: Secure user authentication
 - ✅ **Distributed Clock**: Hybrid Logical Clock for distributed systems
 
 ## Formal Verification
 
 All core components have been formally specified in TLA+ and verified for:
 - Safety properties (invariants)
 - Liveness properties (progress guarantees)
 - Deadlock freedom
 - Serializability
 
 ## Architecture
 
 ColibrìDB follows a layered architecture:
 
 1. **Storage Layer**: WAL, Buffer Pool, Heap Tables, Indexes
 2. **Transaction Layer**: MVCC, Lock Manager, Transaction Manager
 3. **Recovery Layer**: ARIES crash recovery
 4. **Query Layer**: Query executor and optimizer
 5. **Server Layer**: Connection management and protocol
 6. **Security Layer**: Authentication and authorization
 
 ## Performance
 
 - Clock-Sweep eviction for efficient page caching
 - Group commit for WAL optimization
 - MVCC for high concurrency
 - B+Tree indexes for fast lookups
 
 ## References
 
 Based on foundational papers:
 - ARIES (Mohan et al., 1992)
 - Snapshot Isolation (Berenson et al., 1995)
 - B-Trees (Comer, 1979)
 - Hybrid Logical Clocks (Kulkarni & Demirbas, 2014)
 
 */

