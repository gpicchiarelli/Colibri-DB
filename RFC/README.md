# ColibrìDB RFC Documentation

This directory contains Request for Comments (RFC) documents that define ColibrìDB as a standard, production-grade relational database management system. These RFCs provide complete documentation for understanding, implementing, and extending ColibrìDB.

## Purpose

The RFCs in this directory serve as:

1. **Complete Specification**: Comprehensive documentation of every component
2. **Implementation Guide**: Step-by-step instructions for implementing each module
3. **Design Rationale**: Detailed explanations of design choices and trade-offs
4. **Apple-First Optimizations**: Platform-specific optimizations for Apple platforms
5. **Formal Verification**: Mapping to TLA+ specifications for correctness

## Reading the RFCs

### Start Here

1. **RFC 0000**: Overview and Index - Start here to understand the structure
2. **RFC 0001**: Architecture Overview - Understand the overall architecture

### Core Components

3. **RFC 0004**: Buffer Manager - Page caching and eviction policies
4. **RFC 0005**: Write-Ahead Logging - Durability and crash recovery
5. **RFC 0006**: Storage Manager - Disk I/O and storage management
6. **RFC 0019**: Transaction Manager - Transaction lifecycle and ACID
7. **RFC 0020**: MVCC Manager - Multi-version concurrency control

### Additional Components

See **RFC 0000** for complete index of all RFCs.

## RFC Format

Each RFC follows this structure:

1. **Abstract**: Brief summary
2. **Introduction**: Purpose and overview
3. **Design Principles**: Core principles and constraints
4. **Architecture**: Component structure and relationships
5. **API Specification**: Complete API documentation
6. **Invariants**: TLA+ invariants and Swift implementations
7. **Performance Characteristics**: Performance targets and metrics
8. **Error Handling**: Error types and recovery strategies
9. **Testing**: Testing strategy and test cases
10. **Apple-First Optimizations**: Platform-specific features
11. **References**: Related RFCs and academic papers

## Status

| RFC | Component | Status | TLA+ Spec |
|-----|-----------|--------|-----------|
| 0000 | Overview | ✅ Complete | - |
| 0001 | Architecture | ✅ Complete | ColibriDB.tla |
| 0004 | Buffer Manager | ✅ Complete | BufferPool.tla |
| 0005 | Write-Ahead Logging | ✅ Complete | WAL.tla |
| 0006 | Storage Manager | 🚧 In Progress | Storage.tla |
| 0019 | Transaction Manager | 🚧 In Progress | TransactionManager.tla |
| 0020 | MVCC Manager | 🚧 In Progress | MVCC.tla |

*Status Legend*:
- ✅ Complete: Fully documented and verified
- 🚧 In Progress: Documentation in progress
- 📋 Planned: Planned for future documentation

## Contributing

When contributing to ColibrìDB:

1. Read relevant RFCs before making changes
2. Update RFCs when modifying components
3. Add new RFCs for new components
4. Verify implementations match TLA+ specs

## Related Documentation

- **TLA+ Specifications**: `spec/*.tla`
- **Source Code**: `Sources/ColibriCore/`
- **Tests**: `Tests/ColibriCoreTests/`
- **Developer Guide**: `.github/DEVELOPER_GUIDE.md`

## Apple-First Design

ColibrìDB is designed specifically for Apple platforms with:

- **Swift 6.0**: Strict concurrency checking
- **Swift Actors**: Thread-safe concurrency
- **Async/Await**: Structured asynchronous programming
- **APFS**: Native file system optimizations
- **CryptoKit**: Hardware-accelerated encryption
- **ARC**: Automatic memory management

All RFCs include sections on Apple-first optimizations and platform-specific features.

## Questions?

For questions about RFCs:
- Open an issue on GitHub
- Check the TLA+ specifications in `spec/`
- Review the source code in `Sources/ColibriCore/`

---

**Last Updated**: 2025-11-18

