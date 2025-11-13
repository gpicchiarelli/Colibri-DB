# ColibrìDB API Stability Commitment

## Version: 1.0.0

### Public API Guarantee

Starting with version 1.0.0, ColibrìDB commits to API stability with the following guarantees:

#### ✅ STABLE APIs (Will Not Change)

**Core Types** (`ColibriCore/Core/Types.swift`):
- `TxID`, `LSN`, `PageID`, `RID`, `Timestamp`
- `Value`, `Key` type aliases
- `IsolationLevel` enum

**WAL Module** (`ColibriCore/WAL/`):
- `WALManager.appendRecord(txId:kind:data:) -> LSN`
- `WALManager.flushLog() async throws`
- `WALManager.checkpoint() async throws -> LSN`
- `WALRecord` protocol

**MVCC Module** (`ColibriCore/MVCC/`):
- `MVCCManager.beginTransaction(txId:) async throws`
- `MVCCManager.commitTransaction(txId:) async throws`
- `MVCCManager.read(txId:key:) async throws -> Value?`
- `MVCCManager.write(txId:key:value:) async throws`

**Transaction Module** (`ColibriCore/Transaction/`):
- `TransactionManager.begin() async throws -> TxID`
- `TransactionManager.commit(txId:) async throws`
- `TransactionManager.abort(txId:) async throws`

#### ⚠️ EVOLVING APIs (May Change with Deprecation)

**Index Module** (`ColibriCore/Indexes/`):
- Index implementations may add new methods
- Existing methods will be deprecated, not removed
- Minimum 2 minor versions deprecation period

**Performance Module** (`ColibriCore/Performance/`):
- Metrics structure may evolve
- Backward compatibility maintained via versioned exports

**Observability Module** (`ColibriCore/Monitoring/`):
- Log format may change
- Correlation ID format guaranteed stable

#### 🚫 UNSTABLE APIs (May Change Without Notice)

**Internal APIs**:
- Any type/function marked with `_` prefix
- Types in `ColibriCore/Utilities/` (unless documented as stable)
- Test-only APIs

### Versioning Policy

**Semantic Versioning (SemVer)**:
- **MAJOR** (1.x.x): Breaking API changes
- **MINOR** (x.1.x): New features, backward compatible
- **PATCH** (x.x.1): Bug fixes, no API changes

### Deprecation Policy

1. **Announcement**: Deprecated APIs marked with `@available(*, deprecated, message: "...")`
2. **Migration Period**: Minimum 2 minor versions (e.g., deprecated in 1.2.0, removed in 1.4.0)
3. **Documentation**: Migration guide provided for all deprecations
4. **Tooling**: `coldb migrate-api` tool to assist upgrades

### On-Disk Format Stability

**Format Version**: 1.0.0

**Guarantee**:
- All 1.x.x releases can read format 1.0.0
- Format changes require MAJOR version bump
- Migration tool provided for format upgrades

**Backward Compatibility**:
- ColibrìDB 1.x.x can read formats: 1.0.0, 0.9.0, 0.8.0
- Forward compatibility NOT guaranteed (1.0.0 cannot read 2.0.0)

### Protocol Stability

**Network Protocol**: Version 1

**Wire Format**:
- Message framing: Fixed
- Encoding: PostgreSQL wire protocol compatible (subset)
- Authentication: SCRAM-SHA-256

### Breaking Change Policy

**When We Will Break APIs**:
- Critical security vulnerabilities
- Data corruption bugs
- Performance issues requiring architectural changes

**Process**:
1. Security advisory published
2. Patched version released within 48 hours
3. Migration guide provided
4. Community notification (email, GitHub, Discord)

### Commitment Date

**Effective**: 2025-11-12
**Signed**: ColibrìDB Maintainers

---

## API Stability Badge

```
┌─────────────────────────────────────┐
│  ColibrìDB v1.0.0                   │
│  API Stability: ✅ GUARANTEED       │
│  Format Stability: ✅ GUARANTEED    │
│  Compatibility: macOS 13+, Swift 5.9+│
└─────────────────────────────────────┘
```

## Contact

Questions about API stability: api-stability@colibri-db.org

