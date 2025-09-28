# 🐦 ColibrìDB

> **A Modern, High-Performance Relational Database Management System built with Swift 6.2**

[![Build Status](https://img.shields.io/github/actions/workflow/status/gpicchiarelli/Colibrì-DB/ci.yml?branch=main&style=for-the-badge)](https://github.com/gpicchiarelli/Colibrì-DB/actions/workflows/ci.yml)
[![CodeQL](https://img.shields.io/github/actions/workflow/status/gpicchiarelli/Colibrì-DB/codeql.yml?label=CodeQL&branch=main&style=for-the-badge)](https://github.com/gpicchiarelli/Colibrì-DB/actions/workflows/codeql.yml)
[![Swift](https://img.shields.io/badge/Swift-6.2-orange?style=for-the-badge&logo=swift)](https://swift.org)
[![SwiftPM](https://img.shields.io/badge/SwiftPM-Compatible-brightgreen?style=for-the-badge)](https://swift.org/package-manager/)
[![Platform](https://img.shields.io/badge/Platform-macOS%2013%2B-lightgrey?style=for-the-badge&logo=apple)](https://www.apple.com/macos/)
[![License](https://img.shields.io/badge/License-BSD%203--Clause-blue?style=for-the-badge)](https://opensource.org/licenses/BSD-3-Clause)
[![GitHub stars](https://img.shields.io/github/stars/gpicchiarelli/Colibrì-DB?style=for-the-badge&logo=github)](https://github.com/gpicchiarelli/Colibrì-DB/stargazers)
[![GitHub issues](https://img.shields.io/github/issues/gpicchiarelli/Colibrì-DB?style=for-the-badge&logo=github)](https://github.com/gpicchiarelli/Colibrì-DB/issues)
[![GitHub pull requests](https://img.shields.io/github/issues-pr/gpicchiarelli/Colibrì-DB?style=for-the-badge&logo=github)](https://github.com/gpicchiarelli/Colibrì-DB/pulls)
[![GitHub last commit](https://img.shields.io/github/last-commit/gpicchiarelli/Colibrì-DB?style=for-the-badge&logo=github)](https://github.com/gpicchiarelli/Colibrì-DB/commits/main)
[![GitHub contributors](https://img.shields.io/github/contributors/gpicchiarelli/Colibrì-DB?style=for-the-badge&logo=github)](https://github.com/gpicchiarelli/Colibrì-DB/graphs/contributors)
[![PRs Welcome](https://img.shields.io/badge/PRs-welcome-brightgreen?style=for-the-badge)](https://github.com/gpicchiarelli/Colibrì-DB/pulls)

**ColibrìDB** is an experimental, high-performance relational database management system (RDBMS) designed to handle millions of logical connections, optimized for macOS and Apple Silicon. Built with Swift 6.2, it features a modular architecture with heap storage engine, Write-Ahead Logging (WAL), Multi-Version Concurrency Control (MVCC), pluggable indexes, and an administrative CLI.

## ✨ Key Features

### 🗄️ **Advanced Storage & Buffering**
- **Heap File Storage**: Paginated heap files with slot directory and persistent Free Space Map
- **Online Compaction**: Real-time data reorganization without downtime
- **LRU/Clock Buffer Pool**: Background flusher with namespace quotas and intelligent eviction
- **Apple Silicon Optimized**: Native ARM64 performance with CRC32 acceleration

### 🔒 **Enterprise-Grade Durability**
- **WAL v2**: Typed records with CRC32 checksums and ARIES-like recovery
- **Checkpoint System**: Efficient recovery with Dirty Page Table management
- **Transaction Logging**: Complete UNDO/REDO support for data consistency
- **Index Recovery**: B+Tree index replay from WAL during recovery

### 🚀 **High-Performance Indexing**
- **Persistent B+Tree**: Disk-backed with checkpoint support and bulk operations
- **Pluggable Index Types**: Hash, ART (Adaptive Radix Tree), SkipList, Fractal Tree, LSM
- **Deep Validation**: Comprehensive integrity checks and online maintenance
- **Memory-Efficient**: Optimized for large datasets with smart caching

### ⚡ **Modern Concurrency Control**
- **MVCC**: Multi-Version Concurrency Control with configurable isolation levels
- **Lock Manager**: Deadlock detection, timeout handling, and granular locking
- **2PC Support**: Two-Phase Commit for distributed transaction consistency
- **Snapshot Isolation**: Consistent read views for complex queries

### 🧠 **Intelligent Query Processing**
- **Volcano Iterator**: Cost-based query planner with predicate pushdown
- **Advanced Operators**: Scan, filter, project, sort, and join operations
- **Materialized Views**: Cached query results for improved performance
- **SQL Parser**: Full SQL compatibility with modern syntax support

### 🛠️ **Operational Excellence**
- **Administrative CLI**: Complete database management with `coldb` tool
- **CSV Import/Export**: Bulk data operations with format validation
- **Prometheus Metrics**: Production-ready monitoring and observability
- **Policy Engine**: Automated maintenance and optimization scheduling

## 🚀 Quick Start

### Prerequisites

- **macOS 13+** (Apple Silicon recommended for optimal performance)
- **Swift 6.2** (or compatible toolchain via SwiftPM)
- **Disk Space**: Sufficient space for data (`data/`), WAL, and indexes

### Installation

```bash
# Clone the repository
git clone https://github.com/gpicchiarelli/Colibrì-DB.git
cd Colibrì-DB

# Build the project
swift build

# Run the CLI
.build/debug/coldb --config colibridb.conf.json
```

### Interactive Session

```bash
# Start an interactive session
.build/debug/coldb

# Create a table
\create table demo

# Insert data
\insert demo id=1,name=Alice,age=25

# Create an index
\create index idx_demo_name ON demo(name) USING BTree

# Search using the index
\index search demo idx_demo_name Alice

# Query data
\select * FROM demo WHERE name = 'Alice'
```

## ⚙️ Configuration

The `colibridb.conf.json` file controls all database settings:

```json
{
  "dataDir": "./data",
  "maxConnectionsLogical": 1000000,
  "maxConnectionsPhysical": 16,
  "bufferPoolSizeBytes": 1073741824,
  "pageSizeBytes": 8192,
  "walEnabled": true,
  "checksumEnabled": true,
  "cliEnabled": true,
  "metricsEnabled": true,
  "serverEnabled": false,
  "indexImplementation": "Hash",
  "storageEngine": "FileHeap"
}
```

## 📚 Documentation

### 📖 Comprehensive Technical Documentation

Our documentation is organized into multiple sections for different audiences:

#### 🎓 **University Manual** (`docs/`)
- **Part I: Foundations** - Relational principles, SQL algebra, transaction theory
- **Part II: Core Engine** - WAL, Buffer Pool, Heap Storage, B+Tree Indexes, MVCC
- **Part III: Query Processing** - SQL Parser, Logical/Physical Planning, Execution Engine
- **Part IV: Metadata** - Catalog Core, Statistics, Schema Management
- **Part V: Server** - Architecture, Wire Protocol, Operations
- **Part VI: Tooling** - User CLI, Dev CLI, Monitoring & DevOps
- **Part VII: Testing** - Unit Tests, Integration Tests, Benchmarks
- **Part VIII: Future** - Roadmap and Extensions

#### 🔧 **Operational Guides**
- **Configuration Guide** (`docs/Appendices/02-Configurazione.md`)
- **CLI Reference** (`docs/Part-06-Tooling/01-User-CLI.md`)
- **Benchmarking** (`docs/Part-07-Testing/03-Benchmarks.md`)
- **Security** (`SECURITY.md`)

## 🏗️ Architecture

### Repository Structure

```
Colibrì-DB/
├── Sources/
│   ├── ColibriCore/          # Core database engine
│   │   ├── Buffer/           # Buffer pool management
│   │   ├── Catalog/          # System catalog
│   │   ├── Database/         # Database operations
│   │   ├── Index/            # Index implementations
│   │   ├── Storage/          # Storage engine
│   │   ├── Transactions/     # MVCC and locking
│   │   ├── WAL/              # Write-Ahead Logging
│   │   └── ...
│   ├── coldb/                # Administrative CLI
│   ├── coldb-server/         # Network server
│   └── benchmarks/           # Performance testing
├── Tests/                    # Test suite
├── docs/                     # Technical documentation
├── Examples/                 # Usage examples
└── Resources/                # Configuration files
```

### Core Components

- **Storage Engine**: Heap file-based storage with slot directory
- **Buffer Pool**: LRU/Clock eviction with background flushing
- **WAL System**: ARIES-compliant recovery with CRC32 checksums
- **Index Engine**: Pluggable B+Tree, Hash, ART, and LSM implementations
- **Transaction Manager**: MVCC with configurable isolation levels
- **Query Processor**: Volcano iterator with cost-based optimization

## 🧪 Testing & Quality

### Continuous Integration
- **GitHub Actions**: Automated build and test execution
- **CodeQL**: Static analysis and security scanning
- **Swift Testing**: Modern testing framework integration

### Test Coverage
- **Unit Tests**: Core functionality validation
- **Integration Tests**: End-to-end workflow testing
- **Benchmarks**: Performance regression detection
- **Stress Tests**: High-load scenario validation

### Running Tests

```bash
# Run all tests
swift test

# Run specific test categories
swift test --filter WAL
swift test --filter Buffer
swift test --filter BTree

# Run benchmarks
swift run benchmarks --help
```

## 📊 Performance

### Target Performance Metrics
- **WAL Throughput**: 10,000+ operations/second
- **B+Tree Lookups**: 1M+ lookups/second
- **Transaction Throughput**: 1,000+ transactions/second
- **Buffer Pool Hit Rate**: >95%

### Benchmarking

```bash
# WAL performance
swift run benchmarks --wal-throughput --duration 30s

# B+Tree operations
swift run benchmarks --btree-lookups --keys 1000000

# Transaction throughput
swift run benchmarks --transaction-throughput --duration 30s

# Buffer pool efficiency
swift run benchmarks --buffer-hit-rate --workload mixed
```

## 🤝 Contributing

We welcome contributions! Please see our [Contributing Guidelines](CONTRIBUTING.md) and [Code of Conduct](CODE_OF_CONDUCT.md) for details.

### Development Setup

1. Fork the repository
2. Create a feature branch
3. Make your changes
4. Add tests for new functionality
5. Ensure all tests pass
6. Submit a pull request

### Areas for Contribution

- **Core Engine**: Storage, WAL, indexing improvements
- **Query Processing**: Parser enhancements, optimization
- **Testing**: Additional test coverage, benchmarks
- **Documentation**: Technical writing, examples
- **Tooling**: CLI improvements, monitoring tools

## 📈 Roadmap

### Current Status: MVP (Alpha)
- ✅ Core storage engine with WAL
- ✅ B+Tree indexes with recovery
- ✅ Basic MVCC and transaction support
- ✅ Administrative CLI
- ✅ Comprehensive documentation

### Upcoming Features
- **Beta Release**: Multi-user server mode, concurrent transactions
- **Production Release**: Full SQL compliance, advanced monitoring
- **Future**: Distributed architecture, cloud-native deployment

See [ROADMAP.md](ROADMAP.md) for detailed development plans.

## 📄 License

This project is licensed under the **BSD 3-Clause License** - see the [LICENSE](LICENSE) file for details.

## 🙏 Acknowledgments

- **Apple**: For Swift language and development tools
- **Community**: Contributors and early adopters
- **Academic**: Database systems research and literature
- **Open Source**: Inspiration from existing database projects

---

<div align="center">

**Built with ❤️ in Swift for the Apple Ecosystem**

[⭐ Star us on GitHub](https://github.com/gpicchiarelli/Colibrì-DB) • [📖 Read the docs](docs/) • [🐛 Report issues](https://github.com/gpicchiarelli/Colibrì-DB/issues) • [💬 Join discussions](https://github.com/gpicchiarelli/Colibrì-DB/discussions)

</div>
