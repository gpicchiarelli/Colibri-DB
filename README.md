# 🐦 ColibrìDB

> **Un RDBMS sperimentale ad alte prestazioni scritto in Swift 6.2**

[![Build Status](https://img.shields.io/github/actions/workflow/status/gpicchiarelli/Colibrì-DB/ci.yml?branch=main)](https://github.com/gpicchiarelli/Colibrì-DB/actions/workflows/ci.yml)
[![CodeQL](https://img.shields.io/github/actions/workflow/status/gpicchiarelli/Colibrì-DB/codeql.yml?label=CodeQL&branch=main)](https://github.com/gpicchiarelli/Colibrì-DB/actions/workflows/codeql.yml)
![Swift](https://img.shields.io/badge/Swift-6.2-orange.svg)
![SwiftPM](https://img.shields.io/badge/SwiftPM-compatible-brightgreen.svg)
![Platform](https://img.shields.io/badge/platform-macOS%2013%2B-lightgrey.svg)
![License: BSD-3-Clause](https://img.shields.io/badge/License-BSD_3--Clause-blue.svg)
![Stars](https://img.shields.io/github/stars/gpicchiarelli/Colibrì-DB?style=social)
![Issues](https://img.shields.io/github/issues/gpicchiarelli/Colibrì-DB)
![PRs](https://img.shields.io/github/issues-pr/gpicchiarelli/Colibrì-DB)
![Last commit](https://img.shields.io/github/last-commit/gpicchiarelli/Colibrì-DB)
![Contributors](https://img.shields.io/github/contributors/gpicchiarelli/Colibrì-DB)
![PRs Welcome](https://img.shields.io/badge/PRs-welcome-brightgreen.svg)

**ColibrìDB** è un RDBMS sperimentale scritto in Swift 6.2 pensato per gestire milioni di connessioni logiche, ottimizzato per macOS e Apple Silicon. Il progetto punta a un'architettura modulare: motore heap su disco con WAL, MVCC, indici pluggabili e CLI amministrativa `coldb`.

## ✨ Caratteristiche Principali

### 🗄️ **Storage & Buffering**
- **Heap File Storage**: File heap paginati con slot directory e Free Space Map persistente
- **Compattazione Online**: Riorganizzazione dati in tempo reale senza downtime
- **Buffer Pool LRU/Clock**: Flusher in background con quote per namespace ed eviction intelligente
- **Ottimizzato Apple Silicon**: Performance ARM64 native con accelerazione CRC32

### 🔒 **Durabilità Enterprise**
- **WAL v2**: Record tipizzati con checksum CRC32 e recovery ARIES-like
- **Sistema Checkpoint**: Recovery efficiente con gestione Dirty Page Table
- **Transaction Logging**: Supporto completo UNDO/REDO per consistenza dati
- **Index Recovery**: Replay indici B+Tree da WAL durante il recovery

### 🚀 **Indicizzazione ad Alte Prestazioni**
- **B+Tree Persistente**: Su disco con supporto checkpoint e operazioni bulk
- **Tipi di Indici Pluggabili**: Hash, ART (Adaptive Radix Tree), SkipList, Fractal Tree, LSM
- **Validazione Profonda**: Controlli di integrità completi e manutenzione online
- **Memory-Efficient**: Ottimizzato per dataset grandi con caching intelligente

### ⚡ **Controllo Concorrenza Moderno**
- **MVCC**: Multi-Version Concurrency Control con livelli di isolamento configurabili
- **Lock Manager**: Rilevamento deadlock, gestione timeout e locking granulare
- **Supporto 2PC**: Two-Phase Commit per consistenza transazioni distribuite
- **Snapshot Isolation**: Viste di lettura consistenti per query complesse

### 🧠 **Elaborazione Query Intelligente**
- **Volcano Iterator**: Planner cost-based con predicate pushdown
- **Operatori Avanzati**: Scan, filter, project, sort e operazioni join
- **Viste Materializzate**: Risultati query cached per performance migliorate
- **SQL Parser**: Compatibilità SQL completa con sintassi moderna

### 🛠️ **Eccellenza Operativa**
- **CLI Amministrativa**: Gestione completa database con tool `coldb`
- **Import/Export CSV**: Operazioni bulk con validazione formato
- **Metriche Prometheus**: Monitoring e osservabilità pronti per produzione
- **Policy Engine**: Manutenzione e ottimizzazione automatizzate

## 🚀 Avvio Rapido

### Prerequisiti

- **macOS 13+** (Apple Silicon consigliato per performance ottimali)
- **Swift 6.2** (o toolchain compatibile via SwiftPM)
- **Spazio su disco**: Sufficiente per dati (`data/`), WAL e indici

### Installazione

```bash
# Clona il repository
git clone https://github.com/gpicchiarelli/Colibrì-DB.git
cd Colibrì-DB

# Compila il progetto
swift build

# Esegui la CLI
.build/debug/coldb --config colibridb.conf.json
```

### Sessione Interattiva

```bash
# Avvia una sessione interattiva
.build/debug/coldb

# Crea una tabella
\create table demo

# Inserisci dati
\insert demo id=1,name=Alice,age=25

# Crea un indice
\create index idx_demo_name ON demo(name) USING BTree

# Cerca usando l'indice
\index search demo idx_demo_name Alice

# Interroga i dati
\select * FROM demo WHERE name = 'Alice'
```

## ⚙️ Configurazione

Il file `colibridb.conf.json` controlla tutte le impostazioni del database:

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

## 📚 Documentazione

### 📖 Manuale Tecnico Completo

La documentazione è organizzata in più sezioni per diversi tipi di utenti:

#### 🎓 **Manuale Universitario** (`docs/`)
- **Parte I: Fondamenti** - Principi relazionali, algebra SQL, teoria delle transazioni
- **Parte II: Motore Core** - WAL, Buffer Pool, Heap Storage, Indici B+Tree, MVCC
- **Parte III: Elaborazione Query** - SQL Parser, Planning Logico/Fisico, Execution Engine
- **Parte IV: Metadati** - Catalog Core, Statistiche, Gestione Schema
- **Parte V: Server** - Architettura, Wire Protocol, Operazioni
- **Parte VI: Strumenti** - User CLI, Dev CLI, Monitoring & DevOps
- **Parte VII: Testing** - Unit Tests, Integration Tests, Benchmarks
- **Parte VIII: Futuro** - Roadmap ed Estensioni

#### 🔧 **Guide Operative**
- **Guida Configurazione** (`docs/Appendices/02-Configurazione.md`)
- **Riferimento CLI** (`docs/Part-06-Tooling/01-User-CLI.md`)
- **Benchmarking** (`docs/Part-07-Testing/03-Benchmarks.md`)
- **Sicurezza** (`SECURITY.md`)

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
