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

Caratteristiche principali
-------------------------
- **Storage & Buffering**: heap file paginati con slot directory, Free Space Map persistente, compattazione online e buffer pool LRU/Clock con flusher in background e quote per namespace.
- **Durabilità**: WAL v2 con record tipizzati, CRC32, checkpoint, ARIES-like CLR per UNDO e gestione Dirty Page Table. Supporto a replay DB + WAL degli indici B+Tree.
- **Indici**: persistente B+Tree con checkpoint, validazioni profonde, bulk-build e compattazione; indice `AnyStringIndex` con Hash, ART, SkipList, Fractal tree e LSM in-memory.
- **Transazioni & MVCC**: livelli di isolamento configurabili, lock manager con deadlock detection/timeout, snapshot MVCC, vacuum e supporto 2PC (prepare/commit/abort).
- **Planner/Executor**: iteratore Volcano con planner cost-based, operatori scan/filter/project/sort/join, predicate pushdown e caching di viste materializzate.
- **CLI operativa**: gestione tabelle, indici, import/export CSV, buffer pool, politiche di manutenzione, simulatore di ottimizzazione e metriche formato Prometheus.
- **Catalogo & Policy**: cataloghi sistema/indici, statistiche di frammentazione, policy di compattazione programmata e simulatori di clustering.

Requisiti
---------
- macOS 13+ (Apple Silicon consigliato)
- Swift 6.2 (o toolchain compatibile via SwiftPM)
- Spazio su disco per dati (`data/`), WAL e indici

Avvio rapido
------------
```
swift build
.build/debug/coldb --config colibridb.conf.json
```
Per provare una sessione interattiva:
```
\\create table demo
\\insert demo id=1,name=Alice
\\create index idx_demo_name ON demo(name) USING BTree
\\index search demo idx_demo_name Alice
```

Configurazione
--------------
Il file `colibridb.conf.json` controlla directory dati, dimensioni delle pagine, buffer pool, politiche di compattazione, livelli di isolamento e backend di indicizzazione. La struttura completa è descritta in `docs/configuration.md`.

Documentazione
--------------
La documentazione tecnica è allineata e organizzata in `docs/` e il libro degli internals è in `Libro/`:
- `Libro/` — libro in markdown sugli internals (architettura, storage, MVCC, WAL, indici, server, CLI)
- `docs/index.md` — mappa dei documenti e percorsi di lettura
- `docs/overview.md` — visione generale e stato MVP
- `docs/architecture.md` — panoramica a livelli e flussi
- `docs/modules-*.md` — approfondimenti su storage, buffer, indici, WAL, concorrenza
- `docs/cli.md` e `docs/policies.md` — comandi operativi e automazioni
- `docs/security.md`, `docs/apple-silicon.md`, `docs/appendices.md` — aspetti trasversali, ottimizzazioni e materiali di supporto
- `docs/dimensional-limits.md` — vincoli dimensionali (pagine, slot, WAL, buffer) e valori di default
- `docs/benchmarking.md` — guida ai benchmark micro/macro e al target unificato `benchmarks`

Struttura del repository
------------------------
- `Sources/ColibriCore/` — core engine (storage, WAL, MVCC, indici, policy, util)
- `Sources/coldb/` — CLI amministrativa
- `Sources/coldb-server/` — server e wire protocol
- `Sources/benchmarks/` — harness `benchmarks` unificato (scenari tematici e output leggibile)
- `Tests/` — suite di test SwiftPM
- `docs/` — documentazione tecnica
- `Libro/` — libro degli internals in markdown navigabile su GitHub
- `data/` — dati runtime (ignorati dal VCS)

CI e qualità
------------
- GitHub Actions esegue build e test (`.github/workflows/ci.yml`).
- Analisi statica con CodeQL (`.github/workflows/codeql.yml`).

Contribuire
-----------
Consulta `CONTRIBUTING.md`, `CODE_OF_CONDUCT.md` e la roadmap (`docs/roadmap.md`) prima di aprire PR. Strutture dati e protocolli sono progettati per essere estesi: vedere `docs/api-extendibility.md`.

Licenza
-------
BSD 3-Clause. Tutti i contributi ricadono sotto la licenza in `LICENSE`.
