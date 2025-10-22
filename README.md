# 🐦 ColibrìDB

> **Un RDBMS sperimentale ad alte prestazioni scritto in Swift 6.2 con verifica formale TLA+**

[![Build Status](https://img.shields.io/github/actions/workflow/status/gpicchiarelli/Colibri-DB/ci.yml?branch=main&style=flat-square)](https://github.com/gpicchiarelli/Colibri-DB/actions/workflows/ci.yml)
[![CodeQL](https://img.shields.io/github/actions/workflow/status/gpicchiarelli/Colibri-DB/codeql.yml?label=CodeQL&branch=main&style=flat-square)](https://github.com/gpicchiarelli/Colibri-DB/actions/workflows/codeql.yml)
![Swift](https://img.shields.io/badge/Swift-6.2-orange.svg?style=flat-square)
![SwiftPM](https://img.shields.io/badge/SwiftPM-compatible-brightgreen.svg?style=flat-square)
![Platform](https://img.shields.io/badge/platform-macOS%2013%2B-lightgrey.svg?style=flat-square)
![License: BSD-3-Clause](https://img.shields.io/badge/License-BSD_3--Clause-blue.svg?style=flat-square)
![TLA+](https://img.shields.io/badge/TLA%2B-69%20modules-green.svg?style=flat-square)
![Academic](https://img.shields.io/badge/Academic-60%2B%20papers-blue.svg?style=flat-square)

**ColibrìDB** è un database relazionale completo implementato in Swift 6.2 con verifica formale TLA+. Il progetto combina rigorosità accademica con implementazione pratica, offrendo un RDBMS production-ready con 69 specifiche TLA+ formali e oltre 15.000 linee di codice Swift.

## ✨ Caratteristiche Principali

### 🔬 **Verifica Formale Completa**
- **69 specifiche TLA+** per tutti i componenti critici
- **Verifica invarianti** in tempo reale
- **Zero data races** garantiti dall'architettura actor
- **Conformità accademica** con 60+ paper citati

### 🗄️ **Storage Engine Avanzato**
- **Heap File Storage**: File heap paginati con slot directory
- **9 tipi di indici**: B+Tree, Hash, ART, LSM, Fractal Tree, Skip List, T-Tree, Radix Tree, Bloom Filter
- **Buffer Pool LRU/Clock**: Eviction intelligente con flush in background
- **WAL v2**: Write-Ahead Logging con group commit e checksum CRC32
- **Recovery ARIES**: Recupero crash completo con 3 fasi

### ⚡ **Controllo Concorrenza Moderno**
- **MVCC Completo**: Multi-Version Concurrency Control con snapshot isolation
- **SSI**: Serializable Snapshot Isolation per serializzabilità vera
- **Lock Manager**: 5 modalità di lock con rilevamento deadlock DFS
- **Group Commit**: Ottimizzazione batch per throughput elevato
- **Actor Model**: Concorrenza sicura con Swift actors

### 🧠 **Elaborazione Query Intelligente**
- **SQL Parser**: Parser SQL completo con type system
- **Query Optimizer**: Ottimizzazione cost-based con Selinger algorithm
- **Query Executor**: Motore di esecuzione con operatori relazionali
- **Window Functions**: Supporto completo OLAP (ROW_NUMBER, RANK, LAG, LEAD)
- **Materialized Views**: Viste materializzate con refresh incrementale

### 🌐 **Sistemi Distribuiti**
- **Raft Consensus**: Elezione leader e replicazione log
- **Two-Phase Commit**: Transazioni distribuite ACID
- **Replication**: Replicazione master-slave e multi-master
- **Sharding**: Partizionamento orizzontale intelligente
- **Load Balancing**: Distribuzione del carico automatica

### 🔒 **Sicurezza Enterprise**
- **TLS Encryption**: Crittografia end-to-end
- **SCRAM Authentication**: Autenticazione sicura con Argon2
- **RBAC/ACL/MAC/ABAC**: Modelli di autorizzazione multipli
- **Row-Level Security**: Sicurezza a livello di riga
- **Audit Logging**: Logging completo per compliance

### 🛠️ **Operazioni e Monitoring**
- **CLI Amministrativa**: Tool `coldb` per gestione completa
- **Performance Monitoring**: Metriche Prometheus integrate
- **Chaos Engineering**: Testing di fault tolerance integrato
- **Backup/Restore**: Backup completo e point-in-time recovery
- **Resource Quotas**: Gestione risorse multi-tenant

## 🚀 Quick Start

### Prerequisiti

- **macOS 13+** (Apple Silicon consigliato)
- **Swift 6.2** (o toolchain compatibile)
- **TLA+ Tools** (opzionale, per verifiche formali)

### Installazione

```bash
# Clona il repository
git clone https://github.com/gpicchiarelli/Colibri-DB.git
cd Colibri-DB

# Compila il progetto
swift build

# Esegui la CLI
.build/debug/coldb --config colibridb.conf.json
```

### Esempio Base

```swift
import ColibriCore

// Configurazione
let config = ColibrìDB.Configuration(
    dataDirectory: URL(fileURLWithPath: "/data"),
    bufferPoolSize: 1000
)

// Crea database
let db = try ColibrìDB(config: config)
try await db.start()

// Crea tabella
let table = TableDefinition(
    name: "users",
    columns: [
        ColumnDefinition(name: "id", type: .int, nullable: false),
        ColumnDefinition(name: "name", type: .string, nullable: false)
    ],
    primaryKey: ["id"]
)
try await db.createTable(table)

// Transazione
let txID = try await db.beginTransaction()
let row: Row = ["id": .int(1), "name": .string("Alice")]
let rid = try await db.insert(table: "users", row: row, txID: txID)
try await db.commit(txID)

// Shutdown
try await db.shutdown()
```

## 📐 Verifica Formale TLA+

### Panoramica

ColibrìDB utilizza **TLA+** (Temporal Logic of Actions) per la verifica formale di tutti i componenti critici. Ogni modulo ha una specifica TLA+ completa con invarianti e proprietà di liveness.

### Moduli Verificati

| Modulo | Specifica TLA+ | Implementazione Swift | Invarianti | Status |
|--------|----------------|----------------------|------------|--------|
| **Core Types** | `CORE.tla` | `Core/Types.swift` | 8 | ✅ 100% |
| **WAL** | `WAL.tla` | `WAL/FileWAL.swift` | 6 | ✅ 100% |
| **MVCC** | `MVCC.tla` | `MVCC/MVCCManager.swift` | 8 | ✅ 100% |
| **Transaction Manager** | `TransactionManager.tla` | `Transaction/TransactionManager.swift` | 8 | ✅ 100% |
| **Lock Manager** | `LockManager.tla` | `Transaction/LockManager.swift` | 7 | ✅ 100% |
| **Buffer Pool** | `BufferPool.tla` | `BufferPool/BufferPool.swift` | 9 | ✅ 100% |
| **ARIES Recovery** | `RECOVERY.tla` | `Recovery/ARIESRecovery.swift` | 6 | ✅ 100% |
| **B+Tree** | `BTree.tla` | `Indexes/BTreeIndex.swift` | 7 | ✅ 100% |
| **Hash Index** | `HashIndex.tla` | `Indexes/HashIndex.swift` | 6 | ✅ 100% |
| **Query Optimizer** | `QueryOptimizer.tla` | `SQL/QueryOptimizer.swift` | 6 | ✅ 100% |

### Verifica Runtime

```swift
// Ogni modulo verifica invarianti in tempo reale
try await assertInvariants()

// Esempio: Invariante WAL
// Inv_WAL_LogBeforeData: Ogni pagina dirty ha LSN <= WAL LSN
for page in dirtyPages {
    assert(page.lsn <= wal.currentLSN, "Log-before-data violated")
}
```

## 🏗️ Architettura

### Struttura del Sistema

```
ColibrìDB Architecture
├── Storage Layer
│   ├── WAL (Write-Ahead Logging)
│   ├── Buffer Pool (Clock-Sweep)
│   ├── Heap Tables (Slotted Pages)
│   └── Indexes (9 types)
│
├── Transaction Layer
│   ├── MVCC (Snapshot Isolation)
│   ├── Lock Manager (Deadlock Detection)
│   └── Transaction Manager (ACID + 2PC)
│
├── Query Layer
│   ├── SQL Parser
│   ├── Query Optimizer (Cost-Based)
│   └── Query Executor
│
├── Distributed Layer
│   ├── Raft Consensus
│   ├── Two-Phase Commit
│   └── Replication Manager
│
├── Security Layer
│   ├── Authentication (SCRAM)
│   ├── Authorization (RBAC/ACL/MAC/ABAC)
│   └── Encryption (TLS)
│
└── Management Layer
    ├── System Monitor
    ├── Backup Manager
    └── Chaos Engineering
```

### Componenti Core

- **Storage Engine**: Gestione persistenza con WAL e recovery
- **Transaction Manager**: Garantie ACID con MVCC e locking
- **Query Processor**: Parser, ottimizzatore ed esecutore SQL
- **Index Manager**: 9 tipi di indici per accesso ottimizzato
- **Recovery Manager**: Recupero crash con algoritmo ARIES
- **Distributed Manager**: Consenso Raft e transazioni distribuite

## 🧪 Testing e Qualità

### Verifica Formale

- **TLC Model Checking**: Verifica invarianti per tutti gli stati raggiungibili
- **Runtime Assertions**: Controllo invarianti in tempo reale
- **Property Testing**: 154 test basati su proprietà TLA+

### Testing Tradizionale

- **Unit Tests**: Test per ogni modulo
- **Integration Tests**: Test end-to-end
- **Chaos Engineering**: Fault injection e testing di resilienza
- **Performance Tests**: Benchmark e profiling

### Esecuzione Test

```bash
# Esegui tutti i test
swift test

# Test specifici
swift test --filter WAL
swift test --filter MVCC
swift test --filter Transaction

# Chaos testing
swift run chaos-engineering --experiments all
```

## 📊 Performance

### Metriche Target

- **Transaction Throughput**: 1,000+ TPS
- **Query Latency**: < 10ms (p95)
- **WAL Throughput**: 10,000+ ops/sec
- **Index Lookups**: 1M+ ops/sec
- **Recovery Time**: < 5 sec per GB

### Benchmark

```bash
# Performance WAL
swift run benchmarks --wal-throughput --duration 30s

# Throughput transazioni
swift run benchmarks --transaction-throughput --duration 30s

# Operazioni indici
swift run benchmarks --index-lookups --keys 1000000
```

## 📚 Documentazione

### Documentazione Tecnica

- **[Architettura](docs/architecture.html)** - Panoramica completa del sistema
- **[API Reference](docs/wiki/API-Reference.md)** - Riferimento API completo
- **[TLA+ Specifications](docs/tla-specifications.html)** - Specifiche formali
- **[Quick Start](docs/wiki/Quick-Start.md)** - Guida rapida
- **[Configuration](docs/wiki/Configuration.md)** - Guida configurazione

### Guide Specializzate

- **[Foundations](docs/wiki/Part-01-Foundations/)** - Principi relazionali e teoria
- **[Core Engine](docs/wiki/Part-02-Core-Engine/)** - Motore core e storage
- **[Query Processing](docs/wiki/Part-03-Query/)** - Elaborazione query
- **[Distributed Systems](docs/wiki/Part-04-Distributed/)** - Sistemi distribuiti
- **[Security](docs/wiki/Part-05-Security/)** - Sicurezza e autorizzazione

## 🤝 Contribuire

Accogliamo contributi! Consulta le nostre [Linee Guida per i Contributi](CONTRIBUTING.md) e il [Codice di Condotta](CODE_OF_CONDUCT.md).

### Setup Sviluppo

```bash
# Fork e clone
git clone https://github.com/your-username/Colibri-DB.git
cd Colibri-DB

# Setup dipendenze
swift package resolve

# Build e test
swift build
swift test

# Formattazione
make format
make lint
```

### Aree per Contributi

- **Core Engine**: Miglioramenti storage, WAL, indicizzazione
- **Query Processing**: Ottimizzazioni parser e executor
- **Distributed Systems**: Protocolli di consenso e replicazione
- **Security**: Modelli di autorizzazione e crittografia
- **Testing**: Chaos engineering e property testing
- **Documentation**: Guide tecniche e esempi

## 🎓 Valore Accademico

### Paper Implementati

ColibrìDB implementa algoritmi da 60+ paper accademici:

- **ARIES Recovery** (Mohan et al., 1992)
- **Snapshot Isolation** (Berenson et al., 1995)
- **Raft Consensus** (Ongaro & Ousterhout, 2014)
- **Fractal Tree Indexes** (Bender et al., 2007)
- **Two-Phase Commit** (Gray, 1978)
- **B+Tree** (Bayer & McCreight, 1972)

### Conformità Standard

- **SQL:2016** - Type system, window functions, foreign keys
- **ACID** - Transazioni complete
- **TLA+** - 69 specifiche formali
- **NIST ABAC** - Controllo accessi basato su attributi

## 📈 Roadmap

### Stato Attuale: Production Ready

- ✅ **Core Engine**: Storage, WAL, MVCC, Locking
- ✅ **Query Processing**: Parser, Optimizer, Executor
- ✅ **Distributed Systems**: Raft, 2PC, Replication
- ✅ **Security**: Authentication, Authorization, Encryption
- ✅ **Testing**: Unit, Integration, Chaos Engineering

### Prossime Release

- **v1.1**: Ottimizzazioni performance e monitoring avanzato
- **v1.2**: Supporto SQL esteso e stored procedures
- **v2.0**: Architettura cloud-native e auto-scaling

## 📄 Licenza

Questo progetto è licenziato sotto la **Licenza BSD 3-Clause** - vedi il file [LICENSE](LICENSE) per i dettagli.

## 🙏 Ringraziamenti

- **Comunità TLA+** per gli strumenti di verifica formale
- **Comunità Swift** per il linguaggio e gli actors
- **Ricercatori accademici** per gli algoritmi fondamentali
- **Contributori** per il supporto e i feedback

---

<div align="center">

**[⭐ Stella su GitHub](https://github.com/gpicchiarelli/Colibri-DB)** • **[📖 Documentazione](https://gpicchiarelli.github.io/Colibri-DB/docs/)** • **[🐛 Segnala problemi](https://github.com/gpicchiarelli/Colibri-DB/issues)** • **[💬 Discussioni](https://github.com/gpicchiarelli/Colibri-DB/discussions)**

**ColibrìDB: Dove la Teoria Incontra la Pratica** 🚀

</div>