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

## 🏗️ Architettura

### Struttura del Repository

```
Colibrì-DB/
├── Sources/
│   ├── ColibriCore/          # Motore database core
│   │   ├── Buffer/           # Gestione buffer pool
│   │   ├── Catalog/          # Catalogo di sistema
│   │   ├── Database/         # Operazioni database
│   │   ├── Index/            # Implementazioni indici
│   │   ├── Storage/          # Motore storage
│   │   ├── Transactions/     # MVCC e locking
│   │   ├── WAL/              # Write-Ahead Logging
│   │   └── ...
│   ├── coldb/                # CLI amministrativa
│   ├── coldb-server/         # Server di rete
│   └── benchmarks/           # Test di performance
├── Tests/                    # Suite di test
├── docs/                     # Documentazione tecnica
├── Examples/                 # Esempi di utilizzo
└── Resources/                # File di configurazione
```

### Componenti Core

- **Storage Engine**: Storage basato su file heap con slot directory
- **Buffer Pool**: Eviction LRU/Clock con flush in background
- **Sistema WAL**: Recovery ARIES-compliant con checksum CRC32
- **Motore Indici**: Implementazioni pluggabili B+Tree, Hash, ART e LSM
- **Transaction Manager**: MVCC con livelli di isolamento configurabili
- **Query Processor**: Iterator Volcano con ottimizzazione cost-based

## 🧪 Testing e Qualità

### Continuous Integration
- **GitHub Actions**: Esecuzione automatica build e test
- **CodeQL**: Analisi statica e security scanning
- **Swift Testing**: Integrazione framework di test moderno

### Copertura Test
- **Unit Tests**: Validazione funzionalità core
- **Integration Tests**: Test workflow end-to-end
- **Benchmarks**: Rilevamento regressioni performance
- **Stress Tests**: Validazione scenari ad alto carico

### Esecuzione Test

```bash
# Esegui tutti i test
swift test

# Esegui categorie specifiche di test
swift test --filter WAL
swift test --filter Buffer
swift test --filter BTree

# Esegui benchmark
swift run benchmarks --help
```

## 📊 Performance

### Metriche Performance Target
- **WAL Throughput**: 10,000+ operazioni/secondo
- **B+Tree Lookups**: 1M+ lookups/secondo
- **Transaction Throughput**: 1,000+ transazioni/secondo
- **Buffer Pool Hit Rate**: >95%

### Benchmarking

```bash
# Performance WAL
swift run benchmarks --wal-throughput --duration 30s

# Operazioni B+Tree
swift run benchmarks --btree-lookups --keys 1000000

# Throughput transazioni
swift run benchmarks --transaction-throughput --duration 30s

# Efficienza buffer pool
swift run benchmarks --buffer-hit-rate --workload mixed
```

## 🤝 Contribuire

Accogliamo i contributi! Consulta le nostre [Linee Guida per i Contributi](CONTRIBUTING.md) e il [Codice di Condotta](CODE_OF_CONDUCT.md) per i dettagli.

### Setup di Sviluppo

1. Fork del repository
2. Crea un branch per la feature
3. Apporta le modifiche
4. Aggiungi test per le nuove funzionalità
5. Assicurati che tutti i test passino
6. Invia una pull request

### Aree per i Contributi

- **Motore Core**: Miglioramenti storage, WAL, indicizzazione
- **Elaborazione Query**: Miglioramenti parser, ottimizzazione
- **Testing**: Copertura test aggiuntiva, benchmark
- **Documentazione**: Scrittura tecnica, esempi
- **Strumenti**: Miglioramenti CLI, strumenti di monitoring

## 📈 Roadmap

### Stato Attuale: MVP (Alpha)
- ✅ Motore storage core con WAL
- ✅ Indici B+Tree con recovery
- ✅ Supporto MVCC e transazioni base
- ✅ CLI amministrativa
- ✅ Documentazione completa

### Funzionalità in Arrivo
- **Release Beta**: Modalità server multi-utente, transazioni concorrenti
- **Release Produzione**: Conformità SQL completa, monitoring avanzato
- **Futuro**: Architettura distribuita, deployment cloud-native

Vedi [ROADMAP.md](ROADMAP.md) per i piani di sviluppo dettagliati.

## 📄 Licenza

Questo progetto è licenziato sotto la **Licenza BSD 3-Clause** - vedi il file [LICENSE](LICENSE) per i dettagli.

## 🙏 Ringraziamenti

- **Apple**: Per il linguaggio Swift e gli strumenti di sviluppo
- **Comunità**: Contributori e early adopter
- **Accademia**: Ricerca e letteratura sui sistemi database
- **Open Source**: Ispirazione da progetti database esistenti

---

<div align="center">

**Costruito con ❤️ in Swift per l'Ecosistema Apple**

[⭐ Dacci una stella su GitHub](https://github.com/gpicchiarelli/Colibrì-DB) • [📖 Leggi la documentazione](docs/) • [🐛 Segnala problemi](https://github.com/gpicchiarelli/Colibrì-DB/issues) • [💬 Partecipa alle discussioni](https://github.com/gpicchiarelli/Colibrì-DB/discussions)

</div>
