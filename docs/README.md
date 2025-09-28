---
layout: page
title: Documentazione Colibrì DB
description: Documentazione tecnica completa di Colibrì DB
---

# 🐦 Colibrì DB Documentation

<div align="center">

[![Build Status](https://img.shields.io/github/actions/workflow/status/gpicchiarelli/Colibri-DB/ci.yml?branch=main&style=flat-square)](https://github.com/gpicchiarelli/Colibri-DB/actions/workflows/ci.yml)
[![CodeQL](https://img.shields.io/github/actions/workflow/status/gpicchiarelli/Colibri-DB/codeql.yml?label=CodeQL&branch=main&style=flat-square)](https://github.com/gpicchiarelli/Colibri-DB/actions/workflows/codeql.yml)
![Swift](https://img.shields.io/badge/Swift-6.2-orange.svg?style=flat-square)
![SwiftPM](https://img.shields.io/badge/SwiftPM-compatible-brightgreen.svg?style=flat-square)
![Platform](https://img.shields.io/badge/platform-macOS%2013%2B-lightgrey.svg?style=flat-square)
![License: BSD-3-Clause](https://img.shields.io/badge/License-BSD_3--Clause-blue.svg?style=flat-square)

**Un RDBMS sperimentale ad alte prestazioni scritto in Swift 6.2**

[🏠 Home](https://gpicchiarelli.github.io/Colibri-DB/) • [📖 Docs](https://gpicchiarelli.github.io/Colibri-DB/docs/) • [📚 Wiki](https://gpicchiarelli.github.io/Colibri-DB/docs/wiki/) • [🚀 Quick Start](#-quick-start) • [📚 Manuale Tecnico](#-manuale-tecnico) • [🔧 API Reference](#-api-reference)

</div>

---

## 🎯 Panoramica

**Colibrì DB** è un RDBMS sperimentale scritto in Swift 6.2 pensato per gestire milioni di connessioni logiche, ottimizzato per macOS e Apple Silicon. Il progetto punta a un'architettura modulare: motore heap su disco con WAL, MVCC, indici pluggabili e CLI amministrativa `coldb`.

### ✨ Caratteristiche Principali

<table>
<tr>
<td width="50%">

#### 🗄️ **Storage & Buffering**
- **Heap File Storage**: File heap paginati con slot directory
- **Compattazione Online**: Riorganizzazione dati in tempo reale
- **Buffer Pool LRU/Clock**: Flusher in background intelligente
- **Ottimizzato Apple Silicon**: Performance ARM64 native

#### 🔒 **Durabilità Enterprise**
- **WAL v2**: Record tipizzati con checksum CRC32
- **Sistema Checkpoint**: Recovery efficiente ARIES-like
- **Transaction Logging**: Supporto completo UNDO/REDO
- **Index Recovery**: Replay indici B+Tree da WAL

</td>
<td width="50%">

#### 🚀 **Indicizzazione Avanzata**
- **B+Tree Persistente**: Su disco con supporto checkpoint
- **Tipi Pluggabili**: Hash, ART, SkipList, LSM
- **Validazione Profonda**: Controlli di integrità completi
- **Memory-Efficient**: Ottimizzato per dataset grandi

#### ⚡ **Controllo Concorrenza**
- **MVCC**: Multi-Version Concurrency Control
- **Lock Manager**: Rilevamento deadlock e timeout
- **Supporto 2PC**: Two-Phase Commit distribuito
- **Snapshot Isolation**: Viste di lettura consistenti

</td>
</tr>
</table>

## 🚀 Quick Start

### Prerequisiti

- **macOS 13+** (Apple Silicon consigliato)
- **Swift 6.2** (o toolchain compatibile)
- **Spazio su disco**: Sufficiente per dati, WAL e indici

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

### Prima Sessione

```bash
# Avvia una sessione interattiva
.build/debug/coldb

# Crea una tabella
\create table demo

# Inserisci dati
\insert demo id=1,name=Alice,age=25

# Crea un indice
\create index idx_demo_name ON demo(name) USING BTree

# Interroga i dati
\select * FROM demo WHERE name = 'Alice'
```

## 📚 Manuale Tecnico

### 🎓 **Manuale**) - Struttura Completa

La documentazione è organizzata in sezioni progressive per diversi livelli di competenza:

#### **Parte I: Fondamenti**) - Teoria e Principi
- [**00-Guida-Alla-Lettura**]({{ site.baseurl }}/wiki/Part-01-Foundations/00-Guida-Alla-Lettura)) - Come navigare la documentazione
- [**01-Relational-Principles**]({{ site.baseurl }}/wiki/Part-01-Foundations/01-Relational-Principles)) - Principi relazionali e algebra
- [**02-Algebra-SQL**]({{ site.baseurl }}/wiki/Part-01-Foundations/02-Algebra-SQL)) - Algebra relazionale e SQL
- [**03-Transactions-Theory**]({{ site.baseurl }}/wiki/Part-01-Foundations/03-Transactions-Theory)) - Teoria delle transazioni
- [**04-Storage-Principles**]({{ site.baseurl }}/wiki/Part-01-Foundations/04-Storage-Principles)) - Principi di storage e persistenza

#### **Parte II: Motore Core**) - Architettura Interna
- [**00-Introduzione**]({{ site.baseurl }}/wiki/Part-02-Core-Engine/00-Introduzione)) - Panoramica del motore core
- [**01-WAL-and-Recovery**]({{ site.baseurl }}/wiki/Part-02-Core-Engine/01-WAL-and-Recovery)) - Write-Ahead Logging e recovery
- [**02-BufferPool**]({{ site.baseurl }}/wiki/Part-02-Core-Engine/02-BufferPool)) - Gestione buffer pool e caching
- [**03-Heap-Storage**]({{ site.baseurl }}/wiki/Part-02-Core-Engine/03-Heap-Storage)) - Storage engine e heap files
- [**04-BTree-Indexes**]({{ site.baseurl }}/wiki/Part-02-Core-Engine/04-BTree-Indexes)) - Indici B+Tree e strutture dati
- [**05-MVCC-Concurrency**]({{ site.baseurl }}/wiki/Part-02-Core-Engine/05-MVCC-Concurrency)) - Controllo concorrenza MVCC

#### **Parte III: Elaborazione Query**) - Pipeline di Esecuzione
- [**00-Introduzione**]({{ site.baseurl }}/wiki/Part-03-Query/00-Introduzione)) - Panoramica del query processor
- [**01-SQL-Parser**]({{ site.baseurl }}/wiki/Part-03-Query/01-SQL-Parser)) - Parser SQL e AST
- [**02-Logical-Planning**]({{ site.baseurl }}/wiki/Part-03-Query/02-Logical-Planning)) - Pianificazione logica
- [**03-Physical-Planning**]({{ site.baseurl }}/wiki/Part-03-Query/03-Physical-Planning)) - Pianificazione fisica
- [**04-Execution-Engine**]({{ site.baseurl }}/wiki/Part-03-Query/04-Execution-Engine)) - Motore di esecuzione
- [**05-Advanced-Features**]({{ site.baseurl }}/wiki/Part-03-Query/05-Advanced-Features)) - Funzionalità avanzate

#### **Parte IV: Metadati**) - Catalogo e Statistiche
- [**00-Introduzione**]({{ site.baseurl }}/wiki/Part-04-Metadata/00-Introduzione) - Panoramica del sistema metadati
- [**01-CatalogCore**]({{ site.baseurl }}/wiki/Part-04-Metadata/01-CatalogCore) - Catalogo di sistema core
- [**02-CatalogManager**]({{ site.baseurl }}/wiki/Part-04-Metadata/02-CatalogManager) - Gestione catalogo
- [**03-Statistics**]({{ site.baseurl }}/wiki/Part-04-Metadata/03-Statistics) - Statistiche e ottimizzazione

#### **Parte V: Server**) - Architettura di Rete
- [**00-Introduzione**]({{ site.baseurl }}/wiki/Part-05-Server/00-Introduzione) - Panoramica del server
- [**01-ServerArchitecture**]({{ site.baseurl }}/wiki/Part-05-Server/01-ServerArchitecture) - Architettura server
- [**02-Wire-Protocol**]({{ site.baseurl }}/wiki/Part-05-Server/02-Wire-Protocol) - Protocollo di comunicazione
- [**03-ServerOperations**]({{ site.baseurl }}/wiki/Part-05-Server/03-ServerOperations) - Operazioni server

#### **Parte VI: Strumenti**) - CLI e DevOps
- [**00-Introduzione**]({{ site.baseurl }}/wiki/Part-06-Tooling/00-Introduzione) - Panoramica degli strumenti
- [**01-User-CLI**]({{ site.baseurl }}/wiki/Part-06-Tooling/01-User-CLI) - CLI utente e amministrativa
- [**02-Dev-CLI**]({{ site.baseurl }}/wiki/Part-06-Tooling/02-Dev-CLI) - CLI per sviluppatori
- [**03-Monitoring-DevOps**]({{ site.baseurl }}/wiki/Part-06-Tooling/03-Monitoring-DevOps) - Monitoring e DevOps

#### **Parte VII: Testing**) - Qualità e Performance
- [**00-Introduzione**]({{ site.baseurl }}/wiki/Part-07-Testing/00-Introduzione) - Strategia di testing
- [**01-Unit-Tests**]({{ site.baseurl }}/wiki/Part-07-Testing/01-Unit-Tests) - Test unitari
- [**02-Integration-Tests**]({{ site.baseurl }}/wiki/Part-07-Testing/02-Integration-Tests) - Test di integrazione
- [**03-Benchmarks**]({{ site.baseurl }}/wiki/Part-07-Testing/03-Benchmarks) - Benchmarking e performance

#### **Parte VIII: Futuro**) - Roadmap e Estensioni
- [**00-Introduzione**]({{ site.baseurl }}/wiki/Part-08-Future/00-Introduzione) - Visione futura
- [**01-Roadmap**]({{ site.baseurl }}/wiki/Part-08-Future/01-Roadmap) - Roadmap di sviluppo

### 🔧 **Guide Operative**) - Riferimenti Pratici

- [**Prefazione**]({{ site.baseurl }}/wiki/Prefazione) - Introduzione generale al progetto
- [**00-Introduzione**]({{ site.baseurl }}/wiki/Appendices/00-Introduzione) - Guida introduttiva
- [**01-Glossario**]({{ site.baseurl }}/wiki/Appendices/01-Glossario) - Terminologia tecnica
- [**02-Configurazione**]({{ site.baseurl }}/wiki/Appendices/02-Configurazione) - Guida alla configurazione

## 🔧 API Reference

### Core Modules

| Modulo | Descrizione | File Principali |
|--------|-------------|-----------------|
| **ColibriCore** | Motore database core | `Sources/ColibriCore/` |
| **coldb** | CLI amministrativa | `Sources/coldb/` |
| **coldb-server** | Server di rete | `Sources/coldb-server/` |
| **benchmarks** | Test di performance | `Sources/benchmarks/` |

### Quick Links

- [**Database API**]({{ site.baseurl }}/wiki/Part-02-Core-Engine/03-Heap-Storage) - Operazioni database
- [**Index API**]({{ site.baseurl }}/wiki/Part-02-Core-Engine/04-BTree-Indexes) - Gestione indici
- [**Transaction API**]({{ site.baseurl }}/wiki/Part-02-Core-Engine/05-MVCC-Concurrency) - Gestione transazioni
- [**CLI Commands**]({{ site.baseurl }}/wiki/Part-06-Tooling/01-User-CLI) - Comandi CLI
- [**Configuration**]({{ site.baseurl }}/wiki/Appendices/02-Configurazione) - Configurazione sistema

## 🏗️ Architettura del Sistema

### Struttura del Repository

```
Colibri-DB/
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

### Esecuzione Test

```bash
# Esegui tutti i test
swift test

# Esegui categorie specifiche
swift test --filter WAL
swift test --filter Buffer
swift test --filter BTree

# Esegui benchmark
swift run benchmarks --help
```

## 📊 Performance

### Metriche Target

- **WAL Throughput**: 10,000+ operazioni/secondo
- **B+Tree Lookups**: 1M+ lookups/secondo
- **Transaction Throughput**: 1,000+ transazioni/secondo
- **Buffer Pool Hit Rate**: >95%

## 🤝 Contribuire

Accogliamo i contributi! Consulta le nostre [Linee Guida per i Contributi](https://github.com/gpicchiarelli/Colibri-DB/blob/main/CONTRIBUTING.md) e il [Codice di Condotta](https://github.com/gpicchiarelli/Colibri-DB/blob/main/CODE_OF_CONDUCT.md).

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

## 📄 Licenza

Licenza BSD 3-Clause License

---

<div align="center">

[⭐ Stella su GitHub](https://github.com/gpicchiarelli/Colibri-DB) • [📖 Leggi la documentazione]({{ site.baseurl }}/docs/README) • [🐛 Segnala problemi](https://github.com/gpicchiarelli/Colibri-DB/issues) • [💬 Partecipa alle discussioni](https://github.com/gpicchiarelli/Colibri-DB/discussions)

**Colibrì DB**

</div>