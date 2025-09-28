---
layout: page
title: ColibrìDB Wiki
description: Pagina principale della wiki di ColibrìDB
---

# 🐦 ColibrìDB Wiki

<div align="center">

[![Build Status](https://img.shields.io/github/actions/workflow/status/gpicchiarelli/Colibr-DB/ci.yml?branch=main&style=flat-square)](https://github.com/gpicchiarelli/Colibr-DB/actions/workflows/ci.yml)
[![CodeQL](https://img.shields.io/github/actions/workflow/status/gpicchiarelli/Colibr-DB/codeql.yml?label=CodeQL&branch=main&style=flat-square)](https://github.com/gpicchiarelli/Colibr-DB/actions/workflows/codeql.yml)
![Swift](https://img.shields.io/badge/Swift-6.2-orange.svg?style=flat-square)
![SwiftPM](https://img.shields.io/badge/SwiftPM-compatible-brightgreen.svg?style=flat-square)
![Platform](https://img.shields.io/badge/platform-macOS%2013%2B-lightgrey.svg?style=flat-square)
![License: BSD-3-Clause](https://img.shields.io/badge/License-BSD_3--Clause-blue.svg?style=flat-square)

**Un RDBMS sperimentale ad alte prestazioni scritto in Swift 6.2**

</div>

---

## 🎯 Benvenuto in ColibrìDB

**ColibrìDB** è un RDBMS sperimentale scritto in Swift 6.2 pensato per gestire milioni di connessioni logiche, ottimizzato per macOS e Apple Silicon. Il progetto punta a un'architettura modulare: motore heap su disco con WAL, MVCC, indici pluggabili e CLI amministrativa `coldb`.

### ✨ Caratteristiche Principali

- **🗄️ Storage Enterprise**: Heap file storage con buffer pool LRU/Clock e compattazione online
- **🔒 Durabilità Garantita**: WAL v2 con checksum CRC32 e recovery ARIES-like
- **🚀 Indicizzazione Avanzata**: B+Tree persistenti e indici pluggabili (Hash, ART, LSM)
- **⚡ Controllo Concorrenza**: MVCC con livelli di isolamento configurabili
- **🧠 Query Processing**: Volcano iterator con ottimizzazione cost-based
- **🛠️ Operazioni Complete**: CLI amministrativa, import/export, monitoring

## 📚 Navigazione Wiki

### 🚀 **Per Iniziare**
- [**Quick Start**]({{ site.baseurl }}/wiki/Quick-Start) - Installazione e prima sessione
- [**Configurazione**]({{ site.baseurl }}/wiki/Configuration) - Guida completa alle impostazioni
- [**Esempi Pratici**]({{ site.baseurl }}/wiki/Examples) - Casi d'uso e tutorial

### 🏗️ **Architettura e Sviluppo**
- [**Architettura del Sistema**]({{ site.baseurl }}/wiki/Architecture) - Componenti core e design
- [**API Reference**]({{ site.baseurl }}/wiki/API-Reference) - Documentazione completa delle API
- [**Guida per Sviluppatori**]({{ site.baseurl }}/wiki/Development) - Contribuire al progetto

### 🔧 **Operazioni e Troubleshooting**
- [**CLI Reference**]({{ site.baseurl }}/wiki/CLI-Reference) - Comandi e opzioni della CLI
- [**Performance Guide**]({{ site.baseurl }}/wiki/Performance) - Benchmark e ottimizzazioni
- [**Troubleshooting**]({{ site.baseurl }}/wiki/Troubleshooting) - Risoluzione problemi comuni

### 📖 **Documentazione Tecnica**
- [**Manuale Completo**](https://github.com/gpicchiarelli/Colibr-DB/blob/main/docs/README.md) - Documentazione tecnica dettagliata
- [**Roadmap del Progetto**](https://github.com/gpicchiarelli/Colibr-DB/blob/main/PROJECT_ROADMAP.md) - Piano di sviluppo e milestone

## 🎯 Stato del Progetto

### ✅ **Funzionalità Implementate (Alpha)**
- Motore storage core con WAL
- Indici B+Tree con recovery
- Supporto MVCC e transazioni base
- CLI amministrativa completa
- Documentazione tecnica estesa

### 🚧 **In Sviluppo**
- Modalità server multi-utente
- Transazioni concorrenti avanzate
- Ottimizzazioni Apple Silicon
- Sistema di monitoring avanzato

### 🔮 **Pianificato**
- Conformità SQL completa
- Architettura distribuita
- Deployment cloud-native
- Integrazione con ecosistema Swift

## 🚀 Inizia Subito

```bash
# Clona il repository
git clone https://github.com/gpicchiarelli/Colibr-DB.git
cd Colibr-DB

# Compila il progetto
swift build

# Avvia la CLI
.build/debug/coldb --config colibridb.conf.json
```

## 🤝 Contribuire

ColibrìDB accoglie i contributi! Consulta la nostra [Guida per Sviluppatori]({{ site.baseurl }}/wiki/Development) per iniziare.

### Aree di Contributo
- **Motore Core**: Storage, WAL, indicizzazione
- **Query Processing**: Parser, ottimizzazione, execution
- **Testing**: Copertura test, benchmark, stress test
- **Documentazione**: Guide, esempi, API docs
- **Strumenti**: CLI, monitoring, DevOps

## 📊 Metriche Performance

| Metrica | Target | Stato Attuale |
|---------|--------|---------------|
| WAL Throughput | 10,000+ ops/sec | ✅ Implementato |
| B+Tree Lookups | 1M+ lookups/sec | ✅ Implementato |
| Transaction Throughput | 1,000+ txn/sec | 🚧 In sviluppo |
| Buffer Pool Hit Rate | >95% | ✅ Implementato |

## 🔗 Link Utili

- [**Repository GitHub**](https://github.com/gpicchiarelli/Colibr-DB)
- [**Issue Tracker**](https://github.com/gpicchiarelli/Colibr-DB/issues)
- [**Discussioni**](https://github.com/gpicchiarelli/Colibr-DB/discussions)
- [**Pull Requests**](https://github.com/gpicchiarelli/Colibr-DB/pulls)
- [**Releases**](https://github.com/gpicchiarelli/Colibr-DB/releases)

## 📄 Licenza

Questo progetto è licenziato sotto la **Licenza BSD 3-Clause** - vedi il file [LICENSE](https://github.com/gpicchiarelli/Colibr-DB/blob/main/LICENSE) per i dettagli.

---

<div align="center">

**ColibrìDB** - *Un RDBMS moderno per l'ecosistema Swift*

[⭐ Stella su GitHub](https://github.com/gpicchiarelli/Colibr-DB) • [📖 Documentazione](https://github.com/gpicchiarelli/Colibr-DB/blob/main/docs/README.md) • [🐛 Segnala Bug](https://github.com/gpicchiarelli/Colibr-DB/issues)

</div>
