ColibrìDB (MVP)
================

[![Build Status](https://img.shields.io/github/actions/workflow/status/gpicchiarelli/Colibr-DB/ci.yml?branch=main)](https://github.com/gpicchiarelli/Colibr-DB/actions/workflows/ci.yml)
[![CodeQL](https://img.shields.io/github/actions/workflow/status/gpicchiarelli/Colibr-DB/codeql.yml?label=codeql&branch=main)](https://github.com/gpicchiarelli/Colibr-DB/actions/workflows/codeql.yml)
![Swift](https://img.shields.io/badge/Swift-6.2-orange.svg)
![SwiftPM](https://img.shields.io/badge/SwiftPM-compatible-brightgreen.svg)
![Platform](https://img.shields.io/badge/platform-macOS%2013%2B-lightgrey.svg)
![License: BSD-3-Clause](https://img.shields.io/badge/License-BSD_3--Clause-blue.svg)
![Stars](https://img.shields.io/github/stars/gpicchiarelli/Colibr-DB?style=social)
![Issues](https://img.shields.io/github/issues/gpicchiarelli/Colibr-DB)
![PRs](https://img.shields.io/github/issues-pr/gpicchiarelli/Colibr-DB)
![Last commit](https://img.shields.io/github/last-commit/gpicchiarelli/Colibr-DB)
![Contributors](https://img.shields.io/github/contributors/gpicchiarelli/Colibr-DB)
![PRs Welcome](https://img.shields.io/badge/PRs-welcome-brightgreen.svg)

ColibrìDB è un RDBMS sperimentale scritto in Swift 6.2 pensato per gestire milioni di connessioni logiche, ottimizzato per macOS e Apple Silicon. Il progetto punta a un'architettura modulare: motore heap su disco con WAL, MVCC, indici pluggabili e CLI amministrativa `coldb`.

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
La documentazione tecnica è allineata e organizzata in `docs/`:
- `docs/index.md` — mappa dei documenti e percorsi di lettura
- `docs/overview.md` — visione generale e stato MVP
- `docs/architecture.md` — panoramica a livelli e flussi
- `docs/modules-*.md` — approfondimenti su storage, buffer, indici, WAL, concorrenza
- `docs/cli.md` e `docs/policies.md` — comandi operativi e automazioni
- `docs/security.md`, `docs/apple-silicon.md`, `docs/appendices.md` — aspetti trasversali, ottimizzazioni e materiali di supporto
- `docs/dimensional-limits.md` — vincoli dimensionali (pagine, slot, WAL, buffer) e valori di default
- `docs/benchmarking.md` — guida ai benchmark micro/macro e al target `benchmarks`

Struttura del repository
------------------------
- `Sources/ColibriCore/` — core engine (storage, WAL, MVCC, indici, policy, util)
- `Sources/coldb/` — CLI amministrativa
- `Sources/benchmarks/` — harness `benchmarks` per test di performance
- `Tests/` — suite di test SwiftPM
- `docs/` — documentazione tecnica
- `data/` — dati runtime (ignorati dal VCS)
- `prompt/` — materiale ausiliario, escluso dal VCS

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
