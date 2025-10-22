# ColibrìDB Documentation

> **Documentazione completa per il database relazionale formalmente verificato**

Questa è la documentazione completa per ColibrìDB, un RDBMS production-ready implementato in Swift 6.2 con verifica formale TLA+. La documentazione è organizzata per diversi tipi di utenti e livelli di approfondimento.

## 🚀 Quick Start

### Per Sviluppatori

- **[Quick Start](wiki/Quick-Start.md)** - Inizia subito con ColibrìDB
- **[Configuration](wiki/Configuration.md)** - Configurazione del database
- **[API Reference](wiki/API-Reference.md)** - Riferimento API completo
- **[CLI Reference](wiki/CLI-Reference.md)** - Comandi della CLI

### Per Architetti

- **[Architecture](architecture.html)** - Architettura del sistema
- **[TLA+ Specifications](tla-specifications.html)** - Specifiche formali
- **[Performance](wiki/Performance.md)** - Metriche e benchmark
- **[Security](wiki/Part-05-Security/)** - Sicurezza e autorizzazione

### Per Ricercatori

- **[Academic Paper](ACADEMIC_PAPER_DRAFT.md)** - Paper accademico completo
- **[TLA+ Implementation Summary](TLA_IMPLEMENTATION_SUMMARY.md)** - Riepilogo implementazioni
- **[Literature Compliance](spec/LITERATURE_COMPLIANCE_CERTIFICATE.md)** - Conformità letteratura

## 📚 Struttura Documentazione

### 🎓 Manuale Universitario (8 Parti)

#### [Parte I: Fondamenti](wiki/Part-01-Foundations/)
- **Principi Relazionali** - Modello relazionale e algebra
- **Teoria delle Transazioni** - ACID e isolamento
- **Storage Principles** - Gestione persistenza e indici
- **Concurrency Control** - MVCC e locking

#### [Parte II: Motore Core](wiki/Part-02-Core-Engine/)
- **WAL e Recovery** - Write-Ahead Logging e ARIES
- **Buffer Pool** - Gestione cache e eviction
- **Heap Storage** - Storage engine e slotted pages
- **Indici B+Tree** - Strutture dati per accesso veloce
- **MVCC** - Multi-Version Concurrency Control

#### [Parte III: Elaborazione Query](wiki/Part-03-Query/)
- **SQL Parser** - Parsing e analisi sintattica
- **Logical Planning** - Pianificazione logica
- **Physical Planning** - Ottimizzazione cost-based
- **Execution Engine** - Esecuzione operatori relazionali
- **Advanced Features** - Window functions e viste materializzate

#### [Parte IV: Metadati](wiki/Part-04-Metadata/)
- **Catalog Core** - Catalogo di sistema
- **Statistics** - Statistiche per ottimizzazione
- **Schema Management** - Gestione schema e DDL

#### [Parte V: Server](wiki/Part-05-Server/)
- **Server Architecture** - Architettura server
- **Wire Protocol** - Protocollo client-server
- **Server Operations** - Operazioni e gestione connessioni

#### [Parte VI: Tooling](wiki/Part-06-Tooling/)
- **User CLI** - Interfaccia utente
- **Dev CLI** - Strumenti sviluppo
- **Monitoring & DevOps** - Monitoring e operazioni

#### [Parte VII: Testing](wiki/Part-07-Testing/)
- **Unit Tests** - Test unitari
- **Integration Tests** - Test integrazione
- **Benchmarks** - Test performance

#### [Parte VIII: Futuro](wiki/Part-08-Future/)
- **Roadmap** - Piani di sviluppo
- **Estensioni** - Funzionalità future

### 🔧 Guide Operative

#### Configurazione e Deployment
- **[Configuration Guide](wiki/Configuration.md)** - Configurazione completa
- **[Performance Tuning](wiki/Performance.md)** - Ottimizzazione performance
- **[Troubleshooting](wiki/Troubleshooting.md)** - Risoluzione problemi

#### Sviluppo e Contributi
- **[Development Guide](wiki/Development.md)** - Setup sviluppo
- **[API Reference](wiki/API-Reference.md)** - Riferimento API
- **[Examples](wiki/Examples.md)** - Esempi di codice

### 🔬 Documentazione Tecnica

#### Verifica Formale
- **[TLA+ Specifications](tla-specifications.html)** - Specifiche formali complete
- **[Implementation Status](IMPLEMENTATION_STATUS_FINAL.md)** - Stato implementazioni
- **[Completeness Report](TLA_SWIFT_COMPLETENESS_REPORT.md)** - Report completezza

#### Architettura e Design
- **[Architecture Overview](architecture.html)** - Architettura sistema
- **[Academic Foundations](ACADEMIC_PAPER_DRAFT.md)** - Fondamenti accademici
- **[Design Decisions](wiki/Architecture.md)** - Decisioni progettuali

## 🎯 Guide per Tipo di Utente

### 👨‍💻 Sviluppatori

**Per iniziare:**
1. [Quick Start](wiki/Quick-Start.md) - Setup rapido
2. [API Reference](wiki/API-Reference.md) - Riferimento API
3. [Examples](wiki/Examples.md) - Esempi pratici

**Per sviluppo avanzato:**
1. [Development Guide](wiki/Development.md) - Setup completo
2. [Architecture](architecture.html) - Comprensione sistema
3. [Testing](wiki/Part-07-Testing/) - Testing e qualità

### 🏗️ Architetti di Sistema

**Per comprensione architetturale:**
1. [Architecture Overview](architecture.html) - Panoramica completa
2. [TLA+ Specifications](tla-specifications.html) - Specifiche formali
3. [Performance](wiki/Performance.md) - Caratteristiche performance

**Per decisioni progettuali:**
1. [Academic Paper](ACADEMIC_PAPER_DRAFT.md) - Fondamenti teorici
2. [Design Decisions](wiki/Architecture.md) - Decisioni implementative
3. [Literature Compliance](spec/LITERATURE_COMPLIANCE_CERTIFICATE.md) - Conformità accademica

### 🎓 Ricercatori e Accademici

**Per ricerca e studio:**
1. [Academic Paper](ACADEMIC_PAPER_DRAFT.md) - Paper completo
2. [TLA+ Implementation Summary](TLA_IMPLEMENTATION_SUMMARY.md) - Implementazioni
3. [Literature Compliance](spec/LITERATURE_COMPLIANCE_CERTIFICATE.md) - Conformità letteratura

**Per verifica formale:**
1. [TLA+ Specifications](tla-specifications.html) - Specifiche complete
2. [Implementation Status](IMPLEMENTATION_STATUS_FINAL.md) - Stato implementazioni
3. [Completeness Report](TLA_SWIFT_COMPLETENESS_REPORT.md) - Report completezza

### 🔧 Operatori e DevOps

**Per deployment e operazioni:**
1. [Configuration](wiki/Configuration.md) - Configurazione produzione
2. [Performance](wiki/Performance.md) - Ottimizzazione
3. [Troubleshooting](wiki/Troubleshooting.md) - Risoluzione problemi

**Per monitoring:**
1. [Monitoring Guide](wiki/Part-06-Tooling/03-Monitoring-DevOps.md) - Monitoring completo
2. [CLI Reference](wiki/CLI-Reference.md) - Strumenti amministrativi
3. [Performance](wiki/Performance.md) - Metriche e benchmark

## 📖 Come Navigare la Documentazione

### Per Argomento

- **Storage**: [Parte II - Core Engine](wiki/Part-02-Core-Engine/)
- **Query Processing**: [Parte III - Query](wiki/Part-03-Query/)
- **Distributed Systems**: [Parte V - Server](wiki/Part-05-Server/)
- **Security**: [Parte V - Security](wiki/Part-05-Security/)
- **Testing**: [Parte VII - Testing](wiki/Part-07-Testing/)

### Per Livello di Dettaglio

- **Panoramica**: [Architecture](architecture.html), [Quick Start](wiki/Quick-Start.md)
- **Dettaglio**: [Parti I-VIII](wiki/Part-01-Foundations/), [API Reference](wiki/API-Reference.md)
- **Implementazione**: [TLA+ Specifications](tla-specifications.html), [Academic Paper](ACADEMIC_PAPER_DRAFT.md)

### Per Tipo di Contenuto

- **Tutorial**: [Quick Start](wiki/Quick-Start.md), [Examples](wiki/Examples.md)
- **Reference**: [API Reference](wiki/API-Reference.md), [CLI Reference](wiki/CLI-Reference.md)
- **Theory**: [Academic Paper](ACADEMIC_PAPER_DRAFT.md), [TLA+ Specifications](tla-specifications.html)
- **Operations**: [Configuration](wiki/Configuration.md), [Troubleshooting](wiki/Troubleshooting.md)

## 🔍 Ricerca nella Documentazione

### Per Parole Chiave

- **TLA+**: [TLA+ Specifications](tla-specifications.html)
- **Performance**: [Performance](wiki/Performance.md)
- **Security**: [Security](wiki/Part-05-Security/)
- **Testing**: [Testing](wiki/Part-07-Testing/)
- **API**: [API Reference](wiki/API-Reference.md)

### Per Componente

- **WAL**: [WAL and Recovery](wiki/Part-02-Core-Engine/01-WAL-and-Recovery.md)
- **MVCC**: [MVCC Concurrency](wiki/Part-02-Core-Engine/05-MVCC-Concurrency.md)
- **Query Optimizer**: [Physical Planning](wiki/Part-03-Query/03-Physical-Planning.md)
- **Lock Manager**: [MVCC Concurrency](wiki/Part-02-Core-Engine/05-MVCC-Concurrency.md)

## 📝 Contribuire alla Documentazione

La documentazione è parte integrante del progetto. Per contribuire:

1. **Segnala problemi**: Apri una issue per documentazione mancante o errata
2. **Proponi miglioramenti**: Suggerisci nuove sezioni o miglioramenti
3. **Contribuisci contenuti**: Invia PR per aggiornamenti o nuove guide
4. **Migliora esempi**: Aggiungi esempi pratici e casi d'uso

### Linee Guida

- **Chiarezza**: Scrivi in modo chiaro e accessibile
- **Completezza**: Fornisci esempi pratici e casi d'uso
- **Aggiornamento**: Mantieni la documentazione sincronizzata con il codice
- **Struttura**: Segui la struttura esistente e le convenzioni

## 🆘 Supporto

### Risorse di Supporto

- **Issues**: [GitHub Issues](https://github.com/gpicchiarelli/Colibri-DB/issues)
- **Discussions**: [GitHub Discussions](https://github.com/gpicchiarelli/Colibri-DB/discussions)
- **Documentation**: Questa documentazione
- **Examples**: [Examples](wiki/Examples.md)

### Contatti

- **Maintainer**: [@gpicchiarelli](https://github.com/gpicchiarelli)
- **Community**: [GitHub Discussions](https://github.com/gpicchiarelli/Colibri-DB/discussions)
- **Security**: [SECURITY.md](SECURITY.md)

---

**ColibrìDB Documentation** - Aggiornata per v1.0.0  
*Ultimo aggiornamento: 2025-10-19*