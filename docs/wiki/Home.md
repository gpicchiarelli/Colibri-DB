---
layout: doc
title: Home
description: Benvenuto nella documentazione di Colibrì DB - RDBMS moderno per macOS
---

# Benvenuto in Colibrì DB

Colibrì DB è un database relazionale moderno e performante progettato specificamente per macOS, scritto in Swift 6.2 con architettura modulare e verifiche formali complete.

## 🚀 Inizia Subito

- **[Quick Start](Quick-Start.md)** - Installa e configura Colibrì DB in 5 minuti
- **[Architettura](Architecture.md)** - Scopri come funziona internamente
- **[API Reference](API-Reference.md)** - Documentazione completa delle API

## 📚 Documentazione

### Fondamenti
- **[Relational Principles](Part-01-Foundations/01-Relational-Principles.md)** - Principi del modello relazionale
- **[SQL Algebra](Part-01-Foundations/02-Algebra-SQL.md)** - Algebra relazionale e SQL
- **[Transaction Theory](Part-01-Foundations/03-Transactions-Theory.md)** - Teoria delle transazioni ACID
- **[Storage Principles](Part-01-Foundations/04-Storage-Principles.md)** - Principi di storage e persistenza

### Core Engine
- **[WAL and Recovery](Part-02-Core-Engine/01-WAL-and-Recovery.md)** - Write-Ahead Log e recovery
- **[Buffer Pool](Part-02-Core-Engine/02-BufferPool.md)** - Gestione della memoria
- **[Heap Storage](Part-02-Core-Engine/03-Heap-Storage.md)** - Storage su heap
- **[B-Tree Indexes](Part-02-Core-Engine/04-BTree-Indexes.md)** - Indici B-Tree
- **[MVCC Concurrency](Part-02-Core-Engine/05-MVCC-Concurrency.md)** - Controllo concorrenza MVCC

### Query Processing
- **[SQL Parser](Part-03-Query/01-SQL-Parser.md)** - Parsing delle query SQL
- **[Logical Planning](Part-03-Query/02-Logical-Planning.md)** - Pianificazione logica
- **[Physical Planning](Part-03-Query/03-Physical-Planning.md)** - Pianificazione fisica
- **[Execution Engine](Part-03-Query/04-Execution-Engine.md)** - Motore di esecuzione
- **[Advanced Features](Part-03-Query/05-Advanced-Features.md)** - Funzionalità avanzate

### Metadata e Server
- **[Metadata Management](Part-04-Metadata/)** - Gestione metadati
- **[Server Architecture](Part-05-Server/)** - Architettura del server

### Tooling e Testing
- **[Development Tools](Part-06-Tooling/)** - Strumenti di sviluppo
- **[Testing Framework](Part-07-Testing/)** - Framework di testing

## 🔬 Specifiche Formali

Colibrì DB utilizza specifiche TLA+ per verificare formalmente le proprietà di sicurezza e liveness:

- **[Specifiche TLA+](../tla-specifications.html)** - Panoramica delle specifiche formali
- **[WAL Specification](/spec/WAL.tla)** - Specifica del Write-Ahead Log
- **[Consensus Protocol](/spec/ConsensusProtocol.tla)** - Protocollo di consenso Raft
- **[Two-Phase Commit](/spec/TwoPhaseCommit.tla)** - Commit distribuito

## 🛠️ Sviluppo

### Struttura del Codice

```
Sources/ColibriCore/
├── Database/           # Attore principale ColibrìDB
├── BufferPool/         # Gestione buffer pool
├── Storage/            # Storage manager e heap tables
├── WAL/               # Write-Ahead Log
├── Transaction/        # Gestione transazioni
├── MVCC/              # Multi-Version Concurrency Control
├── SQL/               # Parser SQL
├── Query/             # Query executor
├── Consensus/         # Protocollo Raft
├── Distributed/       # Funzionalità distribuite
└── Monitoring/        # Metriche e monitoring
```

### Build e Test

```bash
# Compila il progetto
swift build

# Esegui i test
swift test

# Esegui i benchmark
swift run benchmarks

# Avvia il server
swift run coldb-server
```

## 📊 Performance

Colibrì DB è ottimizzato per performance elevate:

- **Buffer Pool**: Algoritmo clock-sweep per gestione efficiente della memoria
- **WAL**: Group commit e flush ottimizzato per throughput elevato
- **Query Engine**: Ottimizzatore cost-based con statistiche runtime
- **Indici**: B-Tree, hash e bitmap per accessi veloci

## 🔒 Sicurezza

- **Autenticazione**: Sistema di autenticazione robusto
- **Autorizzazione**: RBAC (Role-Based Access Control)
- **Crittografia**: Supporto per crittografia end-to-end
- **Audit**: Logging completo delle operazioni

## 🌐 Distribuzione

- **Sharding**: Partizionamento automatico dei dati
- **Replica**: Replica sincrona e asincrona
- **Consenso**: Protocollo Raft per elezione leader
- **Query Distribuite**: Esecuzione federata delle query

## 🤝 Contribuire

Colibrì DB è un progetto open source. Contributi sono benvenuti!

1. **Fork** il repository
2. **Crea** un branch per la tua feature
3. **Commit** le modifiche
4. **Push** al branch
5. **Apri** una Pull Request

Vedi [CONTRIBUTING.md](https://github.com/gpicchiarelli/Colibri-DB/blob/main/CONTRIBUTING.md) per dettagli.

## 📞 Supporto

- **GitHub Issues**: [Segnala bug](https://github.com/gpicchiarelli/Colibri-DB/issues)
- **Discussions**: [Partecipa alle discussioni](https://github.com/gpicchiarelli/Colibri-DB/discussions)
- **Email**: support@colibridb.dev

## 📄 Licenza

Colibrì DB è rilasciato sotto licenza MIT. Vedi [LICENSE](https://github.com/gpicchiarelli/Colibri-DB/blob/main/LICENSE) per dettagli.

---

*Ultimo aggiornamento: {{ "now" | date: "%d/%m/%Y" }}*