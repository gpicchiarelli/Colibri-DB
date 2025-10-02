---
layout: doc
title: Architettura di Colibrì DB
description: Panoramica completa dell'architettura modulare di Colibrì DB, dai componenti core alle ottimizzazioni Apple Silicon.
category: Architecture
difficulty: Intermediate
version: 0.1.0
---

# 🏗️ Architettura di Colibrì DB

Colibrì DB è progettato con un'architettura modulare che combina principi di database moderni con ottimizzazioni specifiche per l'ecosistema Apple.

## 🎯 Panoramica del Sistema

```
┌─────────────────────────────────────────────────────────────┐
│                    🎯 SQL Interface & CLI                   │
├─────────────────────────────────────────────────────────────┤
│                    🧠 Query Processor                       │
│              ┌─────────────┬─────────────────────┐          │
│              │   Parser    │    Planner/Optimizer │          │
│              └─────────────┴─────────────────────┘          │
├─────────────────────────────────────────────────────────────┤
│                  ⚡ Transaction Manager                     │
│         ┌──────────────┬──────────────┬──────────────┐      │
│         │     MVCC     │ Lock Manager │     2PC      │      │
│         └──────────────┴──────────────┴──────────────┘      │
├─────────────────────────────────────────────────────────────┤
│                    🚀 Index Manager                         │
│    ┌─────────────┬─────────────┬─────────────┬──────────┐   │
│    │   B+Tree    │    Hash     │     ART     │   LSM    │   │
│    └─────────────┴─────────────┴─────────────┴──────────┘   │
├─────────────────────────────────────────────────────────────┤
│                   🗄️ Storage Engine                        │
│  ┌──────────────┬──────────────┬──────────────┬──────────┐  │
│  │ Heap Storage │ Buffer Pool  │     WAL      │   CRC32  │  │
│  └──────────────┴──────────────┴──────────────┴──────────┘  │
└─────────────────────────────────────────────────────────────┘
```

## 🧩 Componenti Principali

### 1. 🎯 SQL Interface & CLI

Il livello più alto fornisce interfacce per interagire con il database.

**Componenti:**
- **SQL Parser**: Analizza e valida le query SQL
- **CLI Interattiva**: Interfaccia a riga di comando per amministrazione
- **API Programmatiche**: Swift API per integrazione applicazioni

**Caratteristiche:**
- Compatibilità SQL standard
- Validazione sintattica e semantica
- Supporto per transazioni interattive
- Comandi amministrativi estesi

```swift
// Esempio API Swift
let db = Database(config: config)
try db.execute("CREATE TABLE users (id INT, name TEXT)")
let results = try db.query("SELECT * FROM users WHERE age > 25")
```

### 2. 🧠 Query Processor

Il cuore dell'elaborazione delle query con ottimizzazione cost-based.

**Architettura Volcano Iterator:**
```
Query → Parse → Logical Plan → Physical Plan → Execute
  ↓       ↓         ↓            ↓           ↓
 AST → Validate → Optimize → Cost Model → Results
```

**Operatori Supportati:**
- **Scan**: Scansione sequenziale e indicizzata
- **Filter**: Applicazione predicati con pushdown
- **Project**: Selezione colonne
- **Join**: Nested loop, hash join, merge join
- **Sort**: Ordinamento con spill su disco
- **Aggregate**: Funzioni di aggregazione

**Ottimizzazioni:**
- Predicate pushdown
- Projection pushdown  
- Join reordering
- Index selection automatica
- Statistiche per cost model

### 3. ⚡ Transaction Manager

Gestione transazioni con MVCC e controllo concorrenza avanzato.

**MVCC (Multi-Version Concurrency Control):**
```
Transaction ID: 100
┌─────────────────────────────────────────┐
│ Row Version Chain                       │
│ ┌─────┐    ┌─────┐    ┌─────┐          │
│ │ v3  │ -> │ v2  │ -> │ v1  │ -> NULL  │
│ │T:99 │    │T:85 │    │T:42 │          │
│ └─────┘    └─────┘    └─────┘          │
└─────────────────────────────────────────┘
```

**Livelli di Isolamento:**
- **Read Uncommitted**: Performance massima
- **Read Committed**: Default, bilancia consistenza/performance  
- **Repeatable Read**: Letture consistenti
- **Serializable**: Massima consistenza

**Lock Manager:**
- Locking granulare (row-level)
- Deadlock detection con timeout
- Lock striping per ridurre contention
- Supporto per lock condivisi/esclusivi

### 4. 🚀 Index Manager

Sistema di indicizzazione pluggabile con multiple implementazioni.

**B+Tree (Implementazione Principale):**
```
                    [Root Node]
                   /     |     \
            [Internal] [Internal] [Internal]
           /    |    \     |        |     \
      [Leaf] [Leaf] [Leaf] ...   [Leaf] [Leaf]
        |      |      |            |      |
      Data   Data   Data         Data   Data
```

**Caratteristiche B+Tree:**
- Persistenza su disco con checkpoint
- Split/merge automatici
- Bulk loading ottimizzato
- Range queries efficienti
- Validazione integrità

**Indici Alternativi:**
- **Hash Index**: O(1) lookup per equality
- **ART (Adaptive Radix Tree)**: Ottimo per stringhe
- **LSM Tree**: Write-heavy workloads
- **SkipList**: In-memory con ordinamento

### 5. 🗄️ Storage Engine

Il livello più basso gestisce persistenza e I/O.

**Heap File Storage:**
```
Page Header (24 bytes)
┌─────────────────────────────────────────┐
│ Page ID │ LSN │ Checksum │ Free Space  │
├─────────────────────────────────────────┤
│              Slot Directory             │
│ [Slot 1] [Slot 2] ... [Slot N]        │
├─────────────────────────────────────────┤
│                                         │
│              Free Space                 │
│                                         │
├─────────────────────────────────────────┤
│ [Record N] ... [Record 2] [Record 1]   │
└─────────────────────────────────────────┘
```

**Buffer Pool LRU/Clock:**
- Cache intelligente per pagine frequenti
- Eviction policy configurabile
- Dirty page tracking
- Flush asincrono in background
- Namespace isolation

**Write-Ahead Logging (WAL):**
```
WAL Record Format:
┌─────────────────────────────────────────┐
│ LSN │ Type │ TxID │ Length │ Checksum  │
├─────────────────────────────────────────┤
│              Payload Data               │
└─────────────────────────────────────────┘
```

**Tipi di Record WAL:**
- `INSERT`: Nuovi record
- `UPDATE`: Modifiche record esistenti  
- `DELETE`: Rimozione record
- `CHECKPOINT`: Punti di recovery
- `COMMIT/ABORT`: Fine transazione

## 🔧 Ottimizzazioni Apple Silicon

### Accelerazione Hardware

**CRC32 Nativo:**
```swift
// Usa istruzioni ARM64 native per checksum
func calculateCRC32(_ data: Data) -> UInt32 {
    return data.withUnsafeBytes { bytes in
        crc32_arm64(bytes.baseAddress!, bytes.count)
    }
}
```

**SIMD Operations:**
- Comparazioni parallele per scan
- Operazioni bulk su array
- Hashing accelerato

### Memory Management

**Unified Memory Architecture:**
- Ottimizzazioni per memoria condivisa CPU/GPU
- Riduzione copie dati non necessarie
- Prefetching intelligente

**Cache Hierarchy:**
- L1/L2 cache awareness
- False sharing avoidance
- Memory alignment ottimale

## 📊 Metriche e Monitoring

### Statistiche Interne

```swift
struct DatabaseStats {
    let bufferHitRate: Double        // % hit rate buffer pool
    let walThroughput: Int          // Record WAL/sec
    let transactionRate: Int        // Transazioni/sec
    let indexLookups: Int          // Lookup indici/sec
    let diskIO: IOStats            // Statistiche I/O
    let memoryUsage: MemoryStats   // Utilizzo memoria
}
```

### Prometheus Integration

```
# HELP colibri_buffer_hit_rate Buffer pool hit rate
# TYPE colibri_buffer_hit_rate gauge
colibri_buffer_hit_rate 0.95

# HELP colibri_wal_throughput WAL records per second
# TYPE colibri_wal_throughput counter
colibri_wal_throughput 10500

# HELP colibri_active_transactions Active transactions
# TYPE colibri_active_transactions gauge
colibri_active_transactions 42
```

## 🔄 Recovery e Durabilità

### ARIES Recovery Algorithm

**Fasi di Recovery:**
1. **Analysis**: Scansione WAL per determinare stato
2. **Redo**: Riapplica operazioni committed
3. **Undo**: Annulla operazioni non committed

**Checkpoint Process:**
```
1. Flush dirty pages to disk
2. Write checkpoint record to WAL
3. Update checkpoint LSN
4. Truncate old WAL segments
```

### Backup e Restore

**Hot Backup:**
- Backup online senza interruzioni
- Point-in-time recovery
- Incremental backup support

## 🚀 Performance Characteristics

### Target Metrics

| Metrica | Target | Attuale |
|---------|--------|---------|
| WAL Throughput | 10K+ ops/sec | ✅ 12K ops/sec |
| B+Tree Lookups | 1M+ lookups/sec | ✅ 1.2M lookups/sec |
| Buffer Hit Rate | >95% | ✅ 97% |
| Transaction Rate | 1K+ tx/sec | ✅ 1.5K tx/sec |

### Scalabilità

**Vertical Scaling:**
- Supporto fino a 1TB di dati
- Buffer pool fino a 64GB
- Milioni di connessioni logiche

**Horizontal Scaling (Futuro):**
- Sharding automatico
- Replica read-only
- Distributed transactions

## 🔮 Roadmap Architetturale

### Versione 0.2.0 (Beta)
- [ ] Server multi-utente
- [ ] Replica streaming
- [ ] Query parallelization

### Versione 1.0.0 (Produzione)
- [ ] Distributed architecture
- [ ] Cloud-native deployment
- [ ] Advanced analytics engine

### Versioni Future
- [ ] GPU acceleration
- [ ] Machine learning integration
- [ ] Real-time analytics

## 📚 Approfondimenti

Per maggiori dettagli sui singoli componenti:

- **[WAL & Recovery]({{ '/wiki/Part-02-Core-Engine/01-WAL-and-Recovery' | relative_url }})** - Sistema di logging e recovery
- **[Buffer Pool]({{ '/wiki/Part-02-Core-Engine/02-BufferPool' | relative_url }})** - Gestione cache e memoria
- **[B+Tree Indexes]({{ '/wiki/Part-02-Core-Engine/04-BTree-Indexes' | relative_url }})** - Implementazione indici
- **[MVCC]({{ '/wiki/Part-02-Core-Engine/05-MVCC-Concurrency' | relative_url }})** - Controllo concorrenza

<div class="alert alert-info">
<strong>💡 Nota:</strong> L'architettura di Colibrì DB è in continua evoluzione. Consulta regolarmente la documentazione per gli aggiornamenti più recenti.
</div>