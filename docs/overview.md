# ColibrìDB — Overview

ColibrìDB è un RDBMS modulare scritto in Swift 6.2 e pensato per sfruttare al massimo hardware Apple Silicon. Il progetto punta a un motore OLTP general purpose con architettura componibile (storage, indici, concorrenza, policy) e un'attenzione particolare a osservabilità e manutenzione automatica.

## Visione
- **Protocol-first**: tutte le componenti principali (storage, indici, WAL, lock manager, policy) espongono protocolli Swift per permettere implementazioni alternative senza impatti a monte.
- **Massimo throughput**: dati paginati, buffer pool con quote per namespace, scritture sequenziali e flusher asincroni per ridurre fsync bloccanti.
- **Osservabilità integrata**: metriche buffer/vacuum disponibili via CLI e in formato Prometheus; cataloghi persistenti con statistiche di frammentazione.
- **Automazione sicura**: politiche di compattazione e ottimizzazione pianificate, con simulazione ex-ante del beneficio atteso e logging delle decisioni.

## Stato attuale (MVP)
- Storage heap su disco con Free Space Map persistente, compattazione online e ripristino dal WAL.
- Buffer pool LRU/Clock/LRU-2 con pin/unpin, background flush e quote separate per tabelle/indici.
- WAL v2 con record tipizzati, CRC32, checkpoint, CLR per undo e recovery ARIES-like (redo/undo).
- Indici: `AnyStringIndex` (Hash, ART, SkipList, Fractal, LSM in-memory) e `FileBPlusTreeIndex` persistente con bulk-build, validazione e compattazione.
- MVCC completo: snapshot visibility, vacuum, undo/redo, supporto a 2PC, isolamento configurabile per transazione.
- CLI `coldb` interattiva con gestione tabelle/indici, import/export CSV, metriche, politiche e simulatore di ottimizzazione.
- Planner Volcano con cost-model: accesso tramite `QueryPlanner`, operatori scan/filter/project/sort/join, predicate pushdown, caching viste materializzate e parallel map sperimentale.
- Cataloghi di sistema/indici con registrazione automatica di tabelle, indici, preferenze di struttura e configurazioni.

## Componenti principali
- **Storage engine** — `FileHeapTable` gestisce pagine da 8KB con slot directory, FSM e checkpoint; `HeapTable` in-memory per test.
- **Buffer pool** — `LRUBufferPool` implementa politiche LRU/Clock/LRU2, background flush e quote gestite da `BufferNamespaceManager`.
- **Log e recovery** — `FileWAL` per il DB, WAL dedicato per ogni `FileBPlusTreeIndex`, Dirty Page Table e replay integrato.
- **Transazioni** — `MVCCManager`, `LockManager`, `SerializableClock`, `TwoPhaseCommit`; gestione di savepoint e rollback parziali.
- **Indici** — `AnyStringIndex` type-erased in-memory e `FileBPlusTreeIndex` persistente con supporto a chiavi composite/multi-tipo.
- **Policy & ottimizzazione** — `PolicyStore`, `SimpleOptimizationSimulator`, compattazione automatica heap/indici e metriche di frammentazione.
- **Planner & esecuzione** — `QueryPlanner`, `PlanOperator` e gli operatori Volcano (scan, filter, project, sort, hash/merge join, limit, parallel map) con cost-model basato su statistiche catalogo.
- **Benchmark & profiling** — target `benchmarks` per scenari micro (heap/indice/planner), linee guida in `docs/performance.md` per fissare baseline e usare strumenti Apple Silicon.

## Percorso di una query (alto livello)
1. La CLI `coldb` interpreta il comando (es. `\\insert`, `\\scan`, `\\index range`).
2. `Database` valida la richiesta, acquisisce i lock necessari e recupera il contesto transazionale/MVCC.
3. Operazioni DML aggiornano l'heap (`FileHeapTable`) e il catalogo MVCC, emettendo record WAL.
4. Gli indici registrati vengono aggiornati attraverso `AnyStringIndex` o `FileBPlusTreeIndex`.
5. Buffer pool e WAL sincronizzano i dati su disco (flush manuale o automatico); il vacuum periodico mantiene bassa la frammentazione.

## Documentazione correlata
- `docs/architecture.md` per il diagramma a livelli e le interazioni fra componenti.
- `docs/modules-*.md` per approfondimenti mirati su buffer, storage, indici, WAL, concorrenza.
- `docs/configuration.md` per la descrizione dettagliata della configurazione runtime.

## Terminologia
Consulta `docs/glossary.md` per abbreviazioni e acronimi utilizzati in tutta la documentazione.
