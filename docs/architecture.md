# Architettura

ColibrìDB adotta un'architettura a strati pensata per sostituibilità delle componenti e osservabilità completa. Ogni layer è isolato da protocolli Swift e comunica tramite strutture dati serializzabili.

```
[ CLI coldb ]
      |
      v
[ Planner leggero ] → [ Executor Volcano-like ]
      |                       |
      |                       v
      |             [ Concurrency & MVCC ]
      |                       |
      |                       v
      |               [ Storage Engine ]
      |                  /    |     \
      |                 v     v      v
      |            [ Buffer ] [ Indici ] [ WAL ]
      |                       |
      v                       v
[ Policy & Telemetria ]   [ Cataloghi ]
```

## Strati logici
- **Interfaccia (`coldb`)**: parser dei comandi, orchestrazione delle operazioni e stampa delle metriche. In futuro ospiterà uno scheduler scriptabile e driver remoti.
- **Planner/Executor**: nel MVP realizza direttamente le operazioni DDL/DML attraverso `Database`. Il modello Volcano (`open/next/close`) è pronto per operatori aggiuntivi (scan, filter, sort, join).
- **Concurrency layer**: `MVCCManager`, `LockManager`, `SerializableClock` e `TwoPhaseCommit` gestiscono visibilità delle tuple, lock shared/exclusive, snapshot e 2PC.
- **Storage engine**: gestisce tabelle heap (`FileHeapTable`, `HeapTable`), buffer pool (`LRUBufferPool`), WAL (`FileWAL`) e indici (`AnyStringIndex`, `FileBPlusTreeIndex`).
- **Cataloghi e policy**: registrano metadati (tabelle, indici, configurazioni, ruoli) e ospitano le `Policy` di manutenzione, collegate al simulatore di ottimizzazione.

## Dipendenze principali
- `Database` è il punto di coordinamento: istanzia buffer pool, WAL, cataloghi e ripristina stato/indici all'avvio.
- `BufferNamespaceManager` applica quote per namespace (`table`, `index`) per evitare che un componente monopolizzi il pool.
- `FileHeapTable` delega il paging al buffer pool e mantiene una Free Space Map persistente (`.fsm`).
- `FileBPlusTreeIndex` utilizza un WAL dedicato (`.wal`) e background flush per le pagine indice; checkpoint periodici riducono la lunghezza del log.
- `MVCCManager` è informato da tutte le operazioni DML per mantenere le catene di versioni e calcolare visibilità e vacuum.

## Flussi di dati
1. **Scrittura (INSERT)**: CLI → `Database.insert` → WAL (record pre/done) → Heap (`FileHeapTable.insert`) → aggiornamento indici → update MVCC. In caso di crash, ARIES usa `pageLSN` per redo/undo.
2. **Lettura (SCAN)**: CLI → `Database.scan` → lock condiviso → snapshot MVCC → pagine tramite buffer pool → conversione `Row` → filtro visibilità.
3. **Compattazione**: Policy pianificata → `Database.compactTable`/`FileBPlusTreeIndex.compactLeaves` → scrittura nuove pagine → swap atomico + aggiornamento FSM/cataloghi → WAL checkpoint.
4. **Vacuum**: timer (`startVacuum`) → MVCC calcola cutoff → heap compattato pagina per pagina → metriche aggiornate (`vacuumTotalPagesCompacted`).

## Osservabilità
- `db.bufferPoolStats()`/`bufferPoolAggregateStats()` espongono hit/miss, dirty, pinned, eviction.
- `db.vacuumStats()` e `db.simulateOptimize` forniscono telemetria per manutenzione.
- `\\stats prometheus` esporta tutte le metriche aggregate in formato Prometheus.

## Estendibilità
- Storage/indici/WAL implementano protocolli (`TableStorageProtocol`, `IndexProtocol`, `WALProtocol`) per sostituire componenti senza cambiare il resto del motore.
- Policy, simulatori e cataloghi sono modulari e possono essere estesi per scenari custom.

Approfondisci i singoli layer nei documenti `docs/modules-*.md`.
