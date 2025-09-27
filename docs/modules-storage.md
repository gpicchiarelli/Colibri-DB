# Storage Engine (Heap file paginati)

## Obiettivi
- Supportare workload OLTP con tuple a lunghezza variabile e inserimenti rapidi.
- Permettere compattazione online e vacuum senza downtime.
- Esporre metriche di frammentazione utili alle policy di manutenzione.

## Implementazione attuale
- **Pagine**: dimensione configurabile (default 8KB), header con `pageId`, `pageLSN`, spazio libero, slot directory a crescere da destra.
- **Heap file**: `FileHeapTable` gestisce l'apertura/creazione del file, mantiene `lastPageId` e chiama il buffer pool per tutte le operazioni I/O.
- **Free Space Map (FSM)**: file `.fsm` JSON con mappatura `pageId → spazio libero contiguo`. Caricato all'avvio, ricostruibile tramite scansione delle pagine.
- **Compattazione**: `compactPage` e `compactAllPages` ricostruiscono slot directory e aggiornano FSM; `Database.compactTable` espone la funzionalità via CLI.
- **Restore**: dopo un delete, `restore(rid,row)` permette a rollback e vacuum di reinserire tuple con lo stesso RID.
- **Metriche**: `HeapFragmentationStats` raccoglie tuple vive/morte, byte liberi/dead, media per pagina e stima globale.

## Flusso operazioni principali
1. **Insert**: codifica JSON del `Row`, scelta pagina tramite FSM (first-fit), aggiornamento slot directory e `pageLSN`, flush tramite buffer pool.
2. **Delete**: marcatura della voce come dead e aggiornamento FSM; MVCC registra la versione come terminata.
3. **Scan**: recupero delle pagine via buffer pool, parsing slot directory, restituzione `(RID, Row)`; MVCC filtra la visibilità.
4. **WAL replay**: `insert(row, pageLSN:)` consente redo deterministico con `pageLSN` coerente.

## Integrazione con MVCC & WAL
- Ogni insert/delete/restore aggiorna `MVCCManager` (visible chain) e produce record WAL `insertPre/insertDone/deleteRow`.
- `pageLSN` viene scritto nell'header per coordinare ARIES: se `pageLSN` ≥ `recordLSN`, l'operazione è idempotente durante il redo.

## Configurazione rilevante
- `pageSizeBytes`, `dataBufferPoolPages`, `autoCompactionEnabled`, `autoCompactionIntervalSeconds`, `heapFragmentationThreshold`, `heapFragmentationSamplePages` in `DBConfig` modulano comportamento heap/vacuum.

## Roadmap
- Layout PAX e alternative row/column hybrid per ottimizzare scansioni analitiche.
- Supporto a hot/cold storage tier e tabelle temporanee puramente in-memory.
- Scrubbing sicuro dello spazio libero (wiping) e compressione LZ4/ZSTD selettiva.
