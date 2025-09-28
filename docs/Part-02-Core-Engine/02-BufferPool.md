# Capitolo 6 — Buffer Pool e Gestione Pagine

## 6.1 Architettura generale
- Componenti principali: `BufferPool`, `BufferFrame`, `BufferNamespaceManager`.
- File sorgente: `Sources/ColibriCore/Buffer`.

## 6.2 BufferPool
### 6.2.1 Strutture dati
- Dizionario dei frame, LRU, mutex.
- Confronto con letteratura (Gray & Reuter).
### 6.2.2 API principali
- `pin(page:)`, `unpin(page:)`, `markDirty(page:)`.
- Semantica, precondizioni, error handling.
### 6.2.3 Flush
- `flushAll()`, integrazione con WAL.
- Diagramma del flusso flush.

## 6.3 BufferNamespaceManager
- Gestione multi-database e partizioni.
- `registerNamespace`, `flush(namespace:)`.

## 6.4 Page Eviction
- Politica LRU attuale, possibilità di CLOCK.
- Analisi di `evictVictim`.

## 6.5 Integrazione con storage
- Interfaccia `PageStorage`.
- `FileHeapTable` come consumer.

## 6.6 Laboratorio
- Script Swift per generare carichi e osservare `BufferPool.stats`.
