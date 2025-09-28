# Capitolo 4 — Fondamenti di Storage e Pagine

## 4.1 Architettura dei file
- Pagine da 8KB, slot directory.
- `FileHeapTable` (`Sources/ColibriCore/Storage/FileHeapTable.swift`).

## 4.2 Buffer pool
- Cache, eviction, dirty pages.
- `BufferPool`, `BufferFrame`, `BufferNamespaceManager`.

## 4.3 PageLSN e logging
- Collegamento con WAL (`pageLSN`, `flush`).
- Assertions e invarianti (`assert(page.pageLSN <= wal.flushedLSN)`).

## 4.4 Indici
- B+Tree (`FileBPlusTreeIndex`), header, checkpoint.
- Pianificazione per altri indici (hash, bitmap).

## 4.5 Gestione spazio libero
- Free space map, compattazione.
- `Vacuum`, `Maintenance` API.

## 4.6 Esempi
- Inserimento record e tracciamento delle scritture.
- Monitoring con `BufferPool.stats`.
