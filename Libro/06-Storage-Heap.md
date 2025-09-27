06 — Storage: Heap paginato
===========================

Obiettivi e modello
-------------------
Heap su file con pagine a dimensione fissa, slot directory, `Free Space Map` (FSM) persistente e compattazione online. Le tuple sono JSON-encoded (MVP).

File e componenti
-----------------
- `Storage/Page.swift` — anatomia pagina, header con `pageId`, `pageLSN`, checksum CRC32, slot directory.
- `Storage/HeapTable.swift` — protocollo e astrazioni comuni.
- `Storage/FileHeapTable.swift` — implementazione su file, gestione FSM e lock striping.

Inserimento, scansione, delete
------------------------------
- Insert: selezione pagina via FSM (first-fit) oppure allocazione nuova pagina, aggiornamento directory e FSM.
- Scan: lettura pagine dal buffer pool, parsing slot e restituzione `(RID, Row)`.
- Delete/Restore: marcatura dead/restore per MVCC e redo deterministico, aggiornamento `pageLSN`.

Integrazione con WAL e MVCC
---------------------------
Ogni mutazione produce record WAL e aggiorna catene MVCC; `pageLSN` coordina idempotenza in redo (`recordLSN` ≤ `pageLSN`).

