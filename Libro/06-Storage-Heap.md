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

Layout di pagina in dettaglio
-----------------------------
L'header occupa la parte iniziale con: magic, `pageId`, `pageLSN`, puntatori allo spazio libero (`freeStart/freeEnd`), contatore slot e checksum. La slot directory cresce da destra, mentre i dati crescono da sinistra; l'inserimento riesce se c'è spazio contiguo sufficiente tra i due.

Algoritmo di inserimento e selezione pagina
-------------------------------------------
La `Free Space Map` mantiene una stima dello spazio contiguo disponibile per pagina e classe le pagine in **bucket** (64B, 128B, ...). L'inserimento prova i candidati `first-fit`, aggiornando FSM e candidati veloci; in assenza di spazio si alloca una nuova pagina.

Compattazione e frammentazione
------------------------------
La compattazione ricostruisce la slot directory mantenendo l'ordine logico e riposizionando i record vivi in modo denso, riducendo frammenti e ottimizzando i futuri insert. Le metriche aiutano a definire soglie di intervento automatico.

Concorrenza e lock striping
---------------------------
Per ridurre contesa, le operazioni usano **lock per strisce** (più lock per gruppi di pagine) e un lock dedicato per la FSM. Gli aggiornamenti di page e FSM sono pensati per minimizzare sezioni critiche e migliorare throughput su carichi concorrenti.

Integrità e checksum
--------------------
Ogni pagina integra un CRC32 calcolato con accelerazione nativa. Durante il load, le pagine con checksum errato vengono scartate e ricostruite da WAL (quando possibile), garantendo integrità end-to-end.

