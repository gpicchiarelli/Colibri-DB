02 — Architettura
=================

Visione a strati
----------------
ColibrìDB adotta un'architettura modulare e osservabile. I layer principali:

- Interfaccia e driver: CLI `Sources/coldb/`, server `Sources/coldb-server/`.
- SQL: lexer, parser e AST in `Sources/ColibriCore/SQL/` con `SQLQueryInterface` come facciata.
- Planner/Executor: cost model, operatori Volcano e orchestrazione in `Sources/ColibriCore/Planner/` e `Database+Planner`.
- Concurrency: `Transactions/` per MVCC, isolamento e lock manager.
- Storage: heap e pagine in `Storage/`, buffer pool in `Buffer/`, WAL in `WAL/`, indici in `Index/`.
- Cataloghi, policy e util in `Catalog/`, `Policy/`, `Util/`.

Flussi essenziali
-----------------
- Query SQL: `SQLQueryInterface.execute(sql)` → `SQLParser.parse` → `executeStatement` → API `Database` (DDL/DML) o `executeQuery` (planner) → operatori Volcano.
- DML (INSERT/UPDATE/DELETE): produce record WAL, aggiorna heap/indici, notifica MVCC; commit/rollback coordinano visibilità e durability.
- Lettura: snapshot MVCC, scansione pagine via buffer pool, filtro visibilità, proiezione.

Punti di ingresso nel codice
----------------------------
- `Sources/ColibriCore/Database.swift` — coordinatore dei sottosistemi, configurazione (`Config.swift`) e metriche.
- `Sources/ColibriCore/SQL/SQLQueryInterface.swift` — facciata SQL di alto livello.
- `Sources/ColibriCore/Planner/QueryPlanner.swift` e `.../PlanOperator.swift` — pianificazione e operatori.
- `Sources/ColibriCore/Transactions/` — MVCC (`MVCC.swift`), isolamento (`Isolation.swift`), lock e 2PC.
- `Sources/ColibriCore/Storage/` — heap (`FileHeapTable.swift`, `HeapTable.swift`), pagine (`Page.swift`).
- `Sources/ColibriCore/WAL/FileWAL.swift` — WAL e recovery.

Risorse correlate
-----------------
- Documenti in `docs/architecture.md`, `docs/overview.md` per una vista sintetica.

Principi di progettazione
-------------------------
L'architettura privilegia coesione interna dei moduli e accoppiamento debole tra layer. Ogni sottosistema espone contratti chiari (protocolli Swift) e si affida a tipi serializzabili per attraversare i confini. L'osservabilità è una proprietà di primo livello: ogni operazione strategica (planner, I/O, WAL) emette segnali e statistiche consultabili da CLI.

Boundary e contratti tra layer
------------------------------
- Tra SQL e motore, `SQLQueryInterface` funge da facciata: accetta testo, restituisce un `SQLStatement` e delega al `Database` o al planner.
- Tra planner/executor e archiviazione, gli operatori non accedono direttamente ai file: si appoggiano a primitive di scan e index access fornite da `Database`, che incapsula MVCC, locking e buffer pool.
- Tra storage e persistenza, `FileWAL` coordina durabilità con LSN e checksum, mentre il buffer pool gestisce dirty pages e flush asincroni.

Sequenza di bootstrap e ripristino
----------------------------------
All'avvio il `Database` costruisce i sottosistemi con la configurazione: buffer pool e namespace, heap tables mappate su file, indici, WAL. Se rileva log, avvia il replay idempotente ricostruendo lo stato coerente sulla base di `pageLSN`. I cataloghi informano il planner circa tabelle e indici e, quando disponibili, le statistiche.

Ciclo di vita di una richiesta
------------------------------
1. Ingresso: server o CLI inoltrano una stringa SQL.
2. Parse: `SQLParser` produce un `SQLStatement` tipizzato.
3. Pianificazione: per `SELECT`, il `QueryPlanner` costruisce un piano (access path, join, sort, limit) valutando costi CPU/IO e cardinalità.
4. Esecuzione: il pipeline Volcano itera le righe, applica filtri/proiezioni, materializza solo se richiesto.
5. Concorrenza e MVCC: gli accessi rispettano snapshot/lock; le scritture emettono record WAL e aggiornano le version chain.
6. Osservabilità: metriche aggregate vengono aggiornate (hit/miss buffer, bytes scritti, latenza pianificazione).

Osservabilità e diagnostica
---------------------------
Punti di misura nelle fasi ad alto costo: pianificazione (tempo e scelte), I/O (pagine lette/scritte), WAL (throughput), vacuum/compattazione (pagine compattate, frammentazione residua). La CLI espone API per consultare queste grandezze per debug e tuning.

Estendibilità e personalizzazione
--------------------------------
La sostituibilità è abilitata da protocolli: si possono introdurre nuovi formati di storage o indici, ridefinire il cost model o aggiungere operatori del planner. Anche il linguaggio SQL è estensibile mantenendo compatibilità.

Trade-off e scelte progettuali
------------------------------
Il design privilegia semplicità operativa e robustezza: JSON per tuple (MVP), heap con compattazione, WAL lineare, B+Tree consolidati. Il risultato è un motore facile da capire, estendere e misurare.

