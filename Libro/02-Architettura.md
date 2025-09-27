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

