01 — Introduzione
=================

Obiettivo del libro
-------------------
Documentare in modo organico gli internals di ColibrìDB, collegando le scelte architetturali al codice sorgente. Il target sono contributori e lettori che desiderano comprendere come il motore funziona sotto il cofano.

Cosa copriamo
-------------
- Architettura a strati e flussi principali.
- Parser SQL, rappresentazioni intermedie e interfaccia di esecuzione.
- Pianificazione ed esecuzione (stile Volcano) con operatori.
- Concorrenza: lock, livelli di isolamento e MVCC.
- Storage: pagine, heap, Free Space Map, buffer pool.
- WAL e recovery (redo/undo; coerenza `pageLSN`).
- Indici (B+Tree, strutture alternative sperimentali).
- Server e CLI.
- Policy, manutenzione, ottimizzazione e telemetria.

Struttura del repository (rapido promemoria)
-------------------------------------------
- `Sources/ColibriCore/` — core engine (storage, WAL, MVCC, indici, planner, SQL).
- `Sources/coldb/` — CLI amministrativa.
- `Sources/coldb-server/` — server TCP e wire protocol.
- `docs/` — guide operative e di riferimento.
- `Tests/` — suite di test SwiftPM.

Come leggere il libro
---------------------
Se sei nuovo al progetto: leggi "02 Architettura", poi i capitoli su SQL, Planner/Executor e Storage. Se contribuisci a una specifica area, salta direttamente al capitolo corrispondente.

