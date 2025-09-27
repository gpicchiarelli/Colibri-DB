# Transazioni & Concorrenza

## Obiettivi
- Garantire isolamento configurabile e durabilità ACID su workload concorrenti.
- Minimizzare la contesa sugli hotspot tramite MVCC e lock granulari.
- Supportare scenari distribuiti (2PC) e manutenzione online (vacuum, compattazione).

## Componenti principali
- **MVCCManager** — Mantiene catene di versioni per ogni `(tabella, RID)`, registra begin/commit/abort, produce snapshot visibili e gestisce vacuum delle tuple non più referenziate.
- **LockManager** — Lock shared/exclusive con deadlock detection, timeout configurabili (`lockTimeoutSeconds`) e tracciamento delle risorse per TID.
- **SerializableClock** — Timestamp logici per implementare livelli di isolamento serializzabile/snapshot.
- **TransactionContext** — Contiene isolamento effettivo, cutoff MVCC e timestamp logico per transazione.
- **TwoPhaseCommit** — Adattatore per gestire prepare/commit/abort distribuito (coordinatore esterno).

## Flusso transazionale
1. `begin()` alloca un TID, registra il contesto nel MVCC e scrive record WAL `begin`.
2. Operazioni DML acquisiscono lock (per tabella/indice/DDL) e registrano undo log (`TxState` con `TxOp`).
3. `commit(tid)` scrive record `commit`, rilascia lock, aggiorna MVCC e serial clock; `rollback` ripercorre il log inverso emettendo CLR.
4. Savepoint: `savepoint(name)` e `rollback(toSavepoint:)` consentono undo parziali.
5. 2PC: `prepareTransaction` forza flush WAL + buffer e marca il TID come preparato; `commitPrepared/abortPrepared` completano la fase successiva.

## Livelli di isolamento
- `DBConfig.defaultIsolationLevel` definisce il livello di default (MVP: `readCommitted`).
- I livelli con snapshot stabile impostano `snapshotCutoff` per filtrare le versioni future.
- Lock manager supporta escalation manuale (DDL) tramite lock di tipo `LockTarget.ddl`.

## Vacuum & manutenzione
- `startVacuum` lancia un timer che processa batch di pagine (`pagesPerRun`) e aggiorna `vacuumTotalPagesCompacted`, `vacuumRuns`, `vacuumLastRun`.
- Il cutoff MVCC garantisce che vengano eliminati solo i record invisibili a tutte le transazioni attive (`minimumActiveTID`).

## Metriche esposte
- `\\stats` stampa aggregati buffer/vacuum.
- `\\vacuum stats` mostra l'ultimo run e i byte recuperati.
- `\\stats prometheus` include `colibridb_vacuum_*` e consente scraping automatico.

## Roadmap
- Implementazione di livelli `repeatable read`/`serializable` con enforcement completo.
- Deadlock detector cooperativo (grafi condivisi tra thread) e lock partitioning adattivo.
- Transaction log replicato per standby follower e replica WAL streaming.
