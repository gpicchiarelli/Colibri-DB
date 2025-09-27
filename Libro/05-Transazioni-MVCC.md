05 — Transazioni, Locking e MVCC
================================

Obiettivi
---------
Garantire ACID su workload concorrenti con snapshot coerenti e lock granulari.

Componenti
----------
- `IsolationLevel` definisce i livelli supportati e se richiedono snapshot stabili.
- `MVCCManager` traccia versioni (`beginTID/endTID`), calcola visibilità e gestisce vacuum.
- `LockManager` fornisce lock shared/exclusive e target per DDL.
- `TwoPhaseCommit` abilita prepare/commit distribuito.

Flusso transazionale
--------------------
1. `Database.begin(isolation:)` alloca TID, registra contesto (cutoff/snapshot), emette WAL `begin`.
2. DML emettono record WAL tipizzati e aggiornano catene MVCC.
3. `commit/rollback` emettono `commit`/CLR e aggiornano visibilità.

Integrazione con letture
------------------------
Le scansioni costruiscono snapshot MVCC e filtrano le tuple in base a `cutoffTID` e agli stati delle versioni.

