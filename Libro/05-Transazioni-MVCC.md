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

Terminologia e concetti chiave
------------------------------
- TID: identificatore di transazione, crescente e usato come proxy temporale.
- Version chain: per ogni `(tabella, RID)` una catena di versioni con `beginTID`/`endTID`.
- Snapshot cutoff: soglia logica oltre la quale le transazioni sono "future" e quindi invisibili.

Lifecycle transazionale
-----------------------
1. Begin: alloca TID, registra contesto (isolamento, cutoff, clock logico) e scrive `begin` nel WAL.
2. DML: inserimenti e cancellazioni creano nuove versioni e undo log; vengono emessi record WAL coerenti.
3. Commit: marca la transazione come committed, aggiorna catene MVCC e appende `commit`.
4. Rollback: ripercorre l'undo log e produce CLR per garantire idempotenza.

Livelli di isolamento e visibilità
----------------------------------
- Read Committed: ogni lettore vede solo effetti di transazioni già committate al momento della lettura; lo snapshot può cambiare durante la transazione.
- Repeatable Read / Snapshot Isolation: snapshot stabile (cutoff) per tutta la durata; evita non-repeatable reads.
- Serializable: impone un ordine totale (tramite clock logico/lock più restrittivi); prevenzione dei conflitti di scrittura.

Locking e DDL
-------------
Le operazioni acquisiscono lock a granularità variabile (tabella, indice, DDL) con **timeout** configurabili. Le operazioni DDL possono forzare escalation per garantire atomicità dei cambiamenti strutturali.

Vacuum e manutenzione
---------------------
Il vacuum rimuove versioni obsolete non più visibili ad alcuna transazione attiva. La frequenza e la profondità del vacuum sono modulabili; le metriche tracciano pagine compattate e frammentazione residua.

2PC (Two Phase Commit)
----------------------
Per scenari distribuiti, una fase di `prepare` forza il flush di WAL e buffer, marcando il TID come pronto. `commitPrepared/abortPrepared` completano o annullano la transazione coordinata esternamente.

