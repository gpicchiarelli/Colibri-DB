# Capitolo 9 — Concorrenza, MVCC e Versioning

## 9.1 Motivazioni per MVCC
- Limiti del due-phase locking.
- Snapshot isolation come compromesso.

## 9.2 Strutture dati
- `MVCCManager`, `MVCCSnapshot`.
- `activeTIDs`, `visibleTransaction`.

## 9.3 Operazioni
- `registerRead`, `registerWrite`, `commit`, `abort`.
- Garbage collection delle vecchie versioni.

## 9.4 Interazione con WAL e undo
- CLR generati per rollback.
- PageLSN e ordine di applicazione.

## 9.5 Testing e verifiche
- Scenari di phantom read, repeatable read.
- Strumenti `Tests/ColibriCoreTests/MVCCTests.swift` (da completare).
