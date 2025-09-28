# Capitolo 3 — Transazioni, ACID e Concorrenza

## 3.1 Assiomi ACID
- Atomicità, Consistenza, Isolamento, Durabilità.
- Formalizzazione logica e implicazioni operative.

## 3.2 Gestione transazioni in ColibrìDB
- `TransactionManager` e API (`Database+Transactions.swift`).
- `activeTIDs`, `txLastLSN`, `TransactionContext`.

## 3.3 Isolamento
- Livelli supportati (`IsolationLevel`).
- Strategie: 2PL vs MVCC, motivazione della scelta attuale.

## 3.4 Logging e durabilità
- Rimando al Cap. 5 per WAL; qui: precondizioni e invarianti.
- `logTransactionBegin`, `logTransactionCommit`, `logTransactionAbort`.

## 3.5 Deadlock e lock manager
- Stato attuale: TODO vs implementato.
- Proposta architetturale (grafo d'attesa, timeout, detection).

## 3.6 Esempi
- Transazione singola: storyboard delle chiamate.
- Transazioni concorrenti: timeline con eventuali conflitti.
