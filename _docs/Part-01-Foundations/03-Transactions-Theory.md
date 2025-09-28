---
layout: page
title: Teoria delle Transazioni
description: Capitolo 3 - Teoria delle transazioni e ACID
---

# Capitolo 3 — Transazioni, ACID e Concorrenza

## 3.1 Proprietà ACID
- **Atomicità**: l'intera transazione viene completata o annullata. Formalmente, se T è una transazione con azioni a₁,…,aₙ, allora lo stato finale Sₙ esiste solo se tutte le azioni sono applicate; in caso contrario il sistema ritorna a S₀.
- **Consistenza**: ogni transazione trasforma uno stato consistente in un altro stato consistente.
- **Isolamento**: le transazioni concorrenti appaiono come se eseguite in sequenza.
- **Durabilità**: gli effetti committati persistono nonostante guasti.

## 3.2 Transaction Manager in ColibrìDB
Il modulo `Database+Transactions.swift` implementa un transaction manager basato su ID numerici (`tid`).

### 3.2.1 Strutture dati
- `activeTIDs: Set<UInt64>`: traccia delle transazioni aperte.
- `txLastLSN: [UInt64: UInt64]`: ultimo LSN scritto per transazione.

### 3.2.2 API principali
- `beginTransaction(isolationLevel:)`: alloca un nuovo `tid`, registra l'inizio nel WAL e aggiorna `activeTIDs`.
- `commitTransaction(tid:)`: scrive record di commit, aggiorna WAL e flush secondo la configurazione.
- `abortTransaction(tid:)`: emette record di abort e chiama l'algoritmo di undo.

## 3.3 Isolamento e livelli
ColibrìDB attualmente implementa un isolamento basato su snapshot (MVCC). Il livello `readCommitted` è la default, mentre `repeatableRead` e `serializable` sono in roadmap.

## 3.4 Interazione con il WAL
- `logTransactionBegin`/`Commit`/`Abort` generano record `WALBeginRecord`, `WALCommitRecord`, `WALAbortRecord`.
- `txLastLSN` viene aggiornato a ogni log per supportare l'undo.

## 3.5 Undo e CLR
- `undoTransaction` ricostruisce le operazioni da `txLastLSN` e produce `WALCLRRecord`.
- Ogni CLR contiene `undoNextLSN` per proseguire l'undo.

## 3.6 Controllo concorrenza
Attualmente un lock manager completo è in progettazione. Il capitolo discute la necessità di lock a livello di record e le interazioni con MVCC.

## 3.7 Laboratorio
1. Aprire due sessioni CLI.
2. In Sessione A: `BEGIN; UPDATE accounts SET balance = balance + 100 WHERE id = 1;`
3. In Sessione B: tentare di leggere `accounts` per vedere l'isolation.
4. Indurre un crash (kill del server) durante la transazione e osservare il recovery.

## 3.8 Collegamenti
Questo capitolo prepara al Capitolo 5 (WAL e recovery) e al Capitolo 9 (MVCC) in Parte II.
