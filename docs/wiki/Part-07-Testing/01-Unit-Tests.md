---
layout: page
title: Unit Tests
description: Capitolo 24 - Test unitari
---

# Capitolo 24 — Testing Unitario e di Modulo

> **Obiettivo**: documentare la strategia di testing unitario per Colibrì DB, evidenziando copertura, framework e casi principali.

---

## 24.1 Struttura della suite

`Tests/ColibriCoreTests` contiene le test case organizzate per modulo (WAL, catalogo, buffer, SQL, ecc.). Usa `XCTest` come framework.

### 24.1.1 Convenzioni
- Naming `testFunctionality`
- Setup/teardown per inizializzare database temporanei.

---

## 24.2 Test WAL

`WALTests.swift` verifica:
- Append and read: assicura monotonicità LSN e integrità dei record.
- Checkpoint: scrittura e lettura di `WALCheckpointRecord`.

Tabella invarianti testati:

| Test | Invariante |
|------|------------|
| `testAppendAndRead` | `read(lsn)` restituisce record originale |
| `testCheckpoint` | `writeCheckpoint` produce record con DPT/ATT |

---

## 24.3 Storage e Buffer

`BufferPoolTests`, `HeapTableTests`:
- Verificano che pin/unpin gestiscano `pinCount`.
- Controllano `pageLSN` prima del flush.

---

## 24.4 Catalogo

`CatalogTests` controlla:
- Registrazione tabelle/indici.
- Persistenza del catalogo.
`StatisticsTests` verifica aggiornamento e utilizzo statistiche.

---

## 24.5 Copertura

Comando `swift test --enable-code-coverage` generare report. Analizzare aree scoperte (es. branch in `RuleEngine`).

---

## 24.6 Laboratorio

1. Eseguire `swift test --filter WALTests`.
2. Introduci volutamente un bug (es. ordine LSN) e osserva il fallimento.
3. Esaminare report di coverage.

---

## 24.7 Collegamenti
- **Parte VII** prosegue con test d'integrazione e benchmark.

