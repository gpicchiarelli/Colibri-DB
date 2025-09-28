---
layout: page
title: MVCC e Concorrenza
description: Capitolo 9 - MVCC e controllo concorrenza in Colibrì DB
---

# Capitolo 9 — Concorrenza, MVCC e Versioning

> **Obiettivo**: spiegare il controllo di concorrenza MVCC di Colibrì DB con un approccio formale, diagrammi temporali e laboratori pratici.

---

## 9.1 Motivazione

Il classico Two-Phase Locking garantisce serializzabilità ma può causare blocchi. MVCC permette letture non bloccanti mantenendo più versioni della stessa tupla.

Fenomeni che MVCC risolve:
- Dirty reads
- Non-repeatable reads
- Lost updates

Fenomeni non completamente risolti (richiede snapshot isolation avanzato): phantom reads.

---

## 9.2 Strutture dati MVCC

| Struttura | Descrizione | File |
|-----------|-------------|------|
| `MVCCManager` | Gestisce versioni e snapshot | `Transactions/MVCC.swift` |
| `VersionChain` | Lista di versioni per `RID` | `Transactions/MVCC.swift` |
| `MVCCSnapshot` | Stato visibile a un `tid` | `Transactions/MVCC.swift` |

Diagramma versioning:
```
RID ──► [Version tid=101, value=v1] ─► [Version tid=102, value=v2] ─► …
```

---

## 9.3 Operazioni principali

### 9.3.1 Lettura (`registerRead`)
- Determina la versione più recente visibile al `tid`.
- Registra dipendenze per detection di conflitti (roadmap).

### 9.3.2 Scrittura (`registerWrite`)
- Crea una nuova versione con `tid` corrente.
- Marca le versioni precedenti come non visibili a snapshot futuri.

### 9.3.3 Commit/abort
- `commit(tid)`: rende la versione visibile a transazioni future.
- `abort(tid)`: genera CLR e ripristina versione precedente.

---

## 9.4 Garbage Collection

Il GC rimuove versioni non visibili a nessuna transazione attiva. Pseudocodice:
```swift
let minActive = activeTIDs.min()
for chain in versionChains {
    chain.remove { version in
        version.tid < minActive && version.isCommitted
    }
}
```

---

## 9.5 Timeline di esempio

Tabella temporale (A = transazione 1, B = transazione 2):

| Tempo | Transazione A | Transazione B | Versioni |
|-------|---------------|---------------|----------|
| t0 | BEGIN | | v0 |
| t1 | UPDATE balance=100 | | v0 → v1 (tid=A) |
| t2 | | SELECT balance | B vede v0 |
| t3 | COMMIT | | v1 diventa visibile |
| t4 | | SELECT balance | B vede v1 |

---

## 9.6 Laboratorio

1. Aprire due sessioni CLI.
2. Sessione A: `BEGIN; UPDATE accounts SET balance = balance + 100 WHERE id=1;`
3. Sessione B: `SELECT balance FROM accounts WHERE id=1;` (osserva valore precedente).
4. Sessione A: `COMMIT;`
5. Sessione B: ripetere SELECT (vede valore aggiornato).

---

## 9.7 Collegamenti
- **Capitolo 3**: teoria ACID e transazioni.
- **Capitolo 5**: CLR prodotti durante abort.
- Appendice Glossario: definizione di MVCC.

