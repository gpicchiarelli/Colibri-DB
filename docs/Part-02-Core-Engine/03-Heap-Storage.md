---
layout: page
title: Heap Storage Engine
description: Capitolo 7 - Motore di storage heap in Colibrì DB
---

# Capitolo 7 — Storage Heap e Gestione delle Tuple

> **Obiettivo**: descrivere in termini accademici la struttura heap-table di Colibrì DB, mappando teoria e codice, con diagrammi e laboratori.

---

## 7.1 Modello di storage

Una **heap table** è una collezione non ordinata di tuple. Le tuple sono memorizzate in pagine di dimensione fissa (8KB). Ogni pagina contiene:
- Header (metadata: `pageId`, `pageLSN`, numero slot).
- Slot directory (array di offset e lunghezze).
- Area dati (tuple in formato compatto).

Schema della pagina:
```
+------------+-------------------+-----------------+
| PageHeader | Slot Directory    | Tuple Data Area |
+------------+-------------------+-----------------+
                ↑                 ↑
                slot entries      tuple payloads
```

---

## 7.2 API di `FileHeapTable`

| Funzione | Descrizione | Effetti |
|----------|-------------|---------|
| `insert(row:pageLSN:)` | Inserisce una nuova tupla | Aggiorna slot, `FreeSpaceMap`, WAL |
| `read(rid:)` | Recupera una tupla | Decodifica da buffer page |
| `delete(rid:pageLSN:)` | Marca la tupla come rimossa | Slot diventa tombstone |
| `update` | Implementata come delete+insert | Produce due record WAL |

### 7.2.1 Inserimento (pseudocodice)
```swift
func insert(row, pageLSN) -> RID {
    let pageId = freeSpaceMap.selectPage(for: row.size)
    let frame = bufferPool.pin(pageId)
    let encoded = RowEncoder.encode(row)
    frame.append(encoded)
    frame.pageLSN = pageLSN
    frame.markDirty()
    bufferPool.unpin(pageId)
    freeSpaceMap.update(pageId, remainingSpace)
    return RID(pageId, slotId)
}
```

### 7.2.2 Lettura
`read(rid)` estrae offset e lunghezza dallo slot directory e deserializza la tupla con `RowDecoder`.

---

## 7.3 Free Space Map

`FreeSpaceMap` mantiene una struttura di priorità (heap) con tuple `(pageId, freeBytes)`. Algoritmo:
1. Inserimento: se la pagina ha spazio sufficiente, rimane nel heap.
2. Se lo spazio scende sotto soglia, la pagina è rimossa finché il vacuum non recupera spazio.

---

## 7.4 Tombstone e vacuum

- **Tombstone**: uno slot marcato come libero ma non ancora compattato; conserva l'offset per eventuale undo.
- **Vacuum**: rimuove i tombstone e compattata la pagina.

Diagramma del processo vacuum:
```
[Pagina con tombstone] → copy live tuples → rebuild slot directory → update FreeSpaceMap
```

---

## 7.5 Integrazione con WAL e MVCC

Ogni operazione heap produce record WAL appropriati (`WALHeapInsertRecord`, `WALHeapDeleteRecord`). Durante undo, vengono generati CLR che ripristinano lo stato della pagina. MVCC utilizza i tombstone per esporre versioni precedenti alle letture.

---

## 7.6 Laboratorio

1. Inserire 1000 tuple e registrare dimensione del file.
2. Cancellarne 500; osservare `FreeSpaceMap` con `\heap stats`.
3. Eseguire `\vacuum accounts` e confrontare dimensione/n° tombstone.

---

## 7.7 Collegamenti
- **Capitolo 6**: buffer pool (pin/unpin).
- **Capitolo 8**: B+Tree utilizza heap per memorizzare rid.
- Appendice B: parametri di configurazione dello storage.

