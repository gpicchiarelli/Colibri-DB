---
layout: page
title: Write-Ahead Logging e Recupero ARIES
description: Capitolo 5 - Sistema WAL di Colibrì DB con recupero ARIES
---

# Capitolo 5 — Write-Ahead Logging e Recupero ARIES

> **Obiettivo**: fornire una trattazione accademica del sistema WAL di Colibrì DB, includendo schemi, pseudocodice, dimostrazioni informali degli invarianti e laboratori riproducibili.

---

## 5.1 Fondamenti teorici

### 5.1.1 Invarianti
1. **Monotonicità LSN**: se `r1` precede `r2` allora `lsn(r1) < lsn(r2)`.
2. **WAL-before-data**: prima che una pagina venga flushata, `pageLSN ≤ flushedLSN`.
3. **Idempotenza**: il REDO applicato due volte produce lo stesso stato.

### 5.1.2 Fasi ARIES
- **Analisi**: ricostruisce ATT e DPT.
- **REDO**: ripete eventi dal `recLSN` minimo.
- **UNDO**: annulla transazioni incomplete usando CLR.

Diagramma ARIES:
```
[Checkpoint] → Analysis → REDO → UNDO → [Fine]
```

---

## 5.2 Implementazione `FileWALManager`

### 5.2.1 Append
Pseudocodice:
```swift
func append(record) {
    lsnLock.lock()
    record.lsn = nextLSN
    nextLSN += 1
    lsnLock.unlock()
    enqueue(record)
    if shouldFlush() { flushPendingRecords() }
}
```

### 5.2.2 Flush
`flushPendingRecords()`:
1. Estrae batch da `pendingRecords`.
2. Ottimizza l'ordine (`GroupCommitOptimizer`).
3. Scrive su file con `writeOptimizedBatch`.
4. Aggiorna `_flushedLSN`.

Schema I/O:
```
Pending Buffer --write--> WAL File --fsync--> Disk
```

---

## 5.3 Checkpoint
`Database.checkpoint()` esegue:
1. `groupCommitSync` (flush WAL).
2. Flush delle tabelle heap (`FileHeapTable.flush`).
3. `FileBPlusTreeIndex.checkpointIndex`.
4. Serializzazione `CheckpointCatalog` (DPT, ATT, `lastDBLSN`).
5. `writeCheckpoint(dpt:att:)` → `WALCheckpointRecord`.

Pseudocodice ridotto:
```swift
let dptArr = dpt.map
let txArr = activeTIDs.map
CheckpointIO.save(...)
wal.writeCheckpoint(dpt: dpt, att: att)
```

---

## 5.4 Recovery `replayGlobalWAL()`

### 5.4.1 Analisi
```
activeTransactionTable = {}
dirtyPageTable = {}
for record in wal.iterate(from: checkpointLSN) {
    aggiorna ATT e DPT in base al tipo di record
}
```

### 5.4.2 REDO
```
for record in wal.iterate(from: recLSNmin) {
    if shouldRedo(record) {
        applyRedoOperation(record)
    }
}
```

`shouldRedo` controlla `pageLSN` per evitare duplicati.

### 5.4.3 UNDO
```
for (txId, lastLSN) in ATT {
    undoTransaction(txId, from: lastLSN)
}
```
`undoTransaction` raccoglie record della transazione e li percorre al contrario generando CLR.

---

## 5.5 Compensating Log Records
`WALCLRRecord` memorizza:
- `undoNextLSN`: prossimo record da annullare.
- `undoneOperationLSN`: record annullato.
- `undoAction`: descrive l'azione inversa (es. `heapInsert`, `indexDelete`).

Durante UNDO, dopo l'applicazione di `undoAction`, il CLR viene scritto nel WAL per garantire idempotenza. In caso di crash durante UNDO, il REDO ripeterà il CLR senza effetti collaterali.

---

## 5.6 Dimostrazione informale di correttezza
1. **Consistenza**: grazie alla monotonicità degli LSN, i record recuperano l'ordine originario.
2. **Durabilità**: `groupCommitSync` garantisce che tutti gli LSN ≤ `flushedLSN` siano su disco.
3. **Atomicità**: transazioni non committate sono presenti in ATT e vengono annullate via UNDO.
4. **Idempotenza**: `shouldRedo` e CLR assicurano che operazioni già applicate non modifichino nuovamente lo stato.

---

## 5.7 Laboratorio guidato

1. **Setup**: avviare il server e inserire dati.
2. **Simulazione crash**: kill del processo durante una transazione.
3. **Recovery**: riavviare, osservare log:
   - `Starting Global WAL Recovery...`
   - `Analysis complete. ATT: ..., DPT: ...`
4. **Verifica**: controllare che solo transazioni committate siano persistite.

Script consigliato (`scripts/recovery_demo.sh` da creare):
```bash
#!/bin/bash
colbd --exec 'BEGIN; INSERT ...;'
kill -9 $(pidof coldb-server)
colbd --exec 'SELECT ...'
```

---

## 5.8 Collegamenti
- `Capitolo 6`: buffer pool, `pageLSN`.
- `Capitolo 9`: MVCC e produzione di CLR nelle operazioni undo.
- Appendice A: definizioni ATT/DPT/LSN.

