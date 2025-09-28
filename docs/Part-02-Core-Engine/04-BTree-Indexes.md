# Capitolo 8 — Indici B+Tree e Strutture Secondarie

## 8.1 Motivazioni
- Complessità di ricerca log(N), ottimizzazione per range scan.
- Differenze rispetto ad altri indici (hash, bitmap).

## 8.2 `FileBPlusTreeIndex`
- File sorgenti: `Sources/ColibriCore/Index/BPlusTree`.
- Header (`Header` struct) con `checkpointLSN`.
- Pagine interne/foglia, record di chiave (`KeyBytes`).

## 8.3 Operazioni principali
- `insert(key:rid:)`, `remove(key:rid:)`, `search`.
- Gestione split/merge (`splitNode`, `mergeNode`).

## 8.4 Logging
- Integrazione con WAL (`logIndexInsert/Delete`).
- Checkpoint specifici dell’indice (`checkpointIndex`).

## 8.5 Statistiche e analisi costi
- Raccolta metriche (`IndexStatistics`).
- Uso nel planner (`CostEstimator`).

## 8.6 Esercitazioni
- Creare un indice, inserirvi record, verificare piani di query.
