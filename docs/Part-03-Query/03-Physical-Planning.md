# Capitolo 12 — Piano Fisico e Ottimizzazione Basata sui Costi

> **Obiettivo**: tradurre il piano logico in un piano fisico con scelte algoritmiche giustificate da stime di costo, in linea con i modelli del paper Selinger et al. (1979).

---

## 12.1 Dal piano logico al fisico

Il `PhysicalPlanner` percorre il piano logico e istanzia operatori concreti. Ogni operatore fisico è un iteratore (`next()`) che esegue un algoritmo specifico (scan sequenziale, join, sort, etc.).

Diagramma:
```
LogicalPlan → PhysicalPlan → Executor
```

---

## 12.2 Cost model

### 12.2.1 Metriche
- **Cardinalità** (|R|): numero di tuple.
- **Selettività** (s): frazione di tuple che soddisfano un predicato.
- **Costo I/O**: numero di pagine lette/scritte.
- **Costo CPU**: operazioni per tuple.

### 12.2.2 Stima
`CostEstimator` sfrutta statistiche dal catalogo (`StatisticsManager`).

Formula tipica:
\[
\text{cardinalità}(\sigma_p(R)) = s_p \cdot |R|
\]

---

## 12.3 Scelta degli operatori

| Operatore logico | Opzioni fisiche | Strategia |
|------------------|-----------------|-----------|
| Scan | TableScan, IndexScan | Usa index se disponibile e selettività bassa |
| Join | Nested Loop, Hash Join, Merge Join (roadmap) | Se join confluisce su attributi indicizzati, preferire hash |
| Aggregation | Hash Aggregate, Sort Aggregate | Se `GROUP BY` ha cardinalità bassa, usare hash |

---

## 12.4 Algoritmi principali

### 12.4.1 TableScan
Sequenzialmente legge pagine da `FileHeapTable` usando il buffer pool. Costo I/O ≈ numero di pagine della tabella.

### 12.4.2 IndexScan
Naviga un B+Tree. Costo ≈ `height * costPage + selectivity * costTuple`.

### 12.4.3 Nested Loop Join
```
for each tuple r in R:
    for each tuple s in S:
        if condition(r, s) then emit(r ⊕ s)
```

Usato quando una delle relazioni è piccola o c'è un index.

### 12.4.4 Hash Join (roadmap)
Costruisce una hash table sulla relazione più piccola e cerca i match nella relazione più grande.

---

## 12.5 Pseudocodice del planner fisico
```swift
func buildPhysicalPlan(logicalPlan) -> PhysicalPlan {
    switch logicalPlan {
    case .scan(let table):
        if let index = chooseIndex(table) {
            return .indexScan(index)
        }
        return .tableScan(table)
    case .filter(let child, let predicate):
        let c = buildPhysicalPlan(child)
        return .filter(child: c, predicate: predicate)
    case .join(let left, let right, let condition):
        let l = buildPhysicalPlan(left)
        let r = buildPhysicalPlan(right)
        let algorithm = chooseJoinAlgorithm(l, r, condition)
        return .join(algorithm, left: l, right: r, condition: condition)
    //...
    }
}
```

---

## 12.6 Esempio completo

Query: `SELECT a.name, b.balance FROM users a JOIN accounts b ON a.id = b.user_id WHERE b.balance > 1000`.

1. Piano logico: `Join(Filter(Scan(b)), Scan(a))`.
2. Decisioni fisiche:
   - `Scan(b)` → `IndexScan` (se esiste indice su `balance`).
   - `Join` → `HashJoin` (se implementato) altrimenti `NestedLoop`.
3. Piano fisico risultante:
```
Project
└─ Join (Hash)
   ├─ IndexScan [accounts]
   └─ TableScan [users]
```

---

## 12.7 Laboratorio

1. Aggiornare statistiche: `ANALYZE accounts;`
2. Eseguire `--explain` per osservare il piano fisico.
3. Modificare le statistiche (es. `UPDATE statistics ...`) e osservare come cambia la scelta del piano.

---

## 12.8 Collegamenti
- **Capitolo 26**: benchmarking per validare piani.
- **Parte IV**: statistiche alimentano il cost model.

