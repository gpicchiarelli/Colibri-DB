# Capitolo 14 — Funzionalità Avanzate di Query

## 14.1 Aggregazioni
`AggregateOperator` implementa funzioni come `SUM`, `COUNT`, `AVG`. Spieghiamo schema per aggregatori parziali e finali. Il planner inserisce `GroupByOperator` con hash table interna.

## 14.2 Funzioni scalari
`FunctionRegistry` mappa nomi a implementazioni Swift. Analizziamo come aggiungere funzioni user-defined.

## 14.3 Ordinamento e limit
`SortOperator` utilizza un algoritmo sort with spill-to-disk. `TopKOperator` esegue limit/offset.

## 14.4 Roadmap
- Window functions: definiremo `WindowOperator` (in sviluppo).
- CTE e subquery correlate.
- Presto integration con `EXPLAIN ANALYZE`.
