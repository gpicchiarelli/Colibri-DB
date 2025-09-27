04 — Planner & Executor
=======================

Panoramica
----------
Il planner costruisce piani Volcano a partire da richieste logiche (`QueryRequest`). Gli operatori espongono un'interfaccia a iteratore; il cost model seleziona tra access path e strategie di join.

File principali
---------------
- `Sources/ColibriCore/Planner/QueryPlanner.swift`
- `Sources/ColibriCore/Planner/PlanOperator.swift`
- `Sources/ColibriCore/Planner/Operators.swift`
- `Sources/ColibriCore/Database/Database+Planner.swift`

Access path e join
------------------
- Access path: `TableScanOperator` vs `IndexScanOperator` su indici candidati; scelta via `CostModel`.
- Join: `HashJoinOperator` e `MergeJoinOperator`; selezione basata su somma di costi CPU+IO.

Parallelismo e limiti
---------------------
- `ParallelMapOperator` permette parallelismo per operatori mappabili.
- `LimitOperator` applica limite a valle.

Esecuzione
----------
`Database.executeQuery(_:)` orchestra pianificazione, materializzazione e caching opzionale del risultato (materialized view cache per chiave).

