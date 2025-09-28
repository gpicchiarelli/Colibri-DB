# Capitolo 12 — Piano Fisico e Cost-Based Optimization

## 12.1 Dal piano logico al fisico
- `PhysicalPlanner` (`Sources/ColibriCore/Planner/PhysicalPlanner.swift`).
- `PhysicalPlan` e operatori concreti.

## 12.2 Stime dei costi
- `CostEstimator`, uso di statistiche (`StatisticsManager`).
- Metriche: cardinalità, selettività, I/O.

## 12.3 Scelta dei join
- Nested Loop, Hash Join, Merge Join (stato implementazione/roadmap).
- Heuristics vs cost-based.

## 12.4 Esempi
- Piano per query con join e filtraggio.
- Output con `EXPLAIN` (funzione da implementare).
