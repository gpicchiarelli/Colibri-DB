# Capitolo 17 — Statistiche e Ottimizzazione Cost-Based

## 17.1 Tipologie di statistiche
- `StatisticsManager`, `TableStatistics`, `ColumnStatistics`.
- Metriche: cardinalità, istogrammi, NDV.

## 17.2 Raccolta e aggiornamento
- `analyzeTable`, `StatisticsCollector`.
- Trigger su `INSERT/UPDATE/DELETE`.

## 17.3 Uso nel planner
- `CostEstimator` e funzioni di stima.
- Influenza sulla scelta dei piani.

## 17.4 Persistenza
- Integrazione con `SystemCatalog.registerStatistic`.
- Checkpoint e backup.

## 17.5 Roadmap
- Sampling adattivo, statistiche multi-colonna, machine learning.
