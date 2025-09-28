# Capitolo 26 — Benchmarking e Performance Engineering

## 26.1 Suite
`swift run benchmarks` esegue scenari: WAL throughput, heap operations, planner performance.

## 26.2 Metriche
Elenco metriche chiave: `appendsPerSecond`, `bytesPerSecond`, `fsyncsPerSecond`, `p95CommitLatencyMs`, `queueDepth`, `compressionRatio`.

## 26.3 Metodologia
- Definizione di baseline.
- Ripetibilità (seme random, configurazione hardware).
- Analisi regressioni.

## 26.4 Ottimizzazione
Strategie per migliorare performance: tuning `DBConfig`, parallelismo, caching, compressione.
