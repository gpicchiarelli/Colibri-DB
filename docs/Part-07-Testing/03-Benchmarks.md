# Capitolo 26 — Benchmarking e Performance Engineering

## 26.1 Suite di benchmark
- `Sources/benchmarks` e scenari (`Benchmarks+Heap`, `Benchmarks+WAL`).
- Parametrizzazione, durata, output.

## 26.2 Metriche chiave
- Throughput, latenza, IOPS, Page Flush rate.
- Metriche riportate in `WALMetrics`, `BufferPoolStats`.

## 26.3 Esecuzione benchmark
- Comando `swift run benchmarks --scenario`.
- Raccolta dati, esportazione grafici.

## 26.4 Tuning e interpretazione
- Configurazioni `DBConfig`, `ServerConfig`.
- Analisi dei risultati, regressioni, profiling.
