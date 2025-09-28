---
layout: page
title: Benchmarks
description: Capitolo 26 - Benchmark e performance
---

# Capitolo 26 — Benchmarking e Performance Engineering

> **Obiettivo**: illustrare come misurare le prestazioni di Colibrì DB in modo rigoroso, definendo scenari, metriche e procedure di analisi.

---

## 26.1 Suite di benchmark

`Sources/benchmarks` contiene scenari predefiniti:
- `Benchmarks+Heap`: test su inserimenti/letture heap.
- `Benchmarks+WAL`: misurazioni throughput WAL.
- `Benchmarks+Transactions`: carichi transazionali.
- `Benchmarks+Indexes`: operazioni su B+Tree.

Comando generale:
```bash
swift run benchmarks --scenario wal-throughput --duration 30s
```

---

## 26.2 Metriche chiave

| Metrica | Descrizione | Fonte |
|---------|-------------|-------|
| `appendsPerSecond` | Append WAL al secondo | `WALMetrics` |
| `bytesPerSecond` | Volume log scritto | `WALMetrics` |
| `fsyncsPerSecond` | Operazioni fsync | `WALMetrics` |
| `p95CommitLatencyMs` | Latenza commit 95° percentile | `WALMetrics` |
| `queueDepth` | Record in coda per group commit | `WALMetrics` |
| `compressionRatio` | Efficienza compressione WAL | `WALMetrics` |

---

## 26.3 Metodologia

1. Definire baseline (hardware, configurazione DB).
2. Riscaldare il sistema (warm-up).
3. Eseguire benchmark multipli per ridurre variabilità.
4. Registrare output e generare grafici.

---

## 26.4 Analisi e tuning

- Regolare `DBConfig` (es. `walGroupCommitMs`).
- Ottimizzare buffer pool e page size.
- Monitorare saturazione I/O e CPU.

---

## 26.5 Laboratorio

1. Eseguire `swift run benchmarks --scenario wal-throughput`.
2. Modificare configurazione (es. `walDurabilityMode = .grouped`) e confrontare.
3. Documentare risultati in report `.md` o `.csv`.

---

## 26.6 Collegamenti
- **Parte VI**: strumenti DevOps per raccolta metriche.
- **Parte VIII**: roadmap su ottimizzazioni hardware.

