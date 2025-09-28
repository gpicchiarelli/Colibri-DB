---
layout: page
title: Roadmap del Progetto
description: Roadmap e piani futuri per Colibrì DB
---

# Capitolo 27 — Roadmap Tecnica

> **Obiettivo**: delineare le evoluzioni pianificate per Colibrì DB, collocandole in una visione strategica di ricerca e sviluppo.

---

## 27.1 Replicazione e alta disponibilità

### 27.1.1 Log shipping
- Replica WAL verso nodi follower.
- Follower applicano REDO e diventano read-only.

### 27.1.2 Failover
- Elezione leader (consensus: Raft o Paxos in roadmap).
- Monitoraggio heartbeat e switchover.

---

## 27.2 Query distribuite

- Sharding orizzontale (partitioning per chiavi).
- Coordinatore che invia subquery a nodi shard.
- Federation verso sorgenti esterne.

Diagramma idea:
```
Coordinator
 ├─ Shard 1
 ├─ Shard 2
 └─ External Source
```

---

## 27.3 Ottimizzazione avanzata

- Planner cost-based completo con dynamic programming (Selinger-style).
- Statistiche multi-dimensionali e adaptive query processing.
- Integrazione con machine learning per stime di costo.

---

## 27.4 Sicurezza enterprise

- TLS end-to-end.
- Autenticazione multi-fattore.
- Row-level security, policy-based access control.

---

## 27.5 Hardware specializzato

- SIMD per operatori vettorizzati.
- GPU per workload analitici.
- Ottimizzazione per Apple Silicon (NEON) e CPU server.

---

## 27.6 Roadmap temporale (indicativa)

| Fase | Obiettivi |
|------|-----------|
| Beta | Planner cost-based, MVCC completo |
| GA | Replicazione, monitoring avanzato |
| Ricerca | Query distribuite, ML-based optimization |

