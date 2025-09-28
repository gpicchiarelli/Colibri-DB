---
layout: page
title: Monitoring e DevOps
description: Capitolo 23 - Monitoring e operazioni DevOps
---

# Capitolo 23 — Monitoring, Build e DevOps

> **Obiettivo**: fornire una guida sistematica per integrare Colibrì DB nei flussi DevOps, dalla build alla produzione, includendo monitoring e backup.

---

## 23.1 Pipeline di build

- `swift build`: compila il progetto.
- `swift test`: esegue suite di test.
- Integrazione con CI (GitHub Actions, GitLab CI): script che automano build/test.

Schema pipeline:
```
Commit → CI Build → Unit Tests → Integration Tests → Artifacts
```

---

## 23.2 Deployment

Strategie tipiche:
- macOS: LaunchDaemon (`plist` in `Resources/`).
- Linux: systemd unit.
- Containerizzazione (Docker) in roadmap.

Tabella parametri importanti:

| Parametro | Descrizione |
|-----------|-------------|
| `dataDir` | Directory dati (WAL, catalogo) |
| `logDir` | File log |
| `checkpointInterval` | Frequenza checkpoint |

---

## 23.3 Monitoring

Metriche disponibili via `Telemetry` e `Metrics`:
- WAL throughput.
- Latenza commit (p95).
- Depth della coda group commit.

Roadmap: esportazione Prometheus, dashboard Grafana.

---

## 23.4 Backup e ripristino

Procedure consigliate:
1. Eseguire `\checkpoint` per garantire stato consistente.
2. Copiare `data/` (WAL, catalogo, checkpoint).
3. Verificare integrità con script di validazione.

Ripristino: ripristinare directory e avviare server (ARIES riprodurrà eventuali operazioni incomplete).

---

## 23.5 Laboratorio

1. Configurare un job CI che esegua `swift build` e `swift test`.
2. Abilitare logging rotativo e monitorarlo.
3. Simulare backup e ripristino su ambiente di staging.

---

## 23.6 Collegamenti
- **Parte VII**: test/benchmark per la pipeline di qualità.
- **Appendice B**: configurazioni per ambienti di deploy.

