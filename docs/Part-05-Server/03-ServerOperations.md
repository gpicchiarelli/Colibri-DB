# Capitolo 20 — Operazioni Server, Fault Tolerance e Manutenzione

> **Obiettivo**: fornire una guida sistematica alle operazioni quotidiane sul server, spiegando come ColibrìDB assicura fault tolerance, manutenzione e monitoraggio.

---

## 20.1 Configurazione

`ServerConfig` definisce parametri come porta, thread pool, path data. Estratto (schema):
```
{
  "host": "127.0.0.1",
  "port": 54321,
  "maxConnections": 128,
  "logLevel": "info"
}
```

La CLI permette di verificarne lo stato (`coldb-dev \server config`).

---

## 20.2 Gestione errori

`APIHandler` distingue errori di:
- Sintassi SQL → `ERR_SYNTAX`.
- Violazione vincoli → `ERR_CONSTRAINT`.
- Errori interni → `ERR_INTERNAL`.

Ogni errore è loggato e inviato al client con dettagli.

---

## 20.3 Fault tolerance

Grazie al WAL globale, in caso di crash il server esegue `Database.replayGlobalWAL()` all'avvio. Diagramma di recovery:
```
Crash → Riavvio → Replay WAL → Stato consistente
```

---

## 20.4 Manutenzione

Comandi CLI supportati:
- `\checkpoint`: forza checkpoint (aggiorna DPT/ATT, tronca WAL).
- `\vacuum`: compattazione heap.
- `\stats`: collezione/visualizzazione statistiche.

In roadmap: scheduling automatico (cron-like).

---

## 20.5 Monitoraggio

Metriche esposte tramite `Telemetry`:
- Connessioni attive.
- Throughput query/sec.
- Latenza media/p95.

Integrazione futura con Prometheus/Grafana.

---

## 20.6 Procedure operative

| Scenario | Procedura |
|----------|-----------|
| Aggiornamento server | `systemctl stop`, backup, upgrade, `systemctl start` |
| Ripristino crash | Verificare WAL, eseguire `colbd --replay` |
| Analisi performance | Eseguire benchmark (`swift run benchmarks`) |

---

## 20.7 Laboratorio

1. Avviare server e CLI.
2. Eseguire `\checkpoint`, `\vacuum`, `\stats`.
3. Simulare crash e verificare recovery.

---

## 20.8 Collegamenti
- **Parte VII**: testing e benchmarking.
- **Appendice B**: configurazioni e procedure di deploy.

