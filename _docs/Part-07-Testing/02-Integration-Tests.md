---
layout: page
title: Integration Tests
description: Capitolo 25 - Test di integrazione
---

# Capitolo 25 — Test di Integrazione e End-to-End

> **Obiettivo**: descrivere i test che coprono l'intera pipeline (parser → planner → executor → server), includendo scenari di crash e concorrenza.

---

## 25.1 Struttura

Test di integrazione assicurano che il sistema funzioni come un tutto. Elementi:
- Setup database.
- Esecuzione query tramite CLI o API.
- Confronto con risultati attesi.

---

## 25.2 Scenari principali

| Scenario | Descrizione |
|----------|-------------|
| Pipeline SQL | `SELECT` complessi con join/aggregate |
| DDL+DML | Sequenza `CREATE` → `INSERT` → `SELECT` |
| Crash recovery | Simulazione crash, verifica recovery |
| Concorrenza | Transazioni parallele con MVCC |

---

## 25.3 Strumenti

- Script shell (`Tests/Scripts`) per orchestrare server/CLI.
- `DevCLI+Testing` per generare workload e assert.

Esempio di script (pseudo):
```bash
start_server
coldb --exec "CREATE TABLE..."
run_workload
kill_server
restart_server
verify_state
```

---

## 25.4 Laboratorio

1. Utilizzare `coldb-dev \test recovery`.
2. Eseguire uno script personalizzato che crea tabelle, inserisce dati, induce crash e verifica risultati.

---

## 25.5 Collegamenti
- **Capitolo 5**: understanding ARIES aiuta a interpretare test di recovery.
- **Parte VIII**: roadmap include test su replicazione e distribuzione.

