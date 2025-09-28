---
layout: page
title: Statistiche
description: Capitolo 20 - Statistiche e ottimizzazione
---

# Capitolo 17 — Statistiche e Ottimizzazione Cost-Based

> **Obiettivo**: spiegare come ColibrìDB raccoglie e utilizza statistiche su tabelle e colonne per alimentare l'ottimizzatore cost-based, con metodi di analisi e laboratori.

---

## 17.1 Tipologie di statistiche

| Tipo | Contenuto | Uso |
|------|-----------|-----|
| Table statistics | Cardinalità, numero pagine | Stima costi scan |
| Column statistics | Distribuzione, valori distinti | Stima selettività |
| Index statistics | Altezza, fanout | Costi per IndexScan |

`StatisticsManager` gestisce questi dati; `StatisticEntry` nel catalogo persiste in `system_catalog.json`.

---

## 17.2 Raccolta

### 17.2.1 `ANALYZE`
Comando CLI che avvia raccolta tramite `StatisticsManager.gatherTableStats`. Passaggi:
1. Scansione delle pagine.
2. Calcolo sample (se abilitato).
3. Aggiornamento `StatisticEntry`.

### 17.2.2 Aggiornamenti incrementali
Insert/delete possono aggiornare statistiche in-line (`updateStatsOnInsert/Delete`). Roadmap: trigger automatici basati su soglie.

---

## 17.3 Uso nel planner

`CostEstimator` interroga `StatisticsManager` per ricavare cardinalità e selettività.

Formule:
- Selettività predicato: \( s = \frac{1}{\text{NDV}} \) (per uguaglianza su attributo con NDV=numero di valori distinti).
- Cardinalità join: \( |R| \cdot |S| \cdot s_{join} \).

Tabella di mapping:

| Funzione | Input | Output |
|----------|-------|--------|
| `estimateRowCount(table)` | Tabella | Cardinalità |
| `estimateSelectivity(predicate)` | Predicato | Selettività |

---

## 17.4 Persistenza

`SystemCatalog.registerStatistic` salva statistiche con timestamp. File JSON di esempio:
```json
{
  "table": "accounts",
  "kind": "column",
  "column": "balance",
  "stats": {
    "count": 100000,
    "ndv": 95000,
    "min": 0.0,
    "max": 100000.0
  }
}
```

---

## 17.5 Laboratorio

1. Creare dataset (`INSERT` massivi o generatori CLI).
2. Eseguire `ANALYZE accounts;`.
3. Verificare statistiche:
   ```bash
   jq '.statistics[] | select(.table=="accounts")' data/system_catalog.json
   ```
4. Eseguire `--explain SELECT ...` per osservare come il planner utilizza le statistiche.

---

## 17.6 Roadmap

- Istogrammi multi-colonna
- Sampling adattivo e auto-update
- Integrazione con machine learning per stime avanzate

---

## 17.7 Collegamenti
- **Capitolo 12**: cost model.
- **Parte VII**: benchmarking per validare l'efficacia delle statistiche.

