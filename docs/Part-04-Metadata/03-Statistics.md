# Capitolo 17 — Statistiche e Ottimizzazione Cost-Based

## 17.1 Teoria delle statistiche
Le statistiche sono fondamentali per stimare costi e cardinalità. Introduciamo concetti di distribuzione di frequenza, selettività, cardinalità.

## 17.2 Implementazione
`StatisticsManager` gestisce raccolta e persistenza delle statistiche. Funzioni chiave:
- `gatherTableStats`
- `gatherColumnStats`
- `updateStatsOnInsert/Delete`

## 17.3 Integrazione con il planner
Il `CostEstimator` utilizza statistiche per valutare piani. Analizziamo l'interfaccia `StatisticsProvider` e i metodi `estimateRowCount`, `estimateSelectivity`.

## 17.4 Persistenza
`SystemCatalog.registerStatistic` salva statistiche in `system_catalog.json`. Spieghiamo formati e update.

## 17.5 Roadmap
- Istogrammi avanzati, statistiche multi-colonna.
- Sampling adattivo.

## 17.6 Laboratorio
- Eseguire `ANALYZE TABLE` (comando CLI) e osservare statistiche aggiornate.
- Confrontare piani di query prima/dopo.
