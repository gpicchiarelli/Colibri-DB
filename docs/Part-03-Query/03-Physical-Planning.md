# Capitolo 12 — Piano Fisico e Ottimizzazione Basata sui Costi

## 12.1 Scopo del piano fisico
Il piano fisico decide gli algoritmi concreti per implementare ogni operatore logico. Introduciamo le metriche di costo (tempo, I/O, memoria) e la funzione obiettivo: minimizzare il costo atteso.

## 12.2 `PhysicalPlanner`
- `buildPhysicalPlan(logical:)`: visita il piano logico e crea operatori fisici.
- `chooseJoinAlgorithm`: decide tra nested loop, hash join, merge join (in roadmap).
- `chooseScan`: selezione tra full scan e index scan.

## 12.3 Stima dei costi
`CostEstimator` utilizza statistiche dal catalogo. Spieghiamo le formule di stima di cardinalità (`cardinality * selectivity`), costo I/O per pagina (`pages * pageCost`), costo CPU.

## 12.4 Pianificazione dinamica
Discussione su possibili ottimizzazioni future: dynamic programming (Selinger), memoization, branch-and-bound.

## 12.5 Laboratorio
- Eseguire query `EXPLAIN` (feature da implementare) per osservare piani fisici.
- Cambiare statistiche nel catalogo e verificare l'impatto sul piano scelto.
