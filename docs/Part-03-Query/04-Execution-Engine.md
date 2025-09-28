# Capitolo 13 — Motore di Esecuzione e Iteratori

## 13.1 Modello iteratore
L'esecuzione utilizza un modello iteratore: ogni operatore espone `next()` che restituisce tuple una alla volta. Spieghiamo la differenza tra push e pull model, e i vantaggi in termini di pipeline e memoria.

## 13.2 Operatori principali
- `TableScanOperator`: legge tuple da `FileHeapTable`.
- `IndexScanOperator`: naviga il B+Tree.
- `FilterOperator`: applica predicati.
- `ProjectionOperator`: ricalcola espressioni.
- `JoinOperator`: implementa nested loop (hash join in roadmap).
- `AggregateOperator`: calcola funzioni di aggregazione.

Per ciascuno analizziamo le funzioni e le strutture interne.

## 13.3 Valutazione espressioni
`ExpressionEvaluator` valuta operazioni aritmetiche, logiche, funzioni built-in. Mostriamo come vengono convertite in closure Swift e discussiamo le ottimizzazioni (memoization, short-circuit).

## 13.4 Materializzazione
Il server può materializzare risultati in blocchi per trasferimento al client. Descriviamo il protocollo `fetch` e l'uso di `ResultBuffer`.

## 13.5 Laboratorio
- Eseguire query step-by-step usando un debugger o log.
- Profilare CPU e memoria durante diversi piani.
