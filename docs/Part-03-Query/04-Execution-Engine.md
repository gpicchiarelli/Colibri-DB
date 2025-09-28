# Capitolo 13 — Motore di Esecuzione e Iteratori

## 13.1 Architettura del runtime
- `Executor` (`Sources/ColibriCore/Query/Executor.swift`).
- Interfaccia `ExecutionOperator` e metodo `next()`.

## 13.2 Operator catalog
- `TableScanOperator`, `IndexScanOperator`, `ProjectionOperator`, `FilterOperator`, `JoinOperator`, `AggregateOperator`.
- Analisi funzione per funzione (fetch tuple, gestione buffer locale, interazione con MVCC).

## 13.3 Valutazione espressioni
- `ExpressionEvaluator` (`Sources/ColibriCore/Query/Expressions`).
- Tipo dinamico `Value` e coercizioni.

## 13.4 Materializzazione risultati
- Strategie: streaming vs materialized.
- Cursoring per il server.

## 13.5 Strumenti di debug
- Modalità tracing, logging temporaneo.
- Metriche d’esecuzione.
