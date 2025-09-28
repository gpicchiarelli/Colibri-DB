# Capitolo 2 — Algebra Relazionale e SQL in ColibrìDB

## 2.1 Richiami di algebra relazionale
- Operazioni primitive: selezione, proiezione, join, unione, differenza.
- Formalizzazione matematica e notazione usata nel testo.

## 2.2 Traduzione in operatori Swift
- `LogicalPlan` (`Sources/ColibriCore/Planner/LogicalPlan.swift`).
- `PhysicalPlan` (`Sources/ColibriCore/Planner/PhysicalPlan.swift`).
- Pattern `enum` con casi associati per gli operatori.

## 2.3 Parsing SQL
- `SQLParser` e struttura AST (`Sources/ColibriCore/SQL/Parser`).
- Funzione `parseSelect` e trasformazione in algebra.

## 2.4 Ottimizzazione
- Regole di riscrittura (proiezione spinta, filtri).
- Collegamento con `OptimizerRule` e `RuleEngine`.

## 2.5 Esecuzione
- `Executor` (`Sources/ColibriCore/Query/Executor.swift`).
- Struttura della pipeline: `execute(plan:)`, `next()`.

## 2.6 Esempio completo
- Query `SELECT balance FROM accounts WHERE id = 42`.
- Trace: SQL → AST → Logical Plan → Physical Plan → Iterator.
- Visualizzazioni e stato delle tabelle temporanee.

## 2.7 Collegamenti futuri
- Introduzione al capitolo sulle transazioni e MVCC.
- Estensioni (aggregate, window functions).
