# Capitolo 11 — Piano Logico e Analisi Semantica

## 11.1 Generazione del piano logico
- `LogicalPlanner` (`Sources/ColibriCore/Planner/LogicalPlanner.swift`).
- Struttura `LogicalPlan`, pattern enum.

## 11.2 Analisi semantica
- Risoluzione nomi (`CatalogLookup`).
- Verifica vincoli, tipi, compatibilità.

## 11.3 Ottimizzazioni logiche
- Regole di semplificazione (`LogicalRule`, `RuleEngine`).
- Esempi: pushdown selezione/proiezione, eliminazione join ridondanti.

## 11.4 Output
- Serializzazione del piano per debugging.
- Rimandi al capitolo successivo per il piano fisico.
