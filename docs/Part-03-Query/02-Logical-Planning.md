# Capitolo 11 — Piano Logico e Analisi Semantica

## 11.1 Obiettivo del piano logico
Il piano logico rappresenta un'espressione relazionale normalizzata. Mostriamo come ogni AST venga convertito in una combinazione di operatori (`Scan`, `Filter`, `Project`, `Join`, `Aggregate`).

## 11.2 `LogicalPlanner`
Analizziamo funzione per funzione:
- `plan(select:)` — costruzione pipeline da clausole SELECT.
- `plan(insert:)`, `plan(update:)`, `plan(delete:)` — operazioni DML.
- `bindTables`, `bindColumns` — risoluzione di nomi usando `CatalogManager`.

## 11.3 Binding e type checking
Descriviamo `BindingContext` e `TypeChecker`. Ogni espressione viene annotata con il tipo risultante, prevenendo errori (es. somma tra INT e STRING).

## 11.4 Regole logiche
`RuleEngine` applica trasformazioni:
- `SelectionPushdownRule`
- `ProjectionSimplificationRule`
- `JoinReorderingRule`

Per ogni regola spieghiamo la condizione di applicabilità e l'effetto sul piano.

## 11.5 Output e debug
`LogicalPlan.describe()` restituisce rappresentazione testuale. Suggeriamo come usare questa funzione per comprendere le trasformazioni.

## 11.6 Laboratorio
- Abilitare logging del planner (modifica config).
- Eseguire query con join e osservare le trasformazioni.
