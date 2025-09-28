# Capitolo 2 — Algebra Relazionale e SQL in ColibrìDB

## 2.1 Algebra relazionale formale
Partiamo dalla definizione classica delle operazioni:
- **Selezione** σᵖ(R): filtraggio delle tuple che soddisfano il predicato p.
- **Proiezione** πₐ(R): estrazione di sottoinsiemi di attributi.
- **Join** R ⋈ S: combinazione basata su condizioni di uguaglianza o generiche.
- **Unione** R ∪ S e differenza R − S: operazioni insiemistiche.
- **Rinominazione** ρ: necessaria per distinguere attributi omonimi.

Discussione sulle proprietà algebriche (commutatività, associatività) e loro impatto sugli algoritmi di ottimizzazione.

## 2.2 AST e rappresentazione nel codice
Il parser SQL produce un albero sintattico (`SQLStatement`). Ad esempio, la clausola SELECT è modellata da `SQLSelect` con campi `projections`, `from`, `where`, `groupBy`, `orderBy`. Nel file `Sources/ColibriCore/SQL/AST/SQLSelect.swift` possiamo osservare la definizione.

## 2.3 Dal SQL al piano logico
`LogicalPlanner.plan(select:)` traduce l'AST in un grafico di operatori. Analizziamo passo per passo la funzione:
1. Costruzione di `LogicalPlan.scan(table:)` per ogni sorgente.
2. Applicazione di `LogicalPlan.filter(predicate:)` per la clausola WHERE.
3. Configurazione di proiezioni e aggregazioni.

Riportiamo estratti del codice con annotazioni per ciascun passaggio.

## 2.4 Analisi semantica
Il planner effettua controlli di coerenza:
- Risoluzione dei nomi di tabelle/colonne mediante `CatalogLookup`.
- Verifica di compatibilità dei tipi con `TypeChecker`.
- Costruzione di `BindingContext` per supportare alias e scoping.

## 2.5 Regole di ottimizzazione
Descriviamo il motore di riscrittura basato su regole (`RuleEngine`). Esempi:
- Pushdown di selezioni: riscritte vicino alle scansioni per ridurre cardinalità.
- Eliminazione proiezioni ridondanti.
- Simbolicamente, σᵖ(πₐ(R)) → πₐ(σᵖ(R)).

Colleghiamo queste trasformazioni ai metodi `applySelectionPushdown` ecc.

## 2.6 Piano fisico preliminare
Il capitolo prepara la transizione al piano fisico. Introduciamo i costi simbolici: costo di I/O per tabelle (T_pagine), costo CPU per record. Questi concetti saranno formalizzati nel Capitolo 12.

## 2.7 Laboratorio
- Eseguire `SELECT balance FROM accounts WHERE id = 42`.
- Utilizzare la modalità debug del planner (`--explain` da implementare) per stampare piani logici.
- Annotare come la selezione viene pushdown e come vengono risolti i binding.

## 2.8 Collegamenti
Questo capitolo fornisce le basi per comprendere la pipeline descritta in Parte III. Le funzioni `LogicalPlan`, `PhysicalPlan` e `Executor` saranno riprese e studiate nel dettaglio nei capitoli successivi.
