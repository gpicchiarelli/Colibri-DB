---
layout: page
title: Algebra SQL
description: Capitolo 2 - Algebra relazionale e SQL
---

# Capitolo 2 — Algebra Relazionale e SQL in ColibrìDB

> **Obiettivo**: derivare la pipeline di trasformazione SQL → AST → Piano Logico, integrando concetti di algebra relazionale, schemi grafici e riferimenti al codice.

---

## 2.1 Algebra relazionale formale

Schema riassuntivo delle operazioni di base:

| Operatore | Simbolo | Significato | Equivalente nel codice |
|-----------|---------|-------------|------------------------|
| Selezione | \( \sigma_{p}(R) \) | Filtra tuple | `LogicalPlan.filter(predicate:)`
| Proiezione | \( \pi_{A}(R) \) | Seleziona attributi | `LogicalPlan.project(columns:)`
| Join | \( R \Join S \) | Combina relazioni | `LogicalPlan.join(type:on:)`
| Unione | \( R \cup S \) | Unisce relazioni | `LogicalPlan.unionAll`
| Differenza | \( R - S \) | Sottrae relazioni | da implementare |

Diagramma concettuale (ASCII):
```
SQL Query
   │
   ▼
Algebra Relazionale (LogicalPlan)
   │
   ▼
Physical Plan → Executor
```

---

## 2.2 Parsing SQL

### 2.2.1 Lexer
`SQLLexer` converte una stringa in token. Ogni token è rappresentato da `SQLToken` (keyword, identificatore, numero, stringa, simbolo). Il metodo `tokenize()` scorre l'input O(n) e solleva `SQLLexerError` in caso di caratteri non riconosciuti.

### 2.2.2 Parser
Il parser ricorsivo discendente (`SQLParser`) implementa regole come:
- `parseSelectStatement`
- `parseInsertStatement`
- `parseCreateTableStatement`

Ogni funzione consuma token e costruisce l'AST. Diagramma UML semplificato:
```
SQLParser
 ├─ parseStatement()
 │   ├─ parseSelectStatement()
 │   ├─ parseInsertStatement()
 │   └─ ...
 └─ parseExpression()
```

---

## 2.3 Costruzione dell'AST

Esempio: `SELECT balance FROM accounts WHERE id = 42`

1. Lexer genera token `SELECT`, `IDENT(balance)`, `FROM`, ...
2. Parser produce AST `SQLSelect` con campi `projections`, `from`, `where`.
3. `SQLSelect` viene trasformato in `LogicalPlan` dal planner.

Tabella degli elementi AST principali:

| Nodo AST | Descrizione | File sorgente |
|----------|-------------|----------------|
| `SQLSelect` | Query SELECT completa | `SQLParser.swift` |
| `SQLExpression` | Albero di espressioni | `SQLParser.swift` |
| `SQLJoin` | Clausole JOIN | `SQLParser.swift` |

---

## 2.4 Pianificazione logica

`LogicalPlanner` converte AST in operatori algebraici:

```swift
func plan(select stmt: SQLSelect) -> LogicalPlan {
    let source = planFromClause(stmt.from)
    let filtered = applyWhere(stmt.where, to: source)
    let projected = applyProjections(stmt.projections, to: filtered)
    return projected
}
```

- `planFromClause` genera `LogicalPlan.scan`.
- `applyWhere` produce `LogicalPlan.filter`.
- `applyProjections` costruisce `LogicalPlan.project`.

---

## 2.5 Ottimizzazioni logiche

`RuleEngine` applica regole di riscrittura. Esempio di pushdown selezione:

```
Input:  π_{A}(σ_{p}(R))
Output: σ_{p}(π_{A}(R))
```

Nel codice la regola è implementata come:
- Condizione: `LogicalPlan.project` figlio `LogicalPlan.filter`.
- Azione: scambiare ordine e aggiornare colonne.

---

## 2.6 Output del planner

`LogicalPlan.describe()` restituisce una rappresentazione ad albero. Esempio:
```
Project [balance]
└─ Filter [id = 42]
   └─ TableScan [accounts]
```

Questo output conferma la sequenza `π` → `σ` → `Scan`.

---

## 2.7 Laboratorio: dal SQL al piano logico

1. `swift run coldb --explain "SELECT balance FROM accounts WHERE id = 42"`
2. Analizzare l'output di `LogicalPlan.describe()`.
3. Modificare la query (aggiungere join, aggregazioni) e osservare le riscritture applicate.

---

## 2.8 Collegamenti
- **Capitolo 12**: prosegue la trasformazione in piano fisico (cost-based).
- **Capitolo 13**: implementa l'esecuzione iteratore-based degli operatori logici.

