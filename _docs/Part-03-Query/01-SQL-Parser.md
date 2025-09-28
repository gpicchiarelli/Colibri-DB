---
layout: page
title: SQL Parser
description: Capitolo 13 - Parser SQL in ColibrìDB
---

# Capitolo 10 — Parsing SQL e Costruzione AST

> **Obiettivo**: trasformare una stringa SQL in una rappresentazione strutturata (AST) con un approccio formale. Useremo notazione BNF, diagrammi, tabelle ed esempi pratici.

---

## 10.1 Grammatica SQL semplificata

### 10.1.1 BNF
```
<statement> ::= <select> | <insert> | <update> | <delete> | <create> | <drop>
<select> ::= SELECT <projection> FROM <from> [WHERE <predicate>] [GROUP BY <columns>] [ORDER BY <columns>]
<projection> ::= * | <expression> {, <expression>}
<from> ::= <table> {JOIN <table> ON <predicate>}
```

Tabella sintesi (estratto):

| Non terminale | Espansione |
|---------------|------------|
| `<table>` | `<identifier>` |
| `<predicate>` | `<expression> <operator> <expression>` |
| `<expression>` | `<term> {(+|-) <term>}` |

### 10.1.2 Tokenizzazione
`SQLLexer` spezza la stringa in token: keyword, identificatori, letterali, simboli. Il metodo `tokenize()` scorre l'input una volta (O(n)).

---

## 10.2 Architettura del parser

Diagramma di chiamate (semplificato):
```
SQLParser.parse(sql)
  ├─ SQLLexer.tokenize()
  └─ SQLParser(tokens)
       └─ parseStatement()
            ├─ parseSelectStatement()
            ├─ parseInsertStatement()
            ├─ parseUpdateStatement()
            └─ parseDeleteStatement()
```

### 10.2.1 Gestione stati
`SQLParser` mantiene `tokens` e `position`. Funzione `currentToken()` restituisce il token corrente, `consume(expected)` avanza e verifica.

---

## 10.3 Esempio guidato

Consideriamo `SELECT balance FROM accounts WHERE id = 42`.

1. **Token**: `SELECT`, `IDENT(balance)`, `FROM`, `IDENT(accounts)`, `WHERE`, `IDENT(id)`, `OP(=)`, `NUM(42)`.
2. **Parsing**: `parseSelectStatement` costruisce `SQLSelect` con:
   - `projections = [.column("balance")]`
   - `from = [.table("accounts")]`
   - `where = .binary(.column("id"), .equals, .literal(42))`

Tabella AST (estratto):

| Campo | Valore |
|-------|--------|
| `SQLSelect.projections` | `[SelectColumn(expression: .column("balance"))]` |
| `SQLSelect.from` | `[SQLTableReference(name: "accounts")]` |
| `SQLSelect.where` | `SQLExpression.binary(...)` |

---

## 10.4 Gestione DDL
`parseCreateTableStatement()` riconosce colonne e vincoli. Diagramma di flusso:
```
CREATE TABLE
    ├─ parseIdentifier() (nome tabella)
    └─ parseColumnDefinition() / parseConstraint()
```

Vincoli gestiti:
- `PRIMARY KEY`
- `FOREIGN KEY`
- `UNIQUE`
- `CHECK`

### 10.4.1 Funzione `parseColumnDefinition`
Analizza attributi (tipo, nullable, default, primary, unique). Restituisce `SQLColumnDefinition`.

---

## 10.5 Gestione espressioni

`parseExpression()` implementa un parser a precedenza. Struttura tipica:
- `parseOr` → `parseAnd` → `parseComparison` → `parseTerm` → `parseFactor`.

Tabella operatori e precedenze:

| Livello | Operatori |
|---------|-----------|
| 1 (alto) | `*`, `/` |
| 2 | `+`, `-` |
| 3 | `=`, `<`, `>` |
| 4 (basso) | `AND`, `OR` |

---

## 10.6 Error handling

Il parser solleva `SQLParseError` con descrizioni precise. Esempio: se appare un token inatteso, `parseStatement()` lancia `unexpectedToken("Expected statement keyword")`.

### 10.6.1 Schema di diagnosi
```
if token ≠ atteso:
    throw SQLParseError.expectedToken(atteso, actual: tokenDescription(token))
```

---

## 10.7 Laboratorio

1. Avviare REPL Swift (`swift`), importare `ColibriCore`, eseguire:
   ```swift
   let ast = try SQLParser.parse("SELECT 1 + 2")
   print(ast)
   ```
2. Provare statement errati per vedere gli errori (es. `SELECT FROM`).
3. Serializzare l'AST in JSON (creare funzione `encodeAST` per debugging).

---

## 10.8 Collegamenti
- **Capitolo 11**: il piano logico usa l'AST come input.
- **Appendice Glossario**: definizioni di AST, parser, token.

