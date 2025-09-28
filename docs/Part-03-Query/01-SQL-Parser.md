# Capitolo 10 — Parsing SQL e Costruzione AST

## 10.1 Lexer e tokenizzazione
- `SQLLexer` (`Sources/ColibriCore/SQL/Parser/SQLLexer.swift`).
- Regole e gestione errori.

## 10.2 Parser
- `SQLParser`, funzioni `parseSelect`, `parseInsert`, `parseUpdate`, `parseDelete`.
- AST: `SQLStatement`, `SQLExpression`.

## 10.3 Validazione sintattica
- Gestione di alias, qualificatori, funzioni.
- Errori sintetici e diagnostica.

## 10.4 Estensioni future
- DDL avanzato, window functions, CTE.
