03 — SQL: Lexer, Parser e AST
=============================

Obiettivi
---------
- Tokenizzare input SQL in modo robusto con supporto a commenti, stringhe, numeri e operatori.
- Rappresentare AST tipizzata per DDL/DML e utilità (`EXPLAIN`).
- Offrire una facciata semplice per esecuzione (`SQLQueryInterface`).

Componenti e file principali
----------------------------
- `Sources/ColibriCore/SQL/SQLLexer.swift` — scansione input in `SQLToken`.
- `Sources/ColibriCore/SQL/SQLParser.swift` — parsing in `SQLStatement` tramite funzioni `parse*`.
- `Sources/ColibriCore/SQL/SQLTypes.swift` — definizioni di `SQLStatement`, `SQLExpression`, operatori e strutture correlate.
- `Sources/ColibriCore/SQL/SQLQueryInterface.swift` — smista `SQLStatement` alle operazioni del `Database` o al planner.

Flusso di esecuzione
--------------------
1. `SQLQueryInterface.execute(sql)` → `SQLParser.parse(sql)` produce `SQLStatement`.
2. `executeStatement(_:)` esegue il caso: DDL/DML tramite API del `Database`, `SELECT` via planner (`Database.executeQuery`).
3. `EXPLAIN` delega al planner ma ritorna il piano anziché i dati.

AST e espressioni
------------------
`SQLTypes.swift` modella:
- `SQLStatement` (create/drop table/index, insert/update/delete/select, explain).
- `SQLExpression` (letterali, colonne, operatori unari/binari, funzioni, CASE WHEN).
- `TableReference` (tabelle e join), `OrderByClause`, vincoli (`SQLConstraint`).

Estensibilità
-------------
- Aggiungere nuove parole chiave: aggiornare `SQLLexer.scanIdentifierOrKeyword` e gli enum/branch del parser.
- Nuove espressioni/operazioni: estendere `SQLExpression`/`SQLStatement` e la `executeStatement` nel `SQLQueryInterface`.

