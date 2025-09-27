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

Tokenizzazione in dettaglio
---------------------------
Il lexer percorre il testo carattere per carattere, gestendo spazi bianchi, commenti (linea `--` e blocco `/* ... */`), stringhe con apici singoli (con escape), numeri interi e floating, identificatori e parole chiave (case-insensitive dove previsto). Gli **operatori** (`=`, `!=`, `<`, `<=`, `>`, `>=`, `+`, `-`, `*`, `/`, `%`) e la **punteggiatura** (virgole, parentesi) vengono riconosciuti atomicamente per evitare ambiguità (`<=` non viene spezzato in `<` + `=`).

Parsing e struttura dell'AST
----------------------------
Il parser delega a funzioni `parse*` specializzate (es. `parseSelectStatement`) che costruiscono un `SQLStatement` fortemente tipizzato. Le **espressioni** (letterali, colonne, operatori unari/binari, funzioni, `CASE WHEN`) sono modellate da un `enum` indiretto, che consente alberi arbitrariamente profondi. Il risultato è un AST utilizzabile sia per l'esecuzione immediata sia per fasi intermedie (es. pianificazione e rewrite).

Recupero errori e messaggistica
-------------------------------
In caso di token inatteso o fine input, gli errori riportano il contesto atteso ed effettivo. Questa accuratezza semplifica la diagnosi di query complesse durante l'uso interattivo in CLI.

Statement supportati e semantica
--------------------------------
Il set copre DDL (`CREATE TABLE`, `CREATE INDEX`, `DROP TABLE`), DML (`INSERT`, `UPDATE`, `DELETE`) e interrogazione (`SELECT`) oltre a `EXPLAIN`. `SELECT` supporta proiezioni (con alias), `FROM` con riferimenti tabellari (e join nel modello dati), `WHERE`, `GROUP BY`, `ORDER BY`, `LIMIT` (dove implementato). La semantica si affida alle primitive del motore: filtro e proiezione vengono eseguiti a valle su snapshot MVCC coerente.

Interfaccia di esecuzione e integrazione
----------------------------------------
`SQLQueryInterface` separa parsing da esecuzione: per DDL/DML invoca le API del `Database`, per `SELECT` attiva il planner. Questo confine consente di introdurre ottimizzazioni (es. cache di viste materializzate) senza toccare il linguaggio.

Linee guida per estendere il linguaggio
---------------------------------------
- Aggiungere nuovi token nel lexer mantenendo l'ordine di precedenza.
- Ampliare `SQLExpression`/`SQLStatement` con nuovi casi e relativi parser.
- Definire una strategia di fallback per funzioni non riconosciute (es. errore esplicito con suggerimento).

