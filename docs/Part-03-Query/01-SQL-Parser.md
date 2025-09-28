# Capitolo 10 — Parsing SQL e Costruzione AST

## 10.1 Teoria del parsing
Una grammatica SQL semplificata può essere definita in forma BNF. Spieghiamo concetti quali terminali, non terminali, regole di produzione. Presentiamo l'algoritmo top-down utilizzato dal parser.

## 10.2 Lexer
`SQLLexer` effettua tokenizzazione. Analizziamo funzioni `tokenize`, gestione string literal, numeri, identificatori. Descriviamo la complessità O(n) e gli errori sollevati (`SQLLexerError`).

## 10.3 Parser
`SQLParser` implementa un parser ricorsivo discendente. Per ogni tipo di statement (`SELECT`, `INSERT`, `CREATE`, etc.) descriviamo la funzione corrispondente (`parseSelectStatement`, `parseCreateTableStatement`). Utilizziamo snippet di codice e commenti per illustrare la logica.

### 10.3.1 Gestione vincoli
`parseConstraint()` riconosce `PRIMARY KEY`, `FOREIGN KEY`, `UNIQUE`, `CHECK`. Spieghiamo come vengono convertiti in `SQLConstraint`.

### 10.3.2 Gestione espressioni
`parseExpression()` costruisce alberi binari per operatori aritmetici/logici. Introduciamo precedenze e associatività.

## 10.4 Costruzione AST
Una volta riconosciuta la sintassi, il parser restituisce `SQLStatement`. Analizziamo la struttura delle classi `SQLSelect`, `SQLInsert`, ecc. Illustreremo come l'AST sia un grafo aciclico con riferimenti a espressioni e clausole.

## 10.5 Error handling
Il parser genera `SQLParseError` con messaggi esplicativi. Discutiamo l'importanza di una buona diagnostica.

## 10.6 Laboratorio
- Provare a parsare statement validi e invalidi usando `SQLParser.parse(sql)` da REPL Swift.
- Osservare l'AST generato serializzandolo in JSON per verifica.
