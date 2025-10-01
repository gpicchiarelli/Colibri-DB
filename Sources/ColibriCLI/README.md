coldb — CLI
===========

Comandi principali
------------------
- DDL/DML: creare tabelle/indici, insert/update/delete, select.
- Transazioni: begin/commit/rollback.
- Manutenzione: compattazione, vacuum, metriche.
- SQL: esecuzione di query testuali via `SQLQueryInterface`.

Esempio
-------
```
.build/debug/coldb --config colibridb.conf.json
\\create table demo
\\insert demo id=1,name=Alice
```

Approfondisci: `Libro/11-CLI.md` e `docs/cli.md`.

