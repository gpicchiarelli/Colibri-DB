11 — CLI
========

Panoramica
----------
CLI amministrativa `coldb` per gestione tabelle, indici, import/export, buffer pool e policy.

Componenti
----------
- `Sources/coldb/CLI+*.swift` — comandi per DML/DDL, transazioni, indici, metriche e SQL.

Esempi
------
```
.build/debug/coldb --config colibridb.conf.json
\\create table demo
\\insert demo id=1,name=Alice
```

