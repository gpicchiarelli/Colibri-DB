# Capitolo 21 — CLI Utente `coldb`

## 21.1 Panoramica
- `Sources/coldb/` struttura dei comandi.
- Entry point `main.swift` e parsing opzioni.

## 21.2 Comandi principali
- `\connect`, `\list`, `\schema`, `\checkpoint`, `\vacuum`.
- Implementazione in `CLI+Commands.swift`, `CLI+SQL.swift`, `CLI+Maintenance.swift`.

## 21.3 Output e formattazione
- `CLIFormatter`, `CLIColors`.
- Formattazione tabelle, viste, statistiche.

## 21.4 Script e automazione
- Esecuzione batch, integrazione con shell.
- Roadmap: scripting, macros, completamento.
