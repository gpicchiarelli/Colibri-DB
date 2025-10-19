---
layout: page
title: User CLI
description: Capitolo 21 - CLI per utenti
---

# Capitolo 21 — CLI Utente `coldb`

> **Obiettivo**: documentare la CLI ufficiale per gli utenti finali, descrivendone architettura, comandi, formattazione e casi d'uso accademici.

---

## 21.1 Architettura

La CLI è implementata in `Sources/coldb`. Componenti principali:
- `CLI.swift`: entry point e loop principale.
- `CLI+Commands.swift`: comandi generali (`\connect`, `\list`, ...).
- `CLI+SQL.swift`: esecuzione query, modalità script.
- `CLIFormatter`, `CLIColors`: formattazione testuale.

Diagramma:
```
User Input → Parser comandi → Executor → Wire Protocol → Server
```

---

## 21.2 Comandi fondamentali

| Comando | Descrizione | File |
|---------|-------------|------|
| `\connect host:port` | Apre una sessione con il server | `CLI+Commands.swift` |
| `\list` | Elenca database/tabelle | `CLI+Commands.swift` |
| `\schema table` | Mostra schema | `CLI+SQL.swift` |
| `\checkpoint` | Richiede checkpoint | `CLI+Maintenance.swift` |
| `\vacuum table` | Avvia vacuum | `CLI+Maintenance.swift` |

Ogni comando è associato a una funzione Swift con logging e gestione errori.

---

## 21.3 Output e formattazione

`CLIFormatter` stampa risultati in tabelle. Funzionalità:
- Larghezza colonne dinamica.
- Coloring opzionale (`CLIColors`).
- Supporto per output CSV/JSON (in roadmap).

Esempio:
```
+----+---------+---------+
| id | owner   | balance |
+----+---------+---------+
| 1  | Alice   |   120.0 |
| 2  | Bob     |   300.0 |
+----+---------+---------+
```

---

## 21.4 Modalità scripting

`coldb -f script.sql` esegue file SQL batch. Lo standard input può essere usato per pipe (`cat script.sql | coldb`).

---

## 21.5 Laboratorio

1. Lanciare `coldb` e connettersi al server.
2. Eseguire comandi `\list`, `\schema`, `SELECT ...`.
3. Esportare output in file (redirect shell).

---

## 21.6 Collegamenti
- **Capitolo 19**: protocolli wire usati dalla CLI.
- **Capitolo 23**: strumenti DevOps e integrazione con script.

