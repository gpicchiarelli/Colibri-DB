# Capitolo 21 — CLI Utente `coldb`

## 21.1 Struttura
Il progetto `Sources/coldb` implementa la CLI. `main.swift` inizializza la CLI, carica configurazioni e gestisce l'interprete di comandi.

## 21.2 Comandi
- `\connect`: stabilisce connessione al server.
- `\list`: elenca database/tabelle.
- `\schema`: mostra definizione di tabella.
- `\checkpoint`, `\vacuum`: invocano operazioni di manutenzione.

Analizziamo le implementazioni in `CLI+Commands.swift`, `CLI+SQL.swift`.

## 21.3 Formattazione output
`CLIFormatter` genera tabelle testuali. Esponiamo funzioni per impostare larghezza colonne, colori (`CLIColors`).

## 21.4 Script
La CLI supporta script batch e pipe. Descriviamo l'uso di `coldb -f file.sql`.

## 21.5 Laboratorio
- Connettersi al server, eseguire query e salvare output.
- Personalizzare la formattazione.
