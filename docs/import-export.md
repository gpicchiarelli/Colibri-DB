# Import/Export (CSV, JSON, BSON)

## CSV (implementato)
- `\import <file.csv> INTO <table>` legge file UTF-8 con header obbligatorio sulla prima riga.
  - I campi vengono mappati per nome colonna; valori mancanti diventano `NULL`.
  - I tipi supportati: `INT`, `DOUBLE`, `BOOL`, `STRING`, `NULL` (riconosciuti automaticamente).
- `\export <table> TO <file.csv>` genera un CSV con header ordinato alfabeticamente, gestione dell'escaping (`","`, `""`, newline) e una riga per tupla visibile.
- Per dataset grandi conviene eseguire l'import in transazione esplicita (`\begin` / `\commit`).

## JSON/BSON (roadmap)
- Supporto streaming per JSON e BSON con mapping configurabile verso tipi SQL.
- Possibilità di import/export direttamente da/verso pipe o HTTP (CLI + future API server).

## Sicurezza
- Applicare permessi restrittivi ai file generati; integrare cifratura lato OS quando necessario.
- Loggare import/export nel catalogo per audit (roadmap).
