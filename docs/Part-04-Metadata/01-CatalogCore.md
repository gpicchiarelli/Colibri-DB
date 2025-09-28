# Capitolo 15 — SystemCatalog e Persistenza Metadati

## 15.1 Struttura del catalogo
- Classi `SystemCatalog`, `Snapshot`.
- Oggetti logici vs fisici, ruoli, statistiche, configurazioni.

## 15.2 Persistenza
- Serializzazione JSON (`persistLocked`).
- File `data/system_catalog.json`.

## 15.3 Operazioni principali
- `registerTable`, `registerIndex`, `removeIndex`.
- Gestione ruoli (`registerRole`, `addRoleMembership`).
- Configurazioni (`registerConfiguration`).

## 15.4 Concorrenza
- Uso di `DispatchQueue` e barrier.
- Invarianti di consistenza.

## 15.5 Esempi
- Creare tabella → verifica nel catalogo.
- Aggiornare statistiche → riflesso nel planner.
