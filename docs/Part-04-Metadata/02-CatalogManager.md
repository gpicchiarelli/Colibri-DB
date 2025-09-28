# Capitolo 16 — CatalogManager e API DDL

## 16.1 Panoramica
- Ruolo di `CatalogManager` come facciata.
- Interazione con `SystemCatalog`, `StatisticsManager`, `CheckpointCatalog`.

## 16.2 Creazione oggetti
- `createDatabase`, `createTable`, `createIndex`.
- Validazioni (`ensureTableDoesNotExist`, `validateColumnDefinitions`).

## 16.3 Modifica e drop
- `alterTable`, `dropTable`, `dropIndex`.
- Aggiornamento metadati e storage.

## 16.4 Cache e invalidazioni
- Cache in-memory, invalidazione su DDL.
- TODO per invalidazioni distribuite.

## 16.5 Esempi
- Sequenza `CREATE TABLE` → `INSERT` → `DROP` con tracciamento catalogo.
