# Capitolo 16 — CatalogManager e API DDL

## 16.1 Funzione di `CatalogManager`
`CatalogManager` fornisce un'interfaccia ad alto livello per le operazioni DDL. Coordina `SystemCatalog`, `Database`, `StatisticsManager` e `CheckpointCatalog`.

## 16.2 Creazione di oggetti
- `createDatabase`: genera directory fisiche, registra metadata, inizializza catalogo.
- `createTable`: valida schema, crea `FileHeapTable`, registra logical/physical object, aggiorna statistiche.
- `createIndex`: crea file B+Tree, registra index, aggiorna catalogo.

Analizziamo la sequenza di chiamate e gli invarianti (es. unicità nomi, esistenza tabelle).

## 16.3 Modifica e drop
`alterTable`, `dropTable`, `dropIndex` eseguono le operazioni inverse. Discutiamo la gestione di lock e la necessità di transazioni.

## 16.4 Cache
`CatalogManager` mantiene cache in-memory per ridurre accessi a `SystemCatalog`. Spieghiamo invalidazioni e thread-safety.

## 16.5 Laboratorio
- Eseguire `CREATE`/`DROP` e osservare gli effetti su `system_catalog.json` e file fisici.
