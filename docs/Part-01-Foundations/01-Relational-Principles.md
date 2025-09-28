# Capitolo 1 — Principi Relazionali e Modello Dati

## 1.1 Origini e definizioni
- Tavole, tuple, domini: definizioni da Codd.
- Funzioni totali/parziali e legami con il typing in Swift.
- Mapping teorico ↔ strutture dati: `CatalogTableSchema`, `CatalogColumnDefinition` (`Sources/ColibriCore/Catalog/LogicalObjects.swift`).

## 1.2 Gerarchia dei tipi
- `DataType` enum: motivazione per ciascun caso (`STRING`, `INT`, ...).
- Implicazioni di `size` e rappresentazioni binarie.
- Serializzazione e codec (`TypeCodec` in `Sources/ColibriCore/Types.swift`).

## 1.3 Chiavi e vincoli
### 1.3.1 Chiave primaria
- `PrimaryKeyDefinition` e enforcement nel planner (`PlannerUniqueConstraints`).
- Effetti sul B+Tree e su `FileHeapTable` (ordinamento, pageLSN).
### 1.3.2 Vincoli unici e check
- `UniqueKeyDefinition`, `CheckConstraintDefinition`.
- Validazione in `ExecutorInsert`, gestione errori `ConstraintViolation`.
### 1.3.3 Vincoli referenziali
- `ForeignKeyDefinition`, strategie `onDelete/onUpdate`.
- TODO implementativi per enforcement runtime.

## 1.4 Schema catalogato e persistenza
- `SystemCatalog.registerTable`/`registerIndex`: come viene materializzato lo schema.
- Persistenza JSON (`Snapshot`, `persistLocked`).
- Collegamento con `data/system_catalog.json`.

## 1.5 Esempio guidato
- Creare una tabella `accounts` via SQL.
- Tracciare chiamate: `SQLParser` → `Planner` → `CatalogManager.createTable`.
- Annotare lo stato del catalogo e i file creati.

## 1.6 Discussione
- Confronto con Postgres/MySQL.
- Scelte progettuali e compromessi.
- Aperture per capitoli successivi (tipi avanzati, normalizzazione).
