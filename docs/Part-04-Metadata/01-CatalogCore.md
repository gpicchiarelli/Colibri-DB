# Capitolo 15 — SystemCatalog e Persistenza Metadati

## 15.1 Ruolo del catalogo
Il catalogo di sistema funge da dizionario permanente. Ogni oggetto logico/fisico viene registrato con metadati (nome, schema, percorso file, statistiche). Discutiamo la necessità di un catalogo coerente per operazioni DDL e ottimizzazione.

## 15.2 Struttura `SystemCatalog`
`SystemCatalog` mantiene un `Snapshot` in memoria con array di `LogicalObject`, `PhysicalObject`, `RoleEntry`, `StatisticEntry`, `ConfigurationEntry`, `StructurePreference`. Analizziamo il costruttore e la logica di caricamento da disco.

### 15.2.1 Concorrenza
Le operazioni sono protette da `DispatchQueue` con flag `.barrier` per garantire thread-safety. Ogni mutazione crea un nuovo snapshot coerente.

### 15.2.2 Persistenza
`persistLocked()` codifica lo snapshot in JSON e lo scrive su file con operazione atomica. Questo garantisce durabilità e resistenza a crash.

## 15.3 API principali
Analizziamo `registerTable`, `registerIndex`, `registerRole`, `registerStatistic`, `registerConfiguration`, `registerStructurePreference`. Per ciascuna descriviamo input, effetti sullo snapshot e sui file fisici.

## 15.4 Rimozione e manutenzione
`removeIndex`, `removeLogical` rimuovono voci e ripuliscono metadata associati.

## 15.5 Laboratorio
- Creare tabella e osservare `system_catalog.json`.
- Aggiornare statistiche e leggere il file per verificare i cambiamenti.
