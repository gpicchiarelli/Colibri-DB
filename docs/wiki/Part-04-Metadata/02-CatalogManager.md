---
layout: page
title: Catalog Manager
description: Capitolo 19 - Gestore del catalogo
---

# Capitolo 16 — CatalogManager e API DDL

> **Obiettivo**: analizzare l'interfaccia ad alto livello che gestisce le operazioni di Data Definition Language (DDL), illustrando il flusso completo di creazione, modifica e cancellazione degli oggetti.

---

## 16.1 Funzione di `CatalogManager`

`CatalogManager` offre API per creare e modificare database, tabelle, indici, ruoli. Opera come **façade** sopra `SystemCatalog`, `Database`, `StatisticsManager`.

Diagramma componenti:
```
CatalogManager
 ├─ SystemCatalog
 ├─ Database
 └─ StatisticsManager
```

---

## 16.2 Creazione di oggetti

### 16.2.1 `createDatabase`
- Crea directory su disco.
- Inizializza catalogo, checkpoint, WAL.
- Registra il database in `SystemCatalog`.

### 16.2.2 `createTable`
Sequence diagram (ASCII):
```
Client → CatalogManager → validateSchema
          ↓
        Database.createTable
          ↓
        SystemCatalog.registerTable
          ↓
        StatisticsManager.initTableStats
```

Passi principali:
1. Validazione schema (unicità nomi colonne, compliance tipi).
2. Creazione file heap (`FileHeapTable`) e registrazione fisica.
3. Aggiornamento catalogo e statistiche.

### 16.2.3 `createIndex`
- Verifica esistenza tabella.
- Costruisce B+Tree (`FileBPlusTreeIndex`).
- Aggiorna catalogo e statistiche.

---

## 16.3 Modifiche e drop

| Operazione | Funzione | Effetti |
|------------|----------|---------|
| Alter table | `alterTable` | Aggiorna schema, invalidazione cache |
| Drop table | `dropTable` | Rimuove entry dal catalogo, elimina file |
| Drop index | `dropIndex` | Rimuove index dal catalogo e file indice |

### 16.3.1 `dropTable`
Pseudocodice:
```swift
func dropTable(name) {
    database.removeTableFiles(name)
    systemCatalog.removeLogical(name, .table)
    statisticsManager.deleteTableStats(name)
}
```

---

## 16.4 Cache e invalidazioni

`CatalogManager` mantiene cache in-memory (es. schema tabelle). Ogni operazione DDL invalida le entry coinvolte per garantire consistenza.

---

## 16.5 Laboratorio

1. Creare una tabella via CLI.
2. Usare `coldb-dev \catalog list` (da implementare) per visualizzare stato.
3. Eseguire `DROP TABLE` e verificare che file e metadati siano rimossi.

---

## 16.6 Collegamenti
- **Capitolo 15**: dettagli su `SystemCatalog`.
- **Parte V**: comandi server e CLI DDL passano tramite `CatalogManager`.

