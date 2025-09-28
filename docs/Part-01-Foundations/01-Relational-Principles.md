---
layout: page
title: Principi Relazionali
description: Capitolo 1 - Principi del modello relazionale
---

# Capitolo 1 — Principi Relazionali e Modello Dati

> **Obiettivo del capitolo**: collegare le definizioni formali del modello relazionale con l'implementazione concreta in Colibrì DB, utilizzando schemi, tabelle riassuntive, pseudocodice e riferimenti puntuali al codice sorgente.

---

## 1.1 Definizioni fondamentali

| Concetto | Definizione formale | Traduzione in Colibrì DB |
|----------|---------------------|-------------------------|
| Relazione `R` | Sottoinsieme finito di \( D_1 \times \dots \times D_n \) | Collezione di `Row` memorizzate in `FileHeapTable` |
| Tupla `t` | Funzione \( t: \{A_1,\dots,A_n\} \to D \) | Istanza di `Row` (dizionario ordinato `String -> Value`) |
| Attributo `A_i` | Coppia (nome, dominio) | `CatalogColumnDefinition` |
| Schema `S` | Insieme ordinato di attributi | `CatalogTableSchema` |

### 1.1.1 Relazione e tupla
Una **relazione** è modellata da un insieme di tuple. In Colibrì DB le tuple sono oggetti `Row` serializzati secondo i codec definiti in `Types.swift`. L'accesso per nome garantisce consistenza con la definizione matematica di funzione.

### 1.1.2 Attributi e domini
Gli attributi sono rappresentati da `CatalogColumnDefinition`, come mostrato nel seguente estratto:

```120:137:Sources/ColibriCore/Catalog/LogicalObjects.swift
public struct CatalogColumnDefinition {
    public let name: String
    public let type: DataType
    public let nullable: Bool
    public let defaultValue: Value?
    public let autoIncrement: Bool
    public let comment: String?
    // ...
}
```

- `name`: etichetta dell'attributo (\( A_i \)).
- `type`: dominio (\( D_i \)), pilotato dall'enumerazione `DataType`.
- `nullable`: rappresenta la possibilità di \(\text{NULL}\).

### 1.1.3 Schema e istanziazione
`CatalogTableSchema` agisce come firma della relazione. L'invariante principale è che le colonne siano univoche e coerenti con i vincoli dichiarati (primarie, uniche, ecc.).

---

## 1.2 Gerarchia dei tipi e serializzazione

### 1.2.1 Enumerazione `DataType`
L'enum `DataType` definisce i domini supportati. Ogni caso riflette un tipo SQL:

| Tipo SQL | Caso `DataType` | Byte allocati | Note |
|----------|-----------------|---------------|------|
| `INT` | `.int` | 4 | Complemento a due |
| `DOUBLE` | `.double` | 8 | IEEE 754 |
| `VARCHAR(n)` | `.string` | variabile | Lunghezza prefissata |
| `BLOB` | `.blob` | variabile | Byte raw |

### 1.2.2 Codec e layout
La serializzazione è affidata a `TypeCodec`. Il seguente pseudocodice illustra la codifica di una riga:

```swift
for column in schema.columns {
    let value = row[column.name]
    TypeCodec.encode(value, into: pageBuffer)
}
```

Il layout binario rispetta l'ordine delle colonne, con eventuali metadati (lunghezze, flag null).

### 1.2.3 Impatto su storage e query
- **Storage**: la dimensione guida la scelta della pagina in `FreeSpaceMap`.
- **Planner**: i tipi sono verificati durante la fase semantica (`TypeChecker`). In caso di mismatch viene sollevato `PlannerError.typeMismatch`.

---

## 1.3 Vincoli e chiavi

### 1.3.1 Chiave primaria (`PRIMARY KEY`)
Definizione formale: un insieme minimo di attributi \( K \) tale che \( \forall t_1,t_2 \in R, t_1[K] = t_2[K] \Rightarrow t_1 = t_2 \).

Implementazione:
- `PrimaryKeyDefinition` memorizza nome e colonne.
- Durante `CatalogManager.createTable` viene verificata l'assenza di duplicati e, se necessario, creato un indice clustered.
- Il planner genera vincoli logici per prevenire insert duplicati.

### 1.3.2 Vincoli unici e check
`UniqueKeyDefinition` e `CheckConstraintDefinition` sono convertiti in operatori di verifica nel planner. Le espressioni `CHECK` sono valutate da `ExpressionEvaluator` durante l'esecuzione di `INSERT/UPDATE`.

### 1.3.3 Vincoli referenziali
`ForeignKeyDefinition` modella la relazione \( R_1 \to R_2 \) con azioni `onDelete` e `onUpdate`. L'enforcement runtime è parziale (roadmap), ma il catalogo registra i metadati necessari (tabelle e colonne coinvolte).

| Azione | Semantica | Stato |
|--------|-----------|-------|
| `RESTRICT` | blocca l'operazione se esistono riferimenti | Supportata |
| `CASCADE` | propaga la modifica | In roadmap |
| `SET NULL/DEFAULT` | aggiorna il valore | In roadmap |

---

## 1.4 Persistenza del catalogo

### 1.4.1 Snapshot e JSON
`SystemCatalog` mantiene uno `Snapshot` in memoria; ogni mutazione aggiorna lo snapshot e richiama `persistLocked()` per scrittura atomica su `data/system_catalog.json`.

### 1.4.2 Flusso `registerTable`
1. Creazione o aggiornamento di `LogicalObject`.
2. Eventuale creazione di `PhysicalObject` (file heap).
3. Persistenza su disco.

Schema sequenziale (ASCII):
```
+-----------+        +-----------------+        +----------------+
| SQL DDL   | -----> | CatalogManager  | -----> | SystemCatalog  |
+-----------+        +-----------------+        +----------------+
        |                                        |
        v                                        v
    File Heap                               system_catalog.json
```

---

## 1.5 Laboratorio guidato

1. **Creazione tabella**
   ```sql
   CREATE TABLE accounts (
       id INT PRIMARY KEY,
       owner STRING NOT NULL,
       balance DOUBLE DEFAULT 0.0
   );
   ```
2. **Verifica catalogo**
   ```bash
   cat data/system_catalog.json | jq '.logical[] | select(.name=="accounts")'
   ```
3. **Analisi**: confrontare i metadati con la definizione SQL e verificare la presenza del file heap corrispondente.

---

## 1.6 Confronto e discussione

| Sistema | Rappresentazione catalogo | Enforcement vincoli |
|---------|---------------------------|---------------------|
| Colibrì DB | JSON con snapshot atomici | Planner + executor |
| PostgreSQL | Tabelle relazionali (`pg_class`, etc.) | Catalogo + executor |
| MySQL | Metadati InnoDB + file `.frm` | Storage engine |

### 1.6.1 Vantaggi
- Semplicità di introspezione (JSON leggibile).
- Aggiornamenti atomici del catalogo.

### 1.6.2 Limiti e roadmap
- Mancanza di enforcement completo per `FOREIGN KEY`.
- Necessità di versioning del catalogo per replicazione.

---

## 1.7 Collegamenti
Questo capitolo prepara il terreno per:
- **Capitolo 2**: trasformazione dello schema in operatori logici.
- **Capitolo 5**: relazione tra metadati e WAL nei checkpoint.

