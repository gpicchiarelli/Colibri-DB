# Capitolo 15 — SystemCatalog e Persistenza dei Metadati

> **Obiettivo**: analizzare il catalogo di sistema come base di conoscenza del database, utilizzando tabelle esplicative, diagrammi e procedure di laboratorio.

---

## 15.1 Ruolo del catalogo

Il catalogo memorizza metadati su oggetti logici (tabelle, indici, viste), oggetti fisici (file), ruoli, statistiche e configurazioni. Garantisce coerenza per operazioni DDL e supporto all'ottimizzazione.

Schema concettuale:
```
+----------------+      +----------------+
| LogicalObject  | ---> | PhysicalObject |
+----------------+      +----------------+
        |                         |
        v                         v
  Table / Index           Heap File / Index File
```

---

## 15.2 Struttura `SystemCatalog`

`SystemCatalog` mantiene uno snapshot in memoria e lo persiste in `data/system_catalog.json`. Componenti chiave:

| Tipo | Descrizione |
|------|-------------|
| `LogicalObject` | Rappresenta oggetti logici con metadati |
| `PhysicalObject` | Associa oggetti logici a file fisici |
| `RoleEntry` | Gestisce privilegi e membership |
| `StatisticEntry` | Memorizza statistiche per tabelle/colonne |
| `ConfigurationEntry` | Parametri di configurazione |

### 15.2.1 Snapshot
`Snapshot` è una struct con array per ciascuna categoria. All'inizializzazione, il catalogo tenta di caricare i dati da disco; se il file non esiste, crea uno snapshot vuoto.

---

## 15.3 Operazioni principali

### 15.3.1 Registrazione tabelle
`registerTable(name:schema:...)`:
1. Cerca se la tabella esiste.
2. Aggiorna metadati (storage, pageSize, inMemory).
3. Associa un `PhysicalObject` con percorso del file.
4. Salva lo snapshot.

### 15.3.2 Registrazione indici
`registerIndex(name:table:kind:path:columns)` aggiorna metadati e associa file indice.

### 15.3.3 Ruoli, statistiche, configurazioni
Funzioni analoghe aggiornano i rispettivi array nello snapshot.

---

## 15.4 Persistenza

Il metodo `persistLocked()` serializza lo snapshot con `JSONEncoder` (con opzioni `prettyPrinted`, `sortedKeys`) e scrive su disco in modo atomico (`Data.write(options: .atomic)`).

Diagramma I/O:
```
Snapshot (RAM) --JSONEncoder--> JSON --write--> system_catalog.json
```

---

## 15.5 Concorrenza

`SystemCatalog` utilizza una `DispatchQueue` con attributo `.concurrent`. Operazioni mutative usano flag `.barrier` per garantire esclusione, mentre le letture avvengono in parallelo.

---

## 15.6 Laboratorio

1. Eseguire `CREATE TABLE accounts ...`.
2. Ispezionare `system_catalog.json`:
   ```bash
   jq '.logical[] | select(.name=="accounts")' data/system_catalog.json
   ```
3. Eseguire `DROP TABLE accounts` e verificare che l'entry venga rimossa.

---

## 15.7 Collegamenti
- **Capitolo 16**: `CatalogManager` usa `SystemCatalog` per orchestrare operazioni DDL.
- **Appendice B**: guida alla configurazione e directory dei file.

