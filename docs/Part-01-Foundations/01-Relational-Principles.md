# Capitolo 1 — Principi Relazionali e Modello Dati

## 1.1 Origini e definizioni
### 1.1.1 Relazione
Una **relazione** R su domini D₁,…,Dₙ è un sottoinsieme finito del prodotto cartesiano D₁ × … × Dₙ. In ColibrìDB ogni tupla è rappresentata dal tipo `Row`, ovvero un dizionario ordinato di valori tipizzati. La definizione è coerente con il file `Sources/ColibriCore/Types.swift`, dove `Value` incapsula i possibili domini.

### 1.1.2 Attributi e domini
Gli attributi sono modellati da `CatalogColumnDefinition`. La funzione di inizializzazione è la seguente:

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

Analizzare il costruttore dimostra come i domini (tipi) siano fissati a compile-time, mentre proprietà come `nullable` e `defaultValue` determinano vincoli a runtime.

### 1.1.3 Tupla
Una tupla è un elemento della relazione, implementata da `Row`. La struttura consente accesso per nome e codifica JSON per persistenza.

## 1.2 Gerarchia dei tipi
### 1.2.1 Enumerazione `DataType`
La definizione `enum DataType` specifica i domini supportati. Ogni caso ha associata una dimensione (`size`) che sarà utilizzata dal layer storage per allocare spazio.

### 1.2.2 Serializzazione
Il mapping `DataType` → binario avviene tramite `TypeCodec`. La funzione `encode(value:into:)` dimostra come i valori vengano trasformati in layout contiguo nelle pagine.

### 1.2.3 Impatto sulle query
La scelta del tipo influenza il planner: `LogicalPlanner` verifica compatibilità nelle espressioni. Descriveremo esempi in §1.5.

## 1.3 Chiavi e vincoli
### 1.3.1 Chiave primaria
`PrimaryKeyDefinition` definisce il set di colonne che rende la relazione funzione. In `CatalogManager.createTable` si verifica l'assenza di duplicati. Nel tempo di inserimento `ExecutorInsert` chiama `IndexManager` per creare eventuali indici clustered.

### 1.3.2 Vincoli unici
`UniqueKeyDefinition` interviene in fase di DDL. La funzione `ensureUniqueConstraint` (Planner) crea check logici e piani di enforcement.

### 1.3.3 Vincoli referenziali
`ForeignKeyDefinition` contiene le azioni `onDelete`/`onUpdate`. L'implementazione runtime è parziale; il manuale discute la progettazione futura.

### 1.3.4 Check constraint
`CheckConstraintDefinition` memorizza un'espressione da valutare; la valutazione è delegata a `ExpressionEvaluator` durante gli insert/update.

## 1.4 Persistenza del catalogo
### 1.4.1 `SystemCatalog.registerTable`
Analizziamo il flusso di registrazione di una tabella:
1. Si costruisce un oggetto `LogicalObject` con metadati.
2. Se esiste già, viene aggiornato e persistito.
3. Viene associato un `PhysicalObject` con il percorso del file heap.

### 1.4.2 Snapshot e JSON
`SystemCatalog` mantiene uno snapshot in memoria aggiornato sotto lock. La funzione `persistLocked()` esegue:
- `JSONEncoder` su `Snapshot`.
- Scrittura atomica su disco.

### 1.4.3 File system
Il catalogo è salvato in `data/system_catalog.json`. I laboratori mostreranno come leggere e interpretare questo file.

## 1.5 Laboratorio: creazione di una tabella
1. Eseguire `colibridb> CREATE TABLE accounts(id INT PRIMARY KEY, balance DOUBLE);`
2. Osservare il log del catalogo: `cat data/system_catalog.json`.
3. Commentare come `CatalogManager.createTable` orchestrai seguenti passaggi:
   - Validazione schema.
   - Allocazione file heap (`FileHeapTable`).
   - Registrazione nel catalogo.

## 1.6 Discussione
Confrontiamo ColibrìDB con PostgreSQL e MySQL riguardo:
- Gestione metadati (JSON vs catalogo relazionale).
- Strategie di enforcement vincoli.
- Estendibilità dei tipi.

Chiudiamo indicando come il Capitolo 2 si agganci a questi concetti introducendo l'algebra relazionale e la pipeline di query.
