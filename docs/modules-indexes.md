# Indici & Strutture Dati Pluggabili

ColibrìDB separa l'API degli indici (`IndexProtocol`) dalle implementazioni concrete, permettendo di selezionare il backend adatto alla tabella o di sperimentare nuove strutture senza toccare il resto del motore.

## API comune
```swift
public protocol IndexProtocol {
    associatedtype Key: Hashable & Comparable
    associatedtype Ref
    mutating func insert(_ key: Key, _ ref: Ref) throws
    func searchEquals(_ key: Key) throws -> [Ref]
    func range(_ lo: Key?, _ hi: Key?) throws -> [Ref]
    mutating func remove(_ key: Key, _ ref: Ref) throws
}
```

## Indici in-memory (`AnyStringIndex`)
`AnyStringIndex` è un contenitore type-erased che espone la stessa API per più backend string-based. I comandi CLI (`USING <kind>`) istanziano automaticamente la variante corretta:
- **Hash** — Extendible hash table in-memory, ottima per lookup esatti (`=`).
- **ART (Adaptive Radix Tree)** — Struttura radice-adattiva con compressione di path, ideale per chiavi stringa/UUID e range lessicografici.
- **SkipList** — Skip list probabilistica con buone proprietà concorrenti e range intermedi.
- **FractalTree** — Indice buffered (message-passing) che raggruppa gli update in batch prima di fonderli nel base tree.
- **LSMTree** — Memtable + run immutabili; merge e compattazione leggera simulano un LSM ibrido.
- **BTree** — Variante in-memory per sperimentazioni rapide con chiavi composite di piccole dimensioni.

Limitazioni attuali:
- Supportano una sola colonna (`columns.count == 1`).
- Non sono persistenti: utili per workload transienti, caching o test.

## Indice persistente (`FileBPlusTreeIndex`)
- B+Tree page-based con pagine radici/interne/foglie memorizzate su disco.
- **Caratteristiche**:
  - Page size ereditato dalla configurazione (`pageSizeBytes`).
  - Chiavi composite/multi-tipo (array di `Value`) con supporto a range su tuple.
  - Bulk build bottom-up (`rebuildIndexBulk`), validazione superficiale e profonda (`validateIndex`, `validateIndexDeep`).
  - Compattazione foglie (`compactIndex`) e dump strutturato (`dump-header`, `dump-leaves`).
  - WAL dedicato (`.wal`) con checkpoint periodici per contenere tempi di recovery.
- **Integrazione CLI**: `USING BTree` crea automaticamente directory `data/indexes/` e registra l'indice nei cataloghi.

## Aggiornamento degli indici
- Ogni `INSERT/DELETE/RESTORE` passa da `Database.updateIndexes`/`removeFromIndexes` per mantenere sincrono il backend selezionato.
- Le operazioni composite per B+Tree generano chiavi miste (`Value`), rispettando l'ordine definito in `CREATE INDEX`.

## Comandi CLI rilevanti
```
\create index idx ON tab(col[,col2,...]) USING <Hash|ART|SkipList|Fractal|LSM|BTree>
\indexes <table>
\index search <table> <index> <value[,value2...]>
\index range <table> <index> <lo> <hi>
\index validate <table> <index>
\index validate-deep <table> <index>
\index rebuild <table> <index>
\index rebuild-bulk <table> <index>
\index dump-header <table> <index> [pageId]
\index dump-leaves <table> <index> [count]
\index compact <table> <index>
```

## Roadmap
- Supporto a indici geospaziali e JSON tramite nuovi backend `IndexProtocol`.
- Versionamento e hot-swap degli indici persistenti durante rebuild online.
- Integrazione con ottimizzatore cost-based per suggerire automaticamente la struttura migliore.
