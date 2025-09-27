# Appendici

## Layout pagina heap (schematico)
```
+------------------------------------------------------------+
| PageHeader (pageId, pageLSN, freeSpaceOffset, ... )        |
+------------------------------------------------------------+
|                    Area dati (record variabili)            |
|  ...                                                       |
+------------------------------------------------------------+
| Slot Directory (offset, length per record) ← cresce a sx   |
+------------------------------------------------------------+
```

## Sequenza tipica INSERT → WAL → Flush → Checkpoint
```
client -> CLI (\insert) -> Database.insert
        -> wal.append(insertPre)
        -> HeapTable.insert (buffer pool)
        -> wal.append(insertDone)
        -> updateIndexes / MVCC.registerInsert
        -> optional flush (manuale o per soglia dirty)
        -> checkpoint (flusha tutte le pagine + truncate WAL)
```

## Stato minimo per recovery
- WAL DB + WAL indici
- Cataloghi (`data/system_catalog.json`, `indexes/*.json`)
- Heap/Index files con `pageLSN`
- Free Space Map (`.fsm`) ricostruibile

## Checklist manutenzione manuale
- `\stats` → valutare hit/miss buffer
- `\vacuum stats` → verificare compattazione automatica
- `\policy list` → controllare finestre di manutenzione
- `\index validate-deep` → audit periodico degli indici critici

## Linee guida contributori
- Scrivere doc comments per logica non ovvia e mantenere `docs/` allineata.
- Aggiungere test SwiftPM per nuove strutture (unit + integrazione su `Tests/`).
- Misurare con Instruments/`swift test --filter` quando si introducono cambiamenti prestazionali.

## Benchmark (roadmap)
- Micro-benchmark per insert/delete/scan heap.
- Range scan comparativi tra Hash/ART/B+Tree.
- Stress test WAL: replay massivo con fault injection.

Integrare nuovi materiali in questa appendice per fornire riferimenti rapidi durante sviluppo e manutenzione.
