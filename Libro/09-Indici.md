09 — Indici
===========

Panoramica
----------
Catalogo indici pluggabile con B+Tree persistente e strutture in-memory sperimentali (Hash, ART, SkipList, Fractal, LSM).

Componenti
----------
- `Index/BPlusTree/` e `FileBPlusTreeIndex.swift` — pagine indice, checkpoint e compattazione.
- `Index/AnyStringIndex.swift` — selettore runtime di implementazioni.

Integrazione con planner
------------------------
`QueryPlanner` valuta indici candidati e costruisce `IndexScanOperator` con bounds da predicati di uguaglianza/intervallo.

