04 — Planner & Executor
=======================

Panoramica
----------
Il planner costruisce piani Volcano a partire da richieste logiche (`QueryRequest`). Gli operatori espongono un'interfaccia a iteratore; il cost model seleziona tra access path e strategie di join.

File principali
---------------
- `Sources/ColibriCore/Planner/QueryPlanner.swift`
- `Sources/ColibriCore/Planner/PlanOperator.swift`
- `Sources/ColibriCore/Planner/Operators.swift`
- `Sources/ColibriCore/Database/Database+Planner.swift`

Access path e join
------------------
- Access path: `TableScanOperator` vs `IndexScanOperator` su indici candidati; scelta via `CostModel`.
- Join: `HashJoinOperator` e `MergeJoinOperator`; selezione basata su somma di costi CPU+IO.

Parallelismo e limiti
---------------------
- `ParallelMapOperator` permette parallelismo per operatori mappabili.
- `LimitOperator` applica limite a valle.

Esecuzione
----------
`Database.executeQuery(_:)` orchestra pianificazione, materializzazione e caching opzionale del risultato (materialized view cache per chiave).

Il modello Volcano in pratica
----------------------------
Ogni operatore implementa `open/next/close`. `next()` produce al più una riga alla volta, delegando ai figli. Questo approccio:
- minimizza la memoria (streaming),
- favorisce il pushdown di filtro e proiezione,
- abilita interruzioni precoci (`LIMIT`).

Schema e righe di esecuzione
----------------------------
Lo `schema` definisce l'ordine e la qualifica delle colonne. Le righe (`PlanRow`) sono dizionari con chiavi qualificate (`alias.colonna`) per evitare collisioni nei join. Le proiezioni ricompongono righe più compatte per gli step a valle.

Stima di cardinalità e modello di costo
---------------------------------------
Il `CostModel` usa uno stimatore di cardinalità che si appoggia a statistiche note (es. `rowCount`, taglie medie) e a **euristiche** quando dati non sono disponibili. Ogni operatore accumula costi CPU/IO e requisiti memoria; per join la scelta fra `HashJoin` e `MergeJoin` si basa sulla somma stimata di CPU+IO e sulla struttura dei dati (necessità di ordinamento).

Ottimizzazioni comuni
---------------------
- Predicate pushdown: evitare lavoro inutile prima possibile.
- Projection pushdown: ridurre la larghezza delle righe.
- Parallel map: sfruttare CPU multiple per trasformazioni indipendenti.
- Limit early-out: interrompere catene lunghe quando il consumatore è saturo.

Materializzazione e caching
---------------------------
In certi scenari, materializzare il risultato intermedio riduce costi futuri (cache per chiave). La scelta è guidata da configurazione e pattern di accesso.

Limiti e roadmap
----------------
La versione attuale privilegia leggibilità del codice e predicibilità, lasciando spazio a ottimizzazioni successive (riordinamento join, statistiche avanzate, costi dipendenti da layout fisico e caching di piani).

