ColibriCore — Core Engine
=========================

Moduli principali
-----------------
- `SQL/` — Lexer, parser, AST e `SQLQueryInterface`.
- `Planner/` — `QueryPlanner`, operatori Volcano e `CostModel`.
- `Transactions/` — `IsolationLevel`, `MVCCManager`, lock, 2PC.
- `Storage/` — `Page`, `HeapTable`, `FileHeapTable`.
- `Buffer/` — `LRUBufferPool`, `BufferNamespaceManager`.
- `WAL/` — `FileWAL` e recovery.
- `Index/` — B+Tree e indici alternativi.
- `Policy/`, `Optimization/`, `Util/` — policy, simulatore e utilità.

Approfondisci
------------
Consulta il libro in `Libro/` per gli internals dei moduli e i documenti in `docs/` per guide operative.

