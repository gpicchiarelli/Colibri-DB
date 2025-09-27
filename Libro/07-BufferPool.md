07 — Buffer Pool
================

Responsabilità
--------------
Caching pagine con politica LRU/Clock, quota per namespace (tabelle/indici), flush asincrono e hint IO.

Componenti
----------
- `Buffer/LRUBufferPool.swift` — cache pagine, eviction, dirty tracking e flush.
- `Buffer/BufferNamespaceManager.swift` — quote per namespace e bilanciamento pressione.
- `Util/IOHints.swift` — suggerimenti su pattern di accesso (sequential vs random).

Metriche e osservabilità
------------------------
Hit/miss, pagine dirty, pinned e eviction esposte via API `Database` e CLI.

