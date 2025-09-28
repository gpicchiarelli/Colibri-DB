# Capitolo 24 — Testing Unitario e di Modulo

## 24.1 Struttura della suite
- `Tests/ColibriCoreTests`: contiene test per moduli core.
- Convenzioni: naming `testXxx`, uso di `XCTestCase`.

## 24.2 WAL Tests
`WALTests.swift` verifica append, iterazione, checkpoint. Analizziamo i test `testAppendAndRead`, `testCheckpoint` e come assicurano gli invarianti.

## 24.3 Storage & Buffer Tests
`BufferPoolTests`, `HeapTableTests`: controllano LSN, flush, eviction. Documentiamo i metodi di setup e teardown.

## 24.4 Catalog Tests
`CatalogTests`, `StatisticsTests`: verificano coerenza del catalogo, aggiornamento statistiche.

## 24.5 Coverage e roadmap
Uso di strumenti di coverage, individuazione di aree scoperte, priorità future.
