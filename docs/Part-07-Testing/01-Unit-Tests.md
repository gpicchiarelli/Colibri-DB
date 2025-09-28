# Capitolo 24 — Testing Unitario e di Modulo

## 24.1 Struttura della suite
- Directory `Tests/ColibriCoreTests`.
- Convenzioni di naming, setup/teardown.

## 24.2 Test per il WAL
- `WALTests.swift`: casi `testWriteAndRead`, `testCheckpoint`.
- Analisi dei record generati, assert.

## 24.3 Test storage e buffer
- `BufferPoolTests`, `HeapTableTests`.
- Mocking del file system, controllo pageLSN.

## 24.4 Test catalogo
- `CatalogTests`, `StatisticsTests`.
- Verifica consistenza dei metadati.

## 24.5 Roadmap
- Copertura mancante, strumenti di coverage.
