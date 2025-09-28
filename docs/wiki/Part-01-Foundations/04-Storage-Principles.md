---
layout: page
title: Principi di Storage
description: Capitolo 4 - Principi di storage e persistenza
---

# Capitolo 4 — Fondamenti di Storage e Pagine

## 4.1 Modello di memoria secondaria
Il motore storage di Colibrì DB utilizza file organizzati in pagine di dimensione fissa (8KB). Ogni pagina è suddivisa in:
- Header: include `pageLSN`, identificatore, numero slot liberi.
- Slot directory: array di offset che puntano alle tuple.
- Area dati: spazio contiguo in cui le tuple sono memorizzate in formato compatto.

Questa organizzazione supporta inserimento e cancellazione efficienti. La struttura `Page` è definita in `Sources/ColibriCore/Storage/Page.swift`.

## 4.2 FileHeapTable
`FileHeapTable` incapsula l'accesso ai file heap. La funzione `insert(row:pageLSN:)` esegue:
1. Selezione di una pagina con spazio sufficiente via `FreeSpaceMap`.
2. Caricamento della pagina nel buffer pool (`BufferPool.pin`).
3. Scrittura della tupla e aggiornamento slot directory.
4. Aggiornamento `pageLSN` per rispettare WAL-before-data.

Il metodo `read(rid:)` restituisce una tupla `Row` decodificando il layout binario.

## 4.3 Buffer pool
Il buffer pool serve da cache di pagine in RAM. `BufferPool` mantiene un dizionario `frames` e un LRU per l'eviction. Ogni `BufferFrame` contiene:
- `pageId`
- `data`
- `dirty` flag
- `pinCount`

Le operazioni `pin`, `unpin`, `markDirty` garantiscono che le pagine siano condivise tra thread senza corruzione.

## 4.4 PageLSN e WAL
Ogni modifica incrementa `page.pageLSN` con l'LSN del record WAL corrispondente. L'invariante fondamentale è:

> `page.pageLSN ≤ wal.flushedLSN` prima di scrivere la pagina su disco.

L'assert è implementata in `FileHeapTable.flush(wal:)`. Violazioni indicano bug nel logging.

## 4.5 Gestione spazio libero
`FreeSpaceMap` mantiene un heap (priorità) di pagine ordinate per spazio libero. Quando una pagina scende sotto una soglia, viene ignorata per nuovi inserimenti. La compattazione (vacuum) ricostruisce le pagine rimuovendo tombstone.

## 4.6 Indici e integrazione
Gli indici B+Tree mantengono proprie pagine e header con `checkpointLSN`. Gli aggiornamenti alle pagine indice seguono lo stesso schema di buffer pool e WAL, consentendo recovery coerente.

## 4.7 Laboratorio
- Creare una tabella, inserire 1000 record.
- Utilizzare `coldb-dev \heap inspect accounts` per visualizzare layout pagine.
- Osservare l'effetto di cancellazioni e vacuum confrontando `FreeSpaceMap` prima/dopo.

## 4.8 Conclusione
Questi principi di storage costituiscono la base per comprendere i capitoli successivi sul WAL (Cap. 5) e sugli indici (Cap. 8).
